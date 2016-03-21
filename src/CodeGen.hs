{-# LANGUAGE ScopedTypeVariables #-}

module CodeGen where

import Prelude
import Data.List
import qualified Data.Map as HashMap
import qualified LLIR
import LLIR

data CGContext = CGContext {
  -- label, constant string
  constStrs :: [(String, String)],
  nextConstStrId :: Int
};

getConstStrId :: CGContext -> String -> (CGContext, String)
getConstStrId cx str =
  (CGContext {
      constStrs = (constStrs cx) ++ [(id, str)],
      nextConstStrId = (nextConstStrId cx) + 1
   }, id)
  where id = ".const_str" ++ (show (nextConstStrId cx))

data FxContext = FxContext {
  variables :: HashMap.Map String String,
  offset :: Int
}

newContext :: FxContext
newContext = FxContext HashMap.empty 8

updateOffset :: FxContext -> FxContext
updateOffset (FxContext table offset) = FxContext table $ offset + 8

lookupVariable :: FxContext -> String -> String
lookupVariable (FxContext table _) var = case HashMap.lookup var table of
                                           Just a -> a
                                           Nothing -> "BAD"

setVariableLoc :: FxContext -> String -> String -> FxContext
setVariableLoc (FxContext table offset) var loc = FxContext (HashMap.adjust update var table) offset
  where update _ = loc

getHeader :: String
getHeader =
  ".section __TEXT,__text\n" ++
  ".globl _main\n"

getMainHeader :: String
getMainHeader =
  "\n" ++
  "_main:\n"

getMainFooter :: String
getMainFooter =
  -- exit(0)
  "\n" ++
  "  movl $0x2000001, %eax           # exit 0\n" ++
  "  syscall"

-- args: [(Name, size)]
getPreCall :: [(String, Int)] -> String
getPreCall args =
  let argRegs = ["%edi", "%esi", "%edx", "%ecx", "%r8d", "%r9d", "%eax", "%r10d", "%r11d", "%ebx", "%r14d", "%r15d", "%r12d", "%13d"]
      remainingArgs = drop (length argRegs) args
      argsInRegisters = (foldl (\acc (arg, reg) -> acc ++ "  movq " ++  (fst arg) ++ ", " ++ reg ++ "\n") "" (zip args argRegs))
      pushedArgs = (foldl (\acc arg -> acc ++ "  push " ++ (fst arg) ++ "\n") "" (reverse remainingArgs)) in
  "  #precall\n" ++
  "  pusha                           # save registers\n" ++
  "  movq %rsp, %rbp                 # new stack frame\n" ++
  argsInRegisters ++
  pushedArgs ++
  "  #/precall\n"

getPostCall :: String
getPostCall =
  "  #postcall\n" ++
  "  popa\n" ++
  "  #/postcall\n"

getProlog :: Int -> String
getProlog localsSize =
  "  #prolog\n" ++
  "  pusha\n" ++
  "  enter $" ++ (show localsSize) ++ " $0\n" ++
  "  #prolog\n"

getEpilog :: String
getEpilog =
  " \n" ++
  "  #epilog\n" ++
  "  leave\n" ++
  "  popa\n" ++
  "  #epilog\n"

genGlobals :: HashMap.Map String (VType, Maybe Int) -> String
genGlobals globals =
    ".bss\n" ++ (intercalate "" $ map genGlobal $ HashMap.toList globals) ++ "\n"

genGlobal :: (String, (VType, Maybe Int)) -> String
genGlobal (name, (_, Nothing)) =
    ".global_" ++ name ++ ":\n  .zero 8\n" -- Need to adjust for arrays
genGlobal (name, (_, Just size)) =
    ".global_" ++ name ++ ":\n  .zero " ++ show (8 * size) ++ "\n"

genCallouts :: HashMap.Map String String -> String
genCallouts callouts =
    "" -- Not sure how to declare global strings

genFunction :: CGContext -> LLIR.VFunction -> (CGContext, String)
genFunction cx f =
  let prolog = getProlog (8 * (length $ (LLIR.functionInstructions f))) in
  let (ncx, locals, blocksStr) = foldl
                   (\(cx, table, s) name ->
                     let block = HashMap.lookup name $ LLIR.blocks f
                         (ncx, hm, str) = genBlock cx block f table in
                     (ncx, hm, s ++ str))
                   (cx, HashMap.empty :: HashMap.Map String String, "") $ LLIR.blockOrder f in
   let strRes = "_" ++ LLIR.functionName f ++ ":\n" ++ prolog ++ blocksStr ++ getEpilog in
   (cx, strRes)

genBlock :: CGContext -> Maybe LLIR.VBlock -> LLIR.VFunction -> HashMap.Map String String -> (CGContext, HashMap.Map String String, String)
genBlock cx Nothing _ table = (cx, table, "BAD\n")
genBlock cx (Just block) f table = 
  foldl (\(cx, t, acc) name ->
          let instruction = HashMap.lookup name $ LLIR.functionInstructions f
              (ncx, table, str) = genInstruction cx instruction t in
                (ncx, table, acc ++ str))
        (cx, table, "")
        (LLIR.blockInstructions block)

valLoc :: LLIR.ValueRef -> HashMap.Map String String -> String
valLoc (ConstInt int) _ = "$" ++ show int
valLoc (ArgRef _ name) table = 
  case HashMap.lookup name table of
    Just s -> s
    Nothing -> "ERROR"
valLoc (InstRef name) table =
  case HashMap.lookup name table of
    Just s -> s
    Nothing -> "ERROR"
valLoc (ConstString name) table =
  case HashMap.lookup name table of
    Just s -> s
    Nothing -> "ERROR"
valLoc (CalloutRef name) table =
  case HashMap.lookup name table of
    Just s -> s
    Nothing -> "ERROR"
valLoc (GlobalRef name) table =
  case HashMap.lookup name table of
    Just s -> s
    Nothing -> "ERROR"
valLoc (FunctionRef name) table =
  case HashMap.lookup name table of
    Just s -> s
    Nothing -> "ERROR"

genArg :: CGContext -> HashMap.Map String String -> ValueRef -> (String, Int)
genArg cx table (InstRef ref) = 
  ("TODO", 0)

genInstruction :: CGContext -> Maybe LLIR.VInstruction -> HashMap.Map String String -> (CGContext, HashMap.Map String String, String)
genInstruction cx Nothing table = (cx, table, "BAD\n")

genInstruction cx (Just (VAllocation _ typ size)) table =
  case size of
    Just i -> (cx, table, "")
    Nothing -> (cx, table, "")

genInstruction cx (Just (VUnOp _ op val)) table =
  let loc = valLoc val table
      final = case val of
        ConstInt _ -> ""
        _ -> "  movq %rax " ++ loc ++ "\n" in
    (cx, table, 
    "  movq " ++ loc ++ "%rax\n" ++
    "  " ++ op ++ " %rax %rax\n" ++ -- what do I do with this value? I should be creating a new temporary variable and adding a new entry in the table for it
    final)

genInstruction cx (Just (VBinOp _ op val1 val2)) table =
    let loc1 = valLoc val1 table
        loc2 = valLoc val2 table in
          (cx, table, 
          "  movq" ++ loc1 ++ "%rax\n" ++
          "  " ++ op ++ loc2 ++ "% rax\n" ++ -- what do I do with this value? I should be creating a new temporary variable and adding a new entry in the table for it
          "TODO")

genInstruction cx (Just (VMethodCall name isName fname args)) table =
  -- push arguments
  let (ncx, ntable, nargs) = foldl (\(cx, table, acc) arg ->
                                      let (ncx, narg) = genArg cx table arg in
                                        (ncx, table, acc ++ narg))
                                   (cx, table, []) args in
  let precall = getPreCall nargs
      postcall = getPostCall
      destination = (show 8 * -1 {- should be offset Tony! -}) ++ "(%bpx)" in
  (ncx, HashMap.insert name destination ntable, precall ++ "  call " ++ fname ++ "\n  movq %eax " ++ destination ++ "\n")

genInstruction cx (Just (VStore _ _ _)) table =
  (cx, table, "TODO")


genInstruction cx (Just (VLookup _ _)) table =
  (cx, table, "TODO")


genInstruction cx (Just (VArrayStore _ _ _ _)) table =
  (cx, table, "TODO")


genInstruction cx (Just (VArrayLookup _ _ _)) table =
  (cx, table, "TODO")


genInstruction cx (Just (VArrayLen _ _)) table =
  (cx, table, "TODO")


genInstruction cx (Just (VReturn _ _)) table =
  (cx, table, "TODO")


genInstruction cx (Just (VCondBranch _ _ _ _)) table =
  (cx, table, "TODO")


genInstruction cx (Just (VUnreachable _)) table =
  (cx, table, "TODO")


genInstruction cx (Just (VUncondBranch _ _)) table =
  (cx, table, "TODO")


genArg :: CGContext -> HashMap.Map String String -> ValueRef -> (String, Int)
genArg cx table (InstRef ref) =
  {-- TODO: look up global vars in the CGContext! --}
  let r = HashMap.lookup ref table in
  case r of
    Just addr -> (addr, 8)
    Nothing -> ("BAD", 8)

genArg cx table (ConstInt i) =
  ("$" ++ (show i), 8)

genArg cx table (ConstString s) =
  let (ncx, id) = getConstStrId cx s
  ("$" ++ id, 8)

gen :: LLIR.PModule -> String
gen mod =
  let globals = LLIR.globals mod
      callouts = LLIR.callouts mod
      fxs = HashMap.elems $ LLIR.functions mod
      cx = CGContext {constStrs = [], nextConstStrId = 0} in
  let (cx2, fns) =
        foldl (\(cx, asm) fn ->
                let (ncx, str) = genFunction cx fn in
                (ncx, asm ++ str)) (cx, "") fxs
  in
    getHeader ++ (genGlobals globals) ++ (genCallouts callouts) ++ fns
