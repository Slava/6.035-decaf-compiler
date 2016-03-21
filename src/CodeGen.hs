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

newCGContext :: CGContext
newCGContext = CGContext [] 0

getConstStrId :: FxContext -> String -> (FxContext, String)
getConstStrId (FxContext (CGContext strs next) table offset) str =
  (FxContext newGlobal table offset, id)
  where id = ".const_str" ++ (show next)
        newGlobal = CGContext{
          constStrs = strs ++ [(id, str)],
          nextConstStrId = next + 1
        }

data FxContext = FxContext {
  global :: CGContext,
  variables :: HashMap.Map String String,
  offset :: Int
}

newFxContext :: CGContext -> FxContext
newFxContext global = FxContext global HashMap.empty 8

updateOffset :: FxContext -> FxContext
updateOffset (FxContext global table offset) = FxContext global table $ offset + 8

lookupVariable :: FxContext -> String -> String
lookupVariable (FxContext _ table _) var = case HashMap.lookup var table of
                                           Just a -> a
                                           Nothing -> "BAD"

setVariableLoc :: FxContext -> String -> String -> FxContext
setVariableLoc (FxContext global table offset) var loc = FxContext global (HashMap.adjust update var table) offset
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
  let prolog = getProlog (8 * (length $ (LLIR.functionInstructions f)))
      (ncx, blocksStr) = foldl
                   (\(cx, s) name ->
                     let block = HashMap.lookup name $ LLIR.blocks f
                         (ncx, str) = genBlock cx block f in
                     (ncx, s ++ str))
                   (newFxContext cx, "") $ LLIR.blockOrder f
      strRes = "_" ++ LLIR.functionName f ++ ":\n" ++ prolog ++ blocksStr ++ getEpilog in
    (cx, strRes)

genBlock :: FxContext -> Maybe LLIR.VBlock -> LLIR.VFunction -> (FxContext, String)
genBlock cx Nothing _ = (cx, "BAD\n")
genBlock cx (Just block) f = 
  foldl (\(cx, acc) name ->
          let instruction = HashMap.lookup name $ LLIR.functionInstructions f
              (ncx, str) = genInstruction cx instruction in
                (ncx, acc ++ str))
        (cx, "")
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

genInstruction :: FxContext -> Maybe LLIR.VInstruction -> (FxContext, String)
genInstruction cx Nothing = (cx, "BAD\n")

genInstruction cx (Just (VAllocation _ typ size)) =
  case size of
    Just i -> (cx, "")
    Nothing -> (cx, "")

genInstruction cx (Just (VUnOp _ op val)) =
  let loc = valLoc val $ variables cx 
      final = case val of
        ConstInt _ -> ""
        _ -> "  movq %rax " ++ loc ++ "\n" in
    (cx, 
    "  movq " ++ loc ++ "%rax\n" ++
    "  " ++ op ++ " %rax %rax\n" ++ -- what do I do with this value? I should be creating a new temporary variable and adding a new entry in the table for it
    final)

genInstruction cx (Just (VBinOp _ op val1 val2)) =
    let loc1 = valLoc val1 $ variables cx
        loc2 = valLoc val2 $ variables cx in
          (cx,
          "  movq" ++ loc1 ++ "%rax\n" ++
          "  " ++ op ++ loc2 ++ "% rax\n" ++ -- what do I do with this value? I should be creating a new temporary variable and adding a new entry in the table for it
          "TODO")

genInstruction cx (Just (VMethodCall name isName fname args)) =
  -- push arguments
  let (ncx, nargs) = foldl (\(cx, acc) arg ->
                              let (ncx, narg) = genArg cx arg in
                                    (ncx, acc ++ [narg]))
                           (cx, []) args
      precall = getPreCall nargs
      postcall = getPostCall
      destination = (show $ 8 * (-1)) ++ "(%bpx)" in
        (setVariableLoc ncx name destination, precall ++ "  call " ++ fname ++ "\n  movq %eax " ++ destination ++ "\n")

genInstruction cx (Just (VStore _ _ _)) =
  (cx, "TODO")

genInstruction cx (Just (VLookup _ _)) =
  (cx, "TODO")

genInstruction cx (Just (VArrayStore _ _ _ _)) =
  (cx, "TODO")

genInstruction cx (Just (VArrayLookup _ _ _)) =
  (cx, "TODO")

genInstruction cx (Just (VArrayLen _ _)) =
  (cx, "TODO")

genInstruction cx (Just (VReturn _ _)) =
  (cx, "TODO")

genInstruction cx (Just (VCondBranch _ _ _ _)) =
  (cx, "TODO")

genInstruction cx (Just (VUnreachable _)) =
  (cx, "TODO")

genInstruction cx (Just (VUncondBranch _ _)) =
  (cx, "TODO")

genArg :: FxContext -> ValueRef -> (FxContext, (String, Int))
genArg cx (InstRef ref) =
  {-- TODO: look up global vars in the CGContext! --}
  (cx, (lookupVariable cx ref, 8))
  
genArg cx (ConstInt i) =
  (cx, ("$" ++ (show i), 8))

genArg cx (ConstString s) =
  let (ncx, id) = getConstStrId cx s in
    (ncx, ("$" ++ id, 8))

genArg cx (ConstBool b) =
  (cx, ("$" ++ (if b then "1" else "0"), 8))

genArg cx (ArgRef i funcName) =
  (cx, (lookupVariable cx $ funcName ++ "@" ++ (show i), 8))

gen :: LLIR.PModule -> String
gen mod =
  let globals = LLIR.globals mod
      callouts = LLIR.callouts mod
      fxs = HashMap.elems $ LLIR.functions mod
      cx = newCGContext
      (cx2, fns) =
        foldl (\(cx, asm) fn ->
                let (ncx, str) = genFunction cx fn in
                  (ncx, asm ++ str)) 
              (cx, "") fxs
  in
    getHeader ++ (genGlobals globals) ++ (genCallouts callouts) ++ fns
