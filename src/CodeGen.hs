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
lookupVariable (FxContext _ table _) var = 
  if head var == '$' then var else case HashMap.lookup var table of
                                           Just a -> a
                                           Nothing -> "Couldn't find " ++ var ++ " in " ++ show (HashMap.toList table)

setVariableLoc :: FxContext -> String -> String -> FxContext
setVariableLoc (FxContext global table offset) var loc = FxContext global (HashMap.alter update var table) offset
  where update _ = Just loc

getHeader :: String
getHeader =
  ".section .text\n" ++
  ".globl main\n"

-- args: [(Name, size)]
getPreCall :: [(String, Int)] -> String
getPreCall args =
  let argRegs = ["%rdi", "%rsi", "%rdx", "%rcx", "%r8", "%r9"]
      remainingArgs = drop (length argRegs) args
      argsInRegisters = (foldl (\acc (arg, reg) -> acc ++ "  movq " ++  (fst arg) ++ ", " ++ reg ++ "\n") "" (zip args argRegs))
      pushedArgs = (foldl (\acc arg -> acc ++ "  push " ++ (fst arg) ++ "\n") "" (reverse remainingArgs)) in
  "  #precall\n" ++
  pusha ++
  argsInRegisters ++
  pushedArgs ++
  "  #/precall\n"

getPostCall :: String
getPostCall =
  "  #postcall\n" ++
  popa ++
  "  #/postcall\n"

getProlog :: Int -> Int -> String
getProlog argsLength localsSize =
  let argRegs = ["%rdi", "%rsi", "%rdx", "%rcx", "%r8", "%r9"] in
  "  #prolog\n" ++
  "  enter $" ++ (show (argsLength * 16 + localsSize)) ++ ", $0\n" ++
  unwords (map (\(x, y) -> "  movq " ++ x ++ ", -" ++ (show $ 8 * y) ++ "(%rbp)\n") $ zip argRegs [1..argsLength]) ++
  "  #prolog\n"

getEpilog :: String
getEpilog =
  " \n" ++
  "  #epilog\n" ++
  "  leave\n" ++
  "  ret\n" ++
  "  #/epilog\n"

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
  let argsLength = length $ LLIR.arguments f
      prolog = getProlog argsLength (16 * (length $ (LLIR.functionInstructions f)))
      ncx1 = foldl
                   (\cx (idx, arg) ->
                     setVariableLoc cx 
                                    (LLIR.functionName f ++ "@" ++ show (idx - 1)) 
                                    (" -" ++ (show $ 8 * idx) ++ "(%rbp)\n"))
                   (newFxContext cx)
                   (zip [1..argsLength] $ LLIR.arguments f)
      (ncx2, blocksStr) = foldl
                   (\(cx, s) name ->
                     let block = HashMap.lookup name $ LLIR.blocks f
                         (ncx, str) = genBlock cx block f in
                     (ncx, s ++ str))
                   (ncx1, "") $ LLIR.blockOrder f
      strRes = LLIR.functionName f ++ ":\n" ++ prolog ++ blocksStr ++ getEpilog in
    (global ncx2, strRes)

genBlock :: FxContext -> Maybe LLIR.VBlock -> LLIR.VFunction -> (FxContext, String)
genBlock cx Nothing _ = (cx, "BAD\n")
genBlock cx (Just block) f = 
  foldl (\(cx, acc) name ->
          let instruction = HashMap.lookup name $ LLIR.functionInstructions f
              (ncx, str) = genInstruction cx instruction in
                (ncx, acc ++ str))
        (cx, "")
        (LLIR.blockInstructions block)

genInstruction :: FxContext -> Maybe LLIR.VInstruction -> (FxContext, String)
genInstruction cx Nothing = (cx, "BAD\n")

genInstruction cx (Just (VAllocation _ typ size)) =
  case size of
    Just i -> (cx, "")
    Nothing -> (cx, "")

genInstruction cx (Just (VUnOp _ op val)) =
  let loc = lookupVariable cx $ snd (genAccess cx val) 
      final = case val of
        ConstInt _ -> ""
        _ -> "  movq %rax, " ++ loc ++ "\n" in
    (cx, 
    "  movq " ++ loc ++ ", %rax\n" ++
    "  " ++ op ++ " %rax %rax\n" ++ -- what do I do with this value? I should be creating a new temporary variable and adding a new entry in the table for it
    final)

genInstruction cx (Just (VBinOp result op val1 val2)) =
    let loc1 = lookupVariable cx $ snd (genAccess cx val1) 
        loc2 = lookupVariable cx $ snd (genAccess cx val2) 
        destination = (show $ (offset cx) * (-1)) ++ "(%rbp)"
        ncx = updateOffset $ setVariableLoc cx result destination in
          (ncx,
          "  movq " ++ loc1 ++ ", %rax\n" ++
          "  " ++ genOp op ++ " " ++ loc2 ++ ", %rax\n" ++
          "  movq %rax, " ++ destination ++ "\n" -- ++
          --"  old cx was: " ++ show (HashMap.toList $ variables cx) ++ ", new cx is: " ++ show (HashMap.toList $ variables ncx)
          )

genInstruction cx (Just (VMethodCall name isName fname args)) =
  -- push arguments
  let (ncx, nargs) = foldl (\(cx, acc) arg ->
                              let (ncx, narg) = genArg cx arg in
                                    (ncx, acc ++ [narg]))
                           (cx, []) args
      precall = getPreCall nargs
      postcall = getPostCall
      destination = (show $ (offset cx) * (-1)) ++ "(%rbp)" in
        (updateOffset $ setVariableLoc ncx name destination, 
         precall ++ "  call " ++ fname ++ "\n  movq %rax, " ++ destination ++ "\n" ++ postcall)

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

genInstruction cx (Just (VReturn _ maybeRef)) =
  case maybeRef of
    Just ref ->
      (cx, "  movq " ++ (snd (genAccess cx ref)) ++ ", %rax\n")
    Nothing -> (cx, "")

genInstruction cx (Just (VCondBranch _ _ _ _)) =
  (cx, "TODO")

genInstruction cx (Just (VUnreachable _)) =
  (cx, "TODO")

genInstruction cx (Just (VUncondBranch _ _)) =
  (cx, "TODO")

genOp :: String -> String
genOp "+" = "addq"
genOp "-" = "subq"
genOp "*" = "mulq"
genOp "/" = "divq"

genArg :: FxContext -> ValueRef -> (FxContext, (String, Int))
genArg cx x =
  let (ncx, asm) = genAccess cx x in
  (ncx, (asm, 8))

genAccess :: FxContext -> ValueRef -> (FxContext, String)
genAccess cx (InstRef ref) =
  {-- TODO: look up global vars in the CGContext! --}
  (cx, lookupVariable cx ref)
  
genAccess cx (ConstInt i) =
  (cx, "$" ++ (show i))

genAccess cx (ConstString s) =
  let (ncx, id) = getConstStrId cx s in
    (ncx, "$" ++ id)

genAccess cx (ConstBool b) =
  (cx, "$" ++ (if b then "1" else "0"))

genAccess cx (ArgRef i funcName) =
  (cx, lookupVariable cx $ funcName ++ "@" ++ (show i))

genConstants cx =
  ".section .rodata\n" ++
  foldl (\str (label, cnst) ->
          str ++ "\n" ++ label ++ ":\n  .string " ++ cnst) "" (constStrs cx)


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
    (genGlobals globals) ++
    getHeader ++
    (genCallouts callouts) ++
    fns ++
    "\n\n" ++
    (genConstants cx2)

pusha =
  "  push %rax\n" ++
  "  push %rbx\n" ++
  "  push %rcx\n" ++
  "  push %rdx\n" ++
  "  push %rsi\n" ++
  "  push %rdi\n" ++
  "  push %rbp\n" ++
  "  push %rsp\n" ++
  "  push %r8\n" ++
  "  push %r9\n" ++
  "  push %r10\n" ++
  "  push %r11\n" ++
  "  push %r12\n" ++
  "  push %r13\n" ++
  "  push %r14\n" ++
  "  push %r15\n"

popa =
  "  pop %r15\n" ++
  "  pop %r14\n" ++
  "  pop %r13\n" ++
  "  pop %r12\n" ++
  "  pop %r11\n" ++
  "  pop %r10\n" ++
  "  pop %r9\n" ++
  "  pop %r8\n" ++
  "  pop %rsp\n" ++
  "  pop %rbp\n" ++
  "  pop %rdi\n" ++
  "  pop %rsi\n" ++
  "  pop %rdx\n" ++
  "  pop %rcx\n" ++
  "  pop %rbx\n" ++
  "  pop %rax\n"
