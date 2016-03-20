{-# LANGUAGE ScopedTypeVariables #-}

module CodeGen where

import Prelude
import Data.List
import qualified Data.Map as HashMap
import qualified SemanticChecker
import qualified LLIR
import LLIR

getHeader =
  ".section __TEXT,__text\n" ++
  ".globl _main\n"

getMainHeader =
  "\n" ++
  "_main:\n"

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
      argsInRegisters = (foldl (\acc (arg, reg) -> acc ++ "  movq " ++  (fst arg) ++ " " ++ reg ++ "\n") "" (zip args argRegs))
      pushedArgs = (foldl (\acc arg -> acc ++ "  push " ++ (fst arg) ++ "\n") "" remainingArgs) in
  "  #precall\n" ++
  "  pusha                           # save registers\n" ++
  "  movq %rsp, %rbp                 # new stack frame\n" ++
  argsInRegisters ++
  pushedArgs ++
  "  #/precall\n"

getPostCall =
  "  #postcall\n" ++
  "  popa\n" ++
  "  #/postcall\n"

getProlog :: Int -> String
getProlog localsSize =
  "\n" ++
  "  #prolog\n" ++
  "  enter $" ++ (show localsSize) ++ " $0\n" ++
  "  #/prolog\n"

genGlobals :: HashMap.Map String VType -> String
genGlobals globals =
    "  .bss\n" ++ (intercalate "" $ map genGlobal $ HashMap.toList globals)

genGlobal :: (String, VType) -> String
genGlobal (name, typ) =
    "  .global_" ++ name ++ ":\n    .zero 8\n" -- Need to adjust for arrays

genCallouts :: HashMap.Map String String -> String
genCallouts callouts =
    "" -- Not sure how to declare global strings

genFunction :: LLIR.VFunction -> String
genFunction f =
  let entry = HashMap.lookup "entry" (LLIR.blocks f) in
    case entry of
    Just e -> genBlock e
    Nothing -> "BAD\n"

genBlock :: LLIR.VBlock -> String
genBlock block =
   snd $ foldl (\(table, s) instruction ->
   let res = genInstruction instruction table in
     (fst res, s ++ (snd res)))
  (HashMap.empty :: HashMap.Map String String, "") $ LLIR.blockInstructions block

valLoc :: LLIR.ValueRef -> HashMap.Map String String -> String
valLoc (ConstInt int) _ = "$" ++ show int
valLoc (ArgRef idx name) table = HashMap.lookup name table
valLoc (InstRef name) table = HashMap.lookup name table
valLoc (ConstString name) table = HashMap.lookup name table
valLoc (CalloutRef name) table = HashMap.lookup name table
valLoc (GlobalRef name) table = HashMap.lookup name table
valLoc (FunctionRef name) table = HashMap.lookup name table

genInstruction :: LLIR.VInstruction -> HashMap.Map String String -> (HashMap.Map String String, String)
genInstruction (VAllocation _ typ size) =
  case size of
    Just i -> HashMap.fromList [] --TODO
    Nothing -> HashMap.fromList []

genInstruction (VUnOp _ op val) table =
  let loc = valLoc val table
      final = case val of
        ConstInt _ -> ""
        _ -> "  movq %rax " ++ loc ++ "\n" in
    "  movq " ++ loc ++ "%rax\n" ++
    "  " ++ op ++ " %rax %rax\n" ++ -- what do I do with this value? I should be creating a new temporary variable and adding a new entry in the table for it
    final

genInstruction (VBinOp _ op val1 val2) table =
    let loc1 = valLoc val1 table
        loc2 = valLoc val2 table in
          "  movq" ++ loc1 ++ "%rax\n" ++
          "  " ++ op ++ loc2 ++ "% rax\n" ++ -- what do I do with this value? I should be creating a new temporary variable and adding a new entry in the table for it
          "TODO"


gen :: LLIR.PModule -> String
gen mod =
  let globals = LLIR.globals mod
      callouts = LLIR.callouts mod
      fxs = HashMap.elems . LLIR.functions mod in
      getHeader ++
      (genGlobals globals) ++ (genCallouts callouts) ++ (intercalate "\n\n" (map genFunction fxs))
