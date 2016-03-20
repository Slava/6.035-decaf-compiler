{-# LANGUAGE ScopedTypeVariables #-}

module CodeGen where

import Prelude
import Data.List
import qualified Data.Map as HashMap
import qualified LLIR
import LLIR

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
      argsInRegisters = (foldl (\acc (arg, reg) -> acc ++ "  movq " ++  (fst arg) ++ " " ++ reg ++ "\n") "" (zip args argRegs))
      pushedArgs = (foldl (\acc arg -> acc ++ "  push " ++ (fst arg) ++ "\n") "" remainingArgs) in
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
  "\n" ++
  "  #prolog\n" ++
  "  pusha\n" ++
  "  enter $" ++ (show localsSize) ++ " $0\n" ++
  "  #prolog\n"

getEpilog :: String
getEpilog =
  "\n" ++
  "  #epilog\n" ++
  "  leave\n" ++
  "  popa\n" ++
  "  #epilog\n"

genGlobals :: HashMap.Map String (VType, Maybe Int) -> String
genGlobals globals =
    "  .bss\n" ++ (intercalate "" $ map genGlobal $ HashMap.toList globals)

genGlobal :: (String, (VType, Maybe Int)) -> String
genGlobal (name, (_, Nothing)) =
    "  .global_" ++ name ++ ":\n    .zero 8\n" -- Need to adjust for arrays
genGlobal (name, (_, Just size)) =
    "  .global_" ++ name ++ ":\n    .zero " ++ show (8 * size) ++ "\n"

genCallouts :: HashMap.Map String String -> String
genCallouts callouts =
    "" -- Not sure how to declare global strings

genFunction :: LLIR.VFunction -> String
genFunction f =
  getProlog (8 * (length $ (LLIR.functionInstructions f))) ++
  (snd $ foldl (\(table, s) name ->
    let block = HashMap.lookup name $ LLIR.blocks f
        res = genBlock block f table in
      (fst res, s ++ (snd res)))
  (HashMap.empty :: HashMap.Map String String, "") $ LLIR.blockOrder f) ++
  getEpilog

genBlock :: Maybe LLIR.VBlock -> LLIR.VFunction -> HashMap.Map String String -> (HashMap.Map String String, String)
genBlock Nothing _ table = (table, "BAD\n")
genBlock (Just block) f table = 
  foldl (\(t, acc) name ->
          let instruction = HashMap.lookup name $ LLIR.functionInstructions f
              res = genInstruction instruction t in
                (fst res, acc ++ snd res))
        (table, "")
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

genInstruction :: Maybe LLIR.VInstruction -> HashMap.Map String String -> (HashMap.Map String String, String)
genInstruction Nothing table = (table, "BAD\n")

genInstruction (Just (VAllocation _ typ size)) table =
  case size of
    Just i -> (table, "")
    Nothing -> (table, "")

genInstruction (Just (VUnOp _ op val)) table =
  let loc = valLoc val table
      final = case val of
        ConstInt _ -> ""
        _ -> "  movq %rax " ++ loc ++ "\n" in
    (table, 
    "  movq " ++ loc ++ "%rax\n" ++
    "  " ++ op ++ " %rax %rax\n" ++ -- what do I do with this value? I should be creating a new temporary variable and adding a new entry in the table for it
    final)

genInstruction (Just (VBinOp _ op val1 val2)) table =
    let loc1 = valLoc val1 table
        loc2 = valLoc val2 table in
          (table, 
          "  movq" ++ loc1 ++ "%rax\n" ++
          "  " ++ op ++ loc2 ++ "% rax\n" ++ -- what do I do with this value? I should be creating a new temporary variable and adding a new entry in the table for it
          "TODO")


gen :: LLIR.PModule -> String
gen mod =
  let globals = LLIR.globals mod
      callouts = LLIR.callouts mod
      fxs = HashMap.elems $ LLIR.functions mod in
        getHeader ++
        (genGlobals globals) ++ (genCallouts callouts) ++ (intercalate "\n\n" (map genFunction fxs))
