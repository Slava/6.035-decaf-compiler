{-# LANGUAGE ScopedTypeVariables #-}

module CodeGen where

import Prelude
import qualified Data.Map as HashMap

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
  "  enter $" ++ (show localSize) ++ " $0\n"
  "  #/prolog\n"

gen cx =
  "hello hello"
