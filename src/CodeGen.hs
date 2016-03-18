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
  let argRegs = ["%edi", "%esi", "%edx", "%ecx", "%r8d", "%r9d", "%eax", "%r10d", "%r11d", "%ebx", "%r14d", "%r15d", "%r12d", "%13d"] in

  "  #precall\n" ++
  "  pusha                           # save registers\n" ++
  "  movq %rsp, %rbp                 # new stack frame\n" ++
  (foldl (\acc (arg, reg) ->
    acc ++ "  " ++ "  #TODO\n"
) "" (zip args argRegs))
  -- XXX push the remaining arguments to stack

  "  #/precall\n"

getPostCall =
  "  #postcall\n" ++
  "  popa\n" ++
  "  #/postcall\n"

getProlog :: Int -> String
getProlog localsSize =
  "\n" ++
  "  #prolog\n" ++
  "  " ++
  "  " ++
  "  #/prolog\n"

gen cx =
  "hello hello"
