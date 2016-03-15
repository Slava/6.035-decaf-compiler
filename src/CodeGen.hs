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
  "  #precall\n" ++
  "  pusha                           # save registers\n" ++
  "  movq %rsp, %rbp                 # new stack frame\n" ++
  -- XXX push arguments
  -- 	movl	$1, %edi
  --    movl	$2, %esi
  --    movl	$3, %edx
  --    movl	$4, %ecx
  --    movl	$5, %r8d
  --    movl	$6, %r9d
  --    movl	$7, %eax
  --    movl	$8, %r10d
  --    movl	$9, %r11d
  --    movl	$10, %ebx
  --    movl	$11, %r14d
  --    movl	$12, %r15d
  --    movl	$13, %r12d
  --    movl	$14, %r13d

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
