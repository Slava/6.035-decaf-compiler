{-# LANGUAGE ScopedTypeVariables #-}

module CodeGen where

import Prelude
import Data.List
import qualified Data.Map as HashMap
import qualified LLIR
import LLIR
import Text.Printf

data CGContext = CGContext {
  -- label, constant string
  constStrs :: [(String, String)],
  nextConstStrId :: Int,
  -- global arrays with sizes
  globalArrays :: [(String, Int)]
}

newCGContext :: CGContext
newCGContext = CGContext [] 0 []

getConstStrId :: FxContext -> String -> (FxContext, String)
getConstStrId fcx str =
  let gcx = global fcx
      next = (nextConstStrId gcx)
      id = ".const_str" ++ (show next)
      gcx2 = gcx{
        constStrs=(constStrs gcx) ++ [(id, str)],
        nextConstStrId = next + 1
      }
      in (fcx{global=gcx2}, id)

addGlobals (CGContext constStrs nextConstStrId globalArrays) globals =
  -- only collects sizes of global arrays so the beginning of main function can set the lengths.
  let arrays = filter (\(_, (_, size)) -> case size of
                          Just _ -> True
                          Nothing -> False)
        (HashMap.toList globals)
      l = map (\(name, (_, Just size)) -> (".global_" ++ name, size)) arrays in
  CGContext constStrs nextConstStrId l

data FxContext = FxContext {
  name   :: String,
  global :: CGContext,
  -- variables maps registers to a label/reg + offset
  variables :: HashMap.Map String (String, Int),
  offset :: Int,
  instrs :: [String],
  errors :: [String]
}

newFxContext :: String -> CGContext -> FxContext
newFxContext name global = FxContext name global HashMap.empty 8 [] []

updateOffsetBy :: FxContext -> Int -> FxContext
updateOffsetBy fcx size = fcx{offset=(offset fcx) + size}

updateOffset :: FxContext -> FxContext
updateOffset fcx = updateOffsetBy fcx 8

locStr :: (String, Int) -> String
locStr (place, offset) =
  if offset /= 0 then (show offset) ++ "(" ++ place ++ ")" else place

lookupVariable :: FxContext -> String -> String
lookupVariable fxc var =
  let table = (variables fxc) in
  case head var of
    '$' -> var
    _ -> let (place, offset) :: (String, Int) = (HashMap.!) table var  in
            locStr (place, offset)

lookupVariableWithOffset :: FxContext -> String -> (String, Int)
lookupVariableWithOffset fcx var =
  let table = variables fcx in (HashMap.!) table var

setVariableLoc :: FxContext -> String -> (String, Int) -> FxContext
setVariableLoc fcx var loc = fcx{variables=HashMap.alter update var (variables fcx)}
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
      pushedArgs = (foldl (\acc arg -> acc ++ "  pushq " ++ (fst arg) ++ "\n") "" (reverse remainingArgs)) in
  "  #precall\n" ++
  pusha ++
  argsInRegisters ++
  pushedArgs ++
  "  #/precall\n"

getPostCall :: Int -> String
getPostCall numArguments =
  "  #postcall\n" ++
  (intercalate "" $ replicate (numArguments - 6) "  pop %rax\n") ++
  popa ++
  "  #/postcall\n"

getProlog :: Int -> Int -> String
getProlog argsLength localsSize =
  let argRegs = ["%rdi", "%rsi", "%rdx", "%rcx", "%r8", "%r9"] in
  "  #prolog\n" ++
  "  enter $" ++ (show (argsLength * 16 + localsSize)) ++ ", $0\n" ++
  -- put register arguments to stack
  unwords (map (\(x, y) -> "  movq " ++ x ++ ", -" ++ (show $ 8 * y) ++ "(%rbp)\n") $ zip argRegs [1..argsLength]) ++
  -- put stack arguments to stack (again, but after the reg args for easy access)
  unwords (map (\(revIdx, argIdx) -> "  movq " ++ (show $ (revIdx + 1) * 8) ++ "(%rbp), %rax\n  movq %rax, -" ++ (show $ 8 * argIdx) ++ "(%rbp)\n") $ zip [1..argsLength] (drop 6 [1..argsLength])) ++
  "  #prolog\n"

getEpilog :: String
getEpilog =
  " \n" ++
  "  #epilog\n" ++
  "  leaveq\n" ++
  "  ret\n" ++
  "  #/epilog\n"

genGlobals :: HashMap.Map String (VType, Maybe Int) -> String
genGlobals globals =
    ".bss\n" ++ (intercalate "" $ map genGlobal $ HashMap.toList globals) ++ "\n"

genGlobal :: (String, (VType, Maybe Int)) -> String
genGlobal (name, (_, Nothing)) =
    ".global_" ++ name ++ ":\n  .zero 8\n" -- Need to adjust for arrays
genGlobal (name, (_, Just size)) =
    -- an extra 8-byte word for storing the length
    ".global_" ++ name ++ ":\n  .zero " ++ show (8 * (1 + size)) ++ "\n"

genCallouts :: HashMap.Map String String -> String
genCallouts callouts =
    "" -- Not sure how to declare global strings

closestMultipleOf16 num =
  ((num + 15) `div` 16) * 16

calculateLocalsSize instrs =
  foldl (+) 0 (map (\instr -> case instr of
                       VStore _ _ _ -> 0
                       VArrayStore _ _ _ _ -> 0
                       VReturn _ _ -> 0
                       VCondBranch _ _ _ _ -> 0
                       VUncondBranch _ _ -> 0
                       VUnreachable _ -> 0
                       VAllocation _ _ (Just x) -> (x + 1) * 8
                       VAllocation _ _ Nothing -> 8
                       _ -> 8
                       ) instrs)

genFunction :: CGContext -> LLIR.VFunction -> (CGContext, String)
genFunction cx f =
  let argsLength = length $ LLIR.arguments f
      localsSize = calculateLocalsSize $ map snd $ HashMap.toList (LLIR.functionInstructions f)
      prolog = getProlog argsLength (closestMultipleOf16 localsSize)
      ncx1 = foldl
                   (\cx (idx, arg) ->
                     setVariableLoc cx
                                    (LLIR.functionName f ++ "@" ++ show (idx - 1))
                                    ("%rbp", (-8) * idx))
                   (newFxContext (LLIR.functionName f) cx)
                   (zip [1..argsLength] $ LLIR.arguments f)
      (ncx2, blocksStr) = foldl
                   (\(cx, s) name ->
                     let block = (HashMap.!) (LLIR.blocks f) name
                         (ncx, str) = genBlock cx block name f in
                     (ncx, s ++ str))
                   (ncx1, "") $ LLIR.blockOrder f
      strRes = "\n" ++ LLIR.functionName f ++ ":\n" ++ prolog ++ blocksStr ++ getEpilog in
    (global ncx2, strRes)

genBlock :: FxContext -> LLIR.VBlock -> String -> LLIR.VFunction -> (FxContext, String)
genBlock cx block name f = (ncx, blockName ++ ":\n" ++ setupGlobals ++ s)
  where (ncx, s) = foldl (\(cx, acc) name ->
          let instruction = (HashMap.!) (LLIR.functionInstructions f) name
              (ncx, str) = genInstruction cx instruction in
                (ncx, acc ++ str))
          (cx, "")
          (LLIR.blockInstructions block)
        blockName = LLIR.blockFunctionName block ++ "_" ++ LLIR.blockName block
        setupGlobals = if blockName /= "main_entry" then "" else genSetupGlobals (global cx)

genSetupGlobals cx =
  concat $ map (\(name, size) -> "  movq $" ++ (show size) ++ ", " ++ name ++ "\n") $ globalArrays cx

arrayToLine :: [String] -> String
arrayToLine ar = concat $ map (\x -> "  " ++ x ++ "\n") ar

genInstruction cx (VAllocation result tp size) =
  let s = case size of
                 Just i -> i
                 Nothing -> 0
      -- reserve first 8-byte number to store the length of the array
      bytes = ((s + 1) * 8)

      -- in case of an array, skip first byte
      stackOffset = (offset cx) * (-1)
      destination = (show stackOffset) ++ "(%rbp)"
      firstOffset = if s > 0 then stackOffset - (bytes - 8) else stackOffset
      first = (show firstOffset) ++ "(%rbp)"

      ncx :: FxContext = case size of
        -- if array, store location of its length lookup at the head
        Just i -> setVariableLoc cx (result ++ "@len") ("%rbp", stackOffset)
        Nothing -> cx
      ncx2 = setVariableLoc ncx result ("%rbp", firstOffset)
      in
        (updateOffsetBy ncx2 bytes,
         "  # allocate " ++ (show bytes) ++ " bytes on stack\n" ++
         if s > 0 then ("  movq $" ++ (show s) ++ ", " ++ destination ++ "\n") else "")

genInstruction cx (VUnOp result op val) =
  let loc = snd $ genAccess cx val
      instruction = case op of
        "-" -> "  negq %rax\n"
        "!" -> "  testq %rax, %rax\n  movq $0, %rax\n  setz %al\n"
      stackOffset = (offset cx) * (-1)
      destination = (show stackOffset) ++ "(%rbp)"
      ncx = updateOffset $ setVariableLoc cx result ("%rbp", stackOffset) in
    (ncx,
    "  movq " ++ loc ++ ", %rax\n" ++
    instruction ++
    "  movq %rax, " ++ destination ++ "\n")

genInstruction cx (VBinOp result op val1 val2) =
    let loc1 = snd $ genAccess cx val1
        loc2 = snd $ genAccess cx val2
        stackOffset = (offset cx) * (-1)
        destination = (show stackOffset) ++ "(%rbp)"
        ncx = updateOffset $ setVariableLoc cx result ("%rbp", stackOffset) in
          (ncx,
          (
            if ((op == "/") || (op == "%")) then
              -- in A/B require A in rax, rdx empty
              "  movq " ++ loc1 ++ ", %rax\n" ++
              let (instA, out) = genOpB op loc2 in
                (arrayToLine instA) ++ (
                  if out /= "%rax" then
                    printf "  movq %s, %s\n" out "%rax"
                  else ""
                )
            else
            "  movq " ++ loc1 ++ ", %rax\n" ++ ( arrayToLine $ genOp op loc2 "%rax")
          ) ++
          "  movq %rax, " ++ destination ++ "\n" -- ++
          --"  old cx was: " ++ show (HashMap.toList $ variables cx) ++ ", new cx is: " ++ show (HashMap.toList $ variables ncx)
          )

genInstruction cx (VMethodCall name isCallout fname args) =
  -- push arguments
  let (ncx, nargs) = foldl (\(cx, acc) arg ->
                              let (ncx, narg) = genArg cx arg in
                                    (ncx, acc ++ [narg]))
                           (cx, []) args
      precall = getPreCall nargs
      cleanRax = "  movq $0, %rax\n"
      postcall = getPostCall $ length args
      stackOffset = (offset cx) * (-1)
      destination = (show stackOffset) ++ "(%rbp)"
      (ncx2, exitMessage) = if fname == "exit" && isCallout then genExitMessage cx (args !! 0) else (ncx, "") in
        (updateOffset $ setVariableLoc ncx2 name ("%rbp", stackOffset),
         exitMessage ++ precall ++ cleanRax ++ "  callq " ++ fname ++ "\n  movq %rax, " ++ destination ++ "\n" ++ postcall)

genInstruction cx (VStore _ val var) =
  let loc1 = snd $ genAccess cx val
      loc2 = snd $ genAccess cx var in
    (cx,
    --show v ++ "\n" ++
    "  movq " ++ loc1 ++ ", %rax\n" ++
    "  movq %rax, " ++ loc2 ++ "\n")

genInstruction cx (VLookup result val) =
  let loc = snd $ genAccess cx val
      stackOffset = (offset cx) * (-1)
      destination = (show stackOffset) ++ "(%rbp)"
      ncx = updateOffset $ setVariableLoc cx result ("%rbp", stackOffset) in
        (ncx,
        "  movq " ++ loc ++ ", %rax\n" ++
        "  movq %rax, " ++ destination ++ "\n")

genInstruction cx (VArrayStore _ val arrayRef idxRef) =
  let arr = case arrayRef of
              InstRef s -> lookupVariable cx s
              GlobalRef s -> ".global_" ++ s
              _ -> "bad array store " ++ (show arrayRef)
      isGlobal = case arrayRef of
        GlobalRef _ -> True
        _ -> False
      idx = snd $ genAccess cx idxRef
      loc = snd $ genAccess cx val in
  (cx,
  "  leaq " ++ arr ++ ", %rax\n" ++
  "  movq " ++ idx ++ ", %rbx\n" ++
  (if isGlobal then "  addq $1, %rbx\n" else "") ++
  "  leaq (%rax, %rbx, 8), %rbx\n" ++
  "  movq " ++ loc ++ ", %rax\n" ++
  "  movq %rax, (%rbx)\n")

genInstruction cx (VArrayLookup result arrayRef idxRef) =
  let arr = case arrayRef of
              InstRef s -> lookupVariable cx s
              GlobalRef s -> ".global_" ++ s
              _ -> "bad array lookup " ++ (show arrayRef)
      isGlobal = case arrayRef of
        GlobalRef _ -> True
        _ -> False
      idx = snd $ genAccess cx idxRef
      stackOffset = (offset cx) * (-1)
      destination = (show stackOffset) ++ "(%rbp)"
      ncx = updateOffset $ setVariableLoc cx result ("%rbp", stackOffset) in
  (ncx,
  "  leaq " ++ arr ++ ", %rax\n" ++
  "  movq " ++ idx ++ ", %rbx\n" ++
  (if isGlobal then "  addq $1, %rbx\n" else "") ++
  "  movq (%rax, %rbx, 8), %rbx\n" ++
  "  movq %rbx, " ++ destination ++ "\n")

genInstruction cx (VArrayLen result ref) =
     let access = case ref of
            InstRef s -> lookupVariable cx (s ++ "@len")
            GlobalRef s -> ".global_" ++ s
            _ -> "bad VArrayLen of " ++ (show ref)
         stackOffset = (offset cx) * (-1)
         destination = (show stackOffset) ++ "(%rbp)"
         ncx = updateOffset $ setVariableLoc cx result ("%rbp", stackOffset) in
   (ncx,
   "  movq " ++ access ++ ", %rax\n" ++
   "  movq %rax, " ++ destination ++ "\n")


genInstruction cx (VReturn _ maybeRef) =
  case maybeRef of
    Just ref -> (cx, "  movq " ++ (snd (genAccess cx ref)) ++ ", %rax\n  leave\n  ret\n")
    Nothing -> (cx, "  leave\n  ret\n")

genInstruction cx (VCondBranch _ cond true false) =
  let loc = snd $ genAccess cx cond in
    (cx,
    "  movq " ++ loc ++ ", %rax\n" ++
    "  testq %rax, %rax\n" ++
    "  jnz " ++ name cx ++ "_" ++ true ++ "\n" ++
    "  jz " ++ name cx ++ "_" ++ false ++ "\n")

genInstruction cx (VUnreachable _) =
  (cx, "  # unreachable instruction\n")

genInstruction cx (VUncondBranch _ dest) =
  (cx, "  jmp " ++ name cx ++ "_" ++ dest ++ "\n")

genInstruction cx (VZeroInstr _ ref size) =
  let dest = snd $ genAccess cx ref in
  (cx,
  "  # bzero\n" ++
  "  cld\n" ++
  "  leaq " ++ dest ++ ", %rdi\n" ++
  "  movq $" ++ (show (size `div` 8)) ++ ", %rcx\n" ++
  "  movq $0, %rax\n" ++
  "  rep stosq\n" ++
  "  # /bzero\n")

genExitMessage :: FxContext -> ValueRef -> (FxContext, String)
genExitMessage cx val = (ncx, "  xorq %rax, %rax\n  movq $" ++ message ++ ", %rdi\n" ++ "  call printf\n")
  where (ncx, message) = case val of
                            LLIR.ConstInt (-1) -> getConstStrId cx ("\"*** RUNTIME ERROR ***: Array out of Bounds access in method \\\"" ++ name cx ++ "\\\"\\n\"")
                            LLIR.ConstInt (-2) -> getConstStrId cx ("\"*** RUNTIME ERROR ***: Method \\\"" ++ name cx ++ "\\\" didn't return\\n\"")

quadRegToByteReg :: String -> String
quadRegToByteReg a
  | a == "%rax" = "%al"
  | a == "%rbx" = "%bl"
  | a == "%rcx" = "%cl"
  | a == "%rdx" = "%dl"
  | a == "%r8"  = "%r8b"
  | a == "%r9"  = "%r9b"
  | a == "%r10" = "%r10b"
  | a == "%r11" = "%r11b"
  | a == "%r12" = "%r12b"
  | a == "%r13" = "%r13b"
  | a == "%r14" = "%r14b"
  | a == "%r15" = "%r15b"
  | a == "%rsp" = "%spl"
  | a == "%rbp" = "%bpl"
  | a == "%rsi" = "%sil"
  | a == "%rsd" = "%dil"

quadRegToWordReg :: String -> String
quadRegToWordReg a
  | a == "%rax" = "%eax"
  | a == "%rbx" = "%ebx"
  | a == "%rcx" = "%ecx"
  | a == "%rdx" = "%edx"
  | a == "%r8"  = "%r8b"
  | a == "%r9"  = "%r9b"
  | a == "%r10" = "%r10d"
  | a == "%r11" = "%r11d"
  | a == "%r12" = "%r12d"
  | a == "%r13" = "%r13d"
  | a == "%r14" = "%r14d"
  | a == "%r15" = "%r15d"
  | a == "%rsp" = "%esp"
  | a == "%rbp" = "%ebp"
  | a == "%rsi" = "%esi"
  | a == "%rsd" = "%ed"

zero :: String -> String
zero reg = printf "xorl %s, %s" reg

-- arg2 must be register, arg1 may be memory
--          OP -> arg1 -> arg2 / output -> insts
genOp :: String -> String -> String -> [String]
-- out is RHS and must be reg/mem, loc is LHS could be immediate/etc
genOp "+"   loc out = [printf "addq %s, %s" loc out]
genOp "-"   loc out = [printf "subq %s, %s" loc out]
genOp "*"   loc out = [printf "imulq %s, %s" loc out]

genOp "=="  loc out = [printf "cmpq %s, %s" loc out, printf "sete %s" $ quadRegToByteReg out,  printf "movzx %s, %s" (quadRegToByteReg out) (quadRegToWordReg out)]
genOp "!="  loc out = [printf "cmpq %s, %s" loc out, printf "setne %s" $ quadRegToByteReg out, printf "movzx %s, %s" (quadRegToByteReg out) (quadRegToWordReg out)]

genOp "<"   loc out = [printf "cmpq %s, %s" loc out, printf "setl %s" $ quadRegToByteReg out, printf "movzx %s, %s" (quadRegToByteReg out) (quadRegToWordReg out)]
genOp "<="  loc out = [printf "cmpq %s, %s" loc out, printf "setle %s" $ quadRegToByteReg out, printf "movzx %s, %s" (quadRegToByteReg out) (quadRegToWordReg out)]
genOp ">"   loc out = [printf "cmpq %s, %s" loc out, printf "setg %s" $ quadRegToByteReg out, printf "movzx %s, %s" (quadRegToByteReg out) (quadRegToWordReg out)]
genOp ">="  loc out = [printf "cmpq %s, %s" loc out, printf "setge %s" $ quadRegToByteReg out, printf "movzx %s, %s" (quadRegToByteReg out) (quadRegToWordReg out)]

genOp "u<"  loc out = [printf "cmpq %s, %s" loc out, printf "setb %s" $ quadRegToByteReg out, printf "movzx %s, %s" (quadRegToByteReg out) (quadRegToWordReg out)]
genOp "u<=" loc out = [printf "cmpq %s, %s" loc out, printf "setbe %s" $ quadRegToByteReg out, printf "movzx %s, %s" (quadRegToByteReg out) (quadRegToWordReg out)]
genOp "u>"  loc out = [printf "cmpq %s, %s" loc out, printf "seta %s" $ quadRegToByteReg out, printf "movzx %s, %s" (quadRegToByteReg out) (quadRegToWordReg out)]
genOp "u>=" loc out = [printf "cmpq %s, %s" loc out, printf "setae %s" $ quadRegToByteReg out, printf "movzx %s, %s" (quadRegToByteReg out) (quadRegToWordReg out)]

genOp "|"   loc out = [printf "orq %s, %s" loc out] -- ++ ", %rax\n  cmp %rax, $0\n  movq $0, %rax\n  setnz %al\n"
genOp "&"   loc out = [printf "andq %s, %s" loc out]-- ++ ", %rax\n  cmp %rax, $0\n  movq $0, %rax\n  setnz %al\n"

-- requires RAX, RDX, and divisor
-- In A/B %rax must contain A, arg2 contains B
-- returns instructions, output
-- op arg2
genOpB :: String -> String -> ([String], String)
genOpB "/" arg2 = (["cqto", printf "idivq %s" arg2], "%rax")
genOpB "%" arg2 = (["cqto", printf "idivq %s" arg2], "%rdx")

genArg :: FxContext -> ValueRef -> (FxContext, (String, Int))
genArg cx x =
  let (ncx, asm) = genAccess cx x in
  (ncx, (asm, 8))

genAccess :: FxContext -> ValueRef -> (FxContext, String)
genAccess cx (InstRef ref) =
  (cx, lookupVariable cx ref)

genAccess cx (ConstInt i) =
  (cx, "$" ++ (show i))

genAccess cx (ConstString s) =
  let (ncx, id) = getConstStrId cx s in
    (ncx, "$" ++ id)

genAccess cx (ConstBool b) =
  (cx, "$" ++ (if b then "1" else "0"))

genAccess cx (ArgRef i funcName) =
  (cx, if i < 6 then lookupVariable cx $ funcName ++ "@" ++ (show i) else (show $ 16 + 8 * (i - 6)) ++ "(%rbp)")

genAccess cx (GlobalRef name) =
  (cx, ".global_" ++ name)

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
      cx2 = addGlobals cx globals
      (cx3, fns) =
        foldl (\(cx, asm) fn ->
                let (ncx, str) = genFunction cx fn in
                  (ncx, asm ++ str))
              (cx2, "") fxs
  in
    (genGlobals globals) ++
    getHeader ++
    (genCallouts callouts) ++
    fns ++
    "\n\n" ++
    (genConstants cx3) ++ "\n"

pusha =
  "  push %rax\n" ++
  "  push %rbx\n" ++
  "  push %rcx\n" ++
  "  push %rdx\n" ++
  "  push %rsi\n" ++
  "  push %rdi\n" ++
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
  "  pop %rdi\n" ++
  "  pop %rsi\n" ++
  "  pop %rdx\n" ++
  "  pop %rcx\n" ++
  "  pop %rbx\n" ++
  "  pop %rax\n"
