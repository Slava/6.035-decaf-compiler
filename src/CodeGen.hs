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
  nextConstStrId :: Int,
  -- global arrays with sizes
  globalArrays :: [(String, Int)]
}

newCGContext :: CGContext
newCGContext = CGContext [] 0 []

getConstStrId :: FxContext -> String -> (FxContext, String)
getConstStrId (FxContext name (CGContext strs next globs) table offset) str =
  (FxContext name newGlobal table offset, id)
  where id = ".const_str" ++ (show next)
        newGlobal = CGContext{
          constStrs = strs ++ [(id, str)],
          nextConstStrId = next + 1,
          globalArrays = globs
        }

addGlobals (CGContext constStrs nextConstStrId globalArrays) globals =
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
  offset :: Int
}

newFxContext :: String -> CGContext -> FxContext
newFxContext name global = FxContext name global HashMap.empty 8

updateOffset :: FxContext -> FxContext
updateOffset (FxContext name global table offset) = FxContext name global table $ offset + 8

updateOffsetBy :: FxContext -> Int -> FxContext
updateOffsetBy (FxContext name global table offset) size = FxContext name global table $ offset + size

locStr (place, offset) =
  if offset /= 0 then (show offset) ++ "(" ++ place ++ ")" else place

lookupVariable :: FxContext -> String -> String
lookupVariable (FxContext _ _ table _) var = 
  if head var == '$' then var else case HashMap.lookup var table of
                                           Just (place, offset) -> locStr (place, offset)
                                           Nothing -> "Couldn't find " ++ var ++ " in " ++ show (HashMap.toList table)

lookupVariableWithOffset :: FxContext -> String -> (String, Int)
lookupVariableWithOffset (FxContext _ _ table _) var = 
  case HashMap.lookup var table of
    Just loc -> loc
    Nothing -> ("Couldn't find " ++ var ++ " in " ++ show (HashMap.toList table), 0)

setVariableLoc :: FxContext -> String -> (String, Int) -> FxContext
setVariableLoc (FxContext name global table offset) var loc = FxContext name global (HashMap.alter update var table) offset
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
  -- TODO: pop arguments
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
                     let block = HashMap.lookup name $ LLIR.blocks f
                         (ncx, str) = genBlock cx block name f in
                     (ncx, s ++ str))
                   (ncx1, "") $ LLIR.blockOrder f
      strRes = LLIR.functionName f ++ ":\n" ++ prolog ++ blocksStr ++ getEpilog in
    (global ncx2, strRes)

genBlock :: FxContext -> Maybe LLIR.VBlock -> String -> LLIR.VFunction -> (FxContext, String)
genBlock cx Nothing name _ = (cx, "# no op block. Block " ++ name ++ " wasn't found\n")
genBlock cx (Just block) name f = (ncx, blockName ++ ":\n" ++ setupGlobals ++ s)
  where (ncx, s) = foldl (\(cx, acc) name ->
          let instruction = HashMap.lookup name $ LLIR.functionInstructions f
              (ncx, str) = genInstruction cx instruction in
                (ncx, acc ++ str))
          (cx, "")
          (LLIR.blockInstructions block)
        blockName = LLIR.blockFunctionName block ++ "_" ++ LLIR.blockName block
        setupGlobals = if blockName /= "main_entry" then "" else genSetupGlobals (global cx)

genSetupGlobals cx =
  concat $ intersperse "\n" $ map (\(name, size) -> "  movq $" ++ (show size) ++ ", " ++ name) $ globalArrays cx

genInstruction :: FxContext -> Maybe LLIR.VInstruction -> (FxContext, String)
genInstruction cx Nothing = (cx, "# empty instruction\n")

genInstruction cx (Just (VAllocation result tp size)) =
  let s = case size of
                 Just i -> i
                 Nothing -> 0
      -- reserve first 8-byte number to store the length of the array
      bytes = ((s + 1) * 8)

      -- in case of an array, skip first byte
      stackOffset = (offset cx) * (-1)
      destination = (show stackOffset) ++ "(%rbp)"
      firstOffset = if s > 0 then stackOffset - 8 else stackOffset
      first = (show firstOffset) ++ "(%rbp)"

      ncx :: FxContext = case size of
        -- if array, store location of its length lookup at the head
        Just i -> setVariableLoc cx (result ++ "@len") ("%rbp", stackOffset)
        Nothing -> cx
      in
        (updateOffsetBy (setVariableLoc ncx result ("%rbp", firstOffset)) bytes,
         "  # allocate " ++ (show bytes) ++ " bytes on stack\n" ++
         if s > 0 then ("  movq $" ++ (show s) ++ ", " ++ destination ++ "\n") else "")

genInstruction cx (Just (VUnOp result op val)) =
  let loc = snd $ genAccess cx val 
      instruction = case op of
        "-" -> "  negq %rax\n"
        "!" -> "  test %rax, %rax\n  setz %al\n"
      stackOffset = (offset cx) * (-1)
      destination = (show stackOffset) ++ "(%rbp)"
      ncx = updateOffset $ setVariableLoc cx result ("%rbp", stackOffset) in
    (ncx, 
    "  movq " ++ loc ++ ", %rax\n" ++
    instruction ++
    "  movq %rax, " ++ destination ++ "\n")

genInstruction cx (Just (VBinOp result op val1 val2)) =
    let loc1 = snd $ genAccess cx val1 
        loc2 = snd $ genAccess cx val2 
        stackOffset = (offset cx) * (-1)
        destination = (show stackOffset) ++ "(%rbp)"
        ncx = updateOffset $ setVariableLoc cx result ("%rbp", stackOffset) in
          (ncx,
          "  movq " ++ loc1 ++ ", %rax\n" ++
          genOp op loc2 ++
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
      stackOffset = (offset cx) * (-1)
      destination = (show stackOffset) ++ "(%rbp)" in
        (updateOffset $ setVariableLoc ncx name ("%rbp", stackOffset),
         precall ++ "  call " ++ fname ++ "\n  movq %rax, " ++ destination ++ "\n" ++ postcall)

genInstruction cx (Just v@(VStore _ val var)) =
  let loc1 = snd $ genAccess cx val
      loc2 = snd $ genAccess cx var in
    (cx,
    --show v ++ "\n" ++
    "  movq " ++ loc1 ++ ", %rax\n" ++
    "  movq %rax, " ++ loc2 ++ "\n")

genInstruction cx (Just (VLookup result val)) =
  let loc = snd $ genAccess cx val
      stackOffset = (offset cx) * (-1)
      destination = (show stackOffset) ++ "(%rbp)"
      ncx = updateOffset $ setVariableLoc cx result ("%rbp", stackOffset) in
        (ncx,
        "  movq " ++ loc ++ ", %rax\n" ++
        "  movq %rax, " ++ destination ++ "\n")

genInstruction cx (Just (VArrayStore _ val arrayRef idxRef)) =
  let arr = case arrayRef of
              InstRef s -> lookupVariable cx s
              GlobalRef s -> ".global_" ++ s
              _ -> "bad array store " ++ (show arrayRef)
      idx = snd $ genAccess cx idxRef
      loc = snd $ genAccess cx val in
  (cx,
   "  leaq " ++ arr ++ ", %rax\n" ++
   "  movq " ++ idx ++ ", %rbx\n" ++
   "  leaq (%rax, %rbx, 8), %rbx\n" ++
   "  movq " ++ loc ++ ", %rax\n" ++
   "  movq %rax, (%rbx)\n")

genInstruction cx (Just (VArrayLookup result arrayRef idxRef)) =
  let arr = case arrayRef of
              InstRef s -> lookupVariable cx s
              GlobalRef s -> ".global_" ++ s
              _ -> "bad array lookup " ++ (show arrayRef)
      idx = snd $ genAccess cx idxRef
      stackOffset = (offset cx) * (-1)
      destination = (show stackOffset) ++ "(%rbp)"
      ncx = updateOffset $ setVariableLoc cx result ("%rbp", stackOffset) in
  (ncx,
   "  leaq " ++ arr ++ ", %rax\n" ++
   "  movq " ++ idx ++ ", %rbx\n" ++
   "  movq (%rax, %rbx, 8), %rbx\n" ++
   "  movq %rbx, " ++ destination ++ "\n")

genInstruction cx (Just (VArrayLen result ref)) =
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
  

genInstruction cx (Just (VReturn _ maybeRef)) =
  case maybeRef of
    Just ref -> (cx, "  movq " ++ (snd (genAccess cx ref)) ++ ", %rax\n  leave\n  ret\n")
    Nothing -> (cx, "  leave\n  ret\n")

genInstruction cx (Just (VCondBranch _ cond true false)) =
  let loc = snd $ genAccess cx cond in
    (cx, 
    "  movq " ++ loc ++ ", %rax\n" ++
    "  test %rax, %rax\n" ++
    "  jnz " ++ name cx ++ "_" ++ true ++ "\n" ++
    "  jz " ++ name cx ++ "_" ++ false ++ "\n")

genInstruction cx (Just (VUnreachable _)) =
  (cx, "  # unreachable instruction TODO?\n")

genInstruction cx (Just (VUncondBranch _ dest)) =
  (cx, "  jmp " ++ name cx ++ "_" ++ dest ++ "\n")

genOp :: String -> String -> String
genOp "+" loc  = "  addq "  ++ loc ++ ", %rax\n"
genOp "-" loc  = "  subq "  ++ loc ++ ", %rax\n"
genOp "*" loc  = "  imulq " ++ loc ++ ", %rax\n"
genOp "/" loc  = "  idivq " ++ loc ++ "\n"
genOp "==" loc = "  cmp "   ++ loc ++ ", %rax\n  setz %al\n"
genOp "!=" loc = "  cmp "   ++ loc ++ ", %rax\n  setnz %al\n"
genOp "<"  loc = "  cmp "   ++ loc ++ ", %rax\n  setl %al\n"
genOp "<=" loc = "  cmp "   ++ loc ++ ", %rax\n  setle %al\n"
genOp ">" loc  = "  cmp "   ++ loc ++ ", %rax\n  setg %al\n"
genOp ">=" loc = "  cmp "   ++ loc ++ ", %rax\n  setge %al\n"
genOp "u<"  loc = "  cmp "   ++ loc ++ ", %rax\n  setl %al\n"
genOp "u<=" loc = "  cmp "   ++ loc ++ ", %rax\n  setle %al\n"
genOp "u>" loc  = "  cmp "   ++ loc ++ ", %rax\n  setg %al\n"
genOp "u>=" loc = "  cmp "   ++ loc ++ ", %rax\n  setge %al\n"
genOp "||" loc = "  or "    ++ loc ++ ", %rax\n  cmp %rax, $0\n  setnz %al\n"
genOp "&&" loc = "  and "   ++ loc ++ ", %rax\n  cmp %rax, $0\n  setnz %al\n"

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
    (genConstants cx3)

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
