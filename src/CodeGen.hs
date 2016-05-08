{-# LANGUAGE ScopedTypeVariables #-}

module CodeGen where

import Prelude
import Data.List
import qualified Data.Map as HashMap
import qualified LLIR
import LLIR hiding (blockName)
import Text.Printf

data CGContext = CGContext {
  -- label, constant string
  constStrs :: HashMap.Map String String,
  nextConstStrId :: Int,
  -- global arrays with sizes
  globalArrays :: [(String, Int)]
} deriving(Eq, Show);

newCGContext :: CGContext
newCGContext = CGContext (HashMap.empty) 0 []

getConstStrId :: FxContext -> String -> (FxContext, String)
getConstStrId fcx str =
  let gcx = global fcx
      strs = constStrs gcx
      in case HashMap.lookup str strs of
	Just name -> (fcx, name)
        Nothing ->
          let next = (nextConstStrId gcx)
              id = ".const_str" ++ (show next)
              gcx2 = gcx{
                constStrs= HashMap.insert str id strs,
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

data InstLoc = Register  String
             | Memory    String Int
             | Immediate Int
  deriving(Eq, Show);

data FxContext = FxContext {
  name   :: String,
  global :: CGContext,
  function :: LLIR.VFunction,
  blockName :: String,
  -- variables maps registers to a label/reg + offset
  variables :: HashMap.Map String InstLoc,
  offset :: Int,
  instrs :: [String],
  errors :: [String]
} deriving(Eq, Show);

newFxContext :: String -> CGContext -> LLIR.VFunction -> FxContext
newFxContext name global func = FxContext name global func "entry" HashMap.empty 0 [] []

updateOffsetBy :: FxContext -> Int -> FxContext
updateOffsetBy fcx size = fcx{offset=(offset fcx) + size}

updateOffset :: FxContext -> FxContext
updateOffset fcx = updateOffsetBy fcx 8

locStr :: InstLoc -> String
locStr (Memory place offset) = (show offset) ++ "(" ++ place ++ ")"
locStr (Register place) = place
locStr (Immediate place) = "$" ++ (show place)

getVar :: FxContext -> String -> InstLoc
getVar fxc var = hml (variables fxc) var "getVar"

lookupVariable :: FxContext -> String -> String
lookupVariable fxc var =
  let table = (variables fxc) in
  case head var of
    '$' -> var
    _ -> locStr $ hml table var "lookupVariable"

setVariableLoc :: FxContext -> String -> InstLoc -> FxContext
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

getProlog :: FxContext -> Int -> Int -> String
getProlog cx argsLength localsSize =
  let argRegs = ["%rdi", "%rsi", "%rdx", "%rcx", "%r8", "%r9"]
      argz = ( argRegs ++ (map (\i -> (show $ (i - (length argRegs) + 1) * 8) ++ "(%rbp)") (drop 6 [1..argsLength]) ) ) in
  "  #prolog\n" ++
  "  push %rbp\n" ++
  "  movq %rsp, %rbp\n" ++
  "  subq $" ++ (show localsSize) ++ ", %rsp\n" ++
  -- put register arguments to stack
  ( arrayToLine $ concat $ map (\(x, y) ->
    let fm = x
        to = getRef cx $ ArgRef (y-1) (name cx)
        in
          if fm == to then [] else move x to ) $ zip argz [1..argsLength] )
  ++ "  #/prolog\n"

getEpilog :: String
getEpilog =
  " \n" ++
  "  #epilog\n" ++
  "  movq %rbp, %rsp\n" ++
  "  pop %rbp\n" ++
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

localSize instr =
  case instr of
    VStore _ _ _ -> 0
    VArrayStore _ _ _ _ -> 0
    VReturn _ _ -> 0
    VCondBranch _ _ _ _ -> 0
    VUncondBranch _ _ -> 0
    VUnreachable _ -> 0
    VAllocation _ _ (Just x) -> (x + 1) * 8
    VAllocation _ _ Nothing -> 8
    _ -> 8

calculateLocalsSize instrs =
  foldl (+) 0 (map localSize instrs)

genFunction :: CGContext -> LLIR.VFunction -> (CGContext, String)
genFunction cx f =
  let argsLength = length $ LLIR.arguments f
      instrs = concat $ map (\x -> snd $ getBlockInstrs f $ hml (LLIR.blocks f) x "getblocks" ) (LLIR.blockOrder f)
      nzInst = (filter (\x -> 0 /= (localSize x)) instrs)
      localsSize = (8*argsLength) + (calculateLocalsSize nzInst)
      ncx0 = foldl (\cx (idx, arg) ->
                let sz = 8 in
                    if idx <= 6 then
                      updateOffsetBy ( setVariableLoc cx
                                    (LLIR.functionName f ++ "@" ++ show (idx - 1))
                                    (Memory "%rbp" $ ( -((offset cx) + sz)  ) ) ) sz
                    else setVariableLoc cx
                                  (LLIR.functionName f ++ "@" ++ show (idx - 1))
                                  (Memory "%rbp" $ ( (idx - 6) + 2 ) * 6 ) )
                   (newFxContext (LLIR.functionName f) cx f)
                   (zip [1..argsLength] $ LLIR.arguments f)
      ncx1 = foldl (\cx arg ->
                let sz = localSize arg in
		
                      updateOffsetBy ( setVariableLoc cx
                                   (LLIR.getName arg)
                                   (Memory "%rbp" $ ( -((offset cx) + sz)  ) ) ) sz )
                  ncx0
                  nzInst
      (ncx2, blocksStr) = foldl
                   (\(cx, s) name ->
                     let block = hml (LLIR.blocks f) name "getFunc-Block"
                         (ncx, str) = genBlock cx{blockName=name} block name f in
                     (ncx, s ++ str))
                   (ncx1, "") $ LLIR.blockOrder f
      prolog = getProlog ncx2 argsLength (closestMultipleOf16 localsSize)
      strRes = "\n" ++ LLIR.functionName f ++ ":\n" ++ prolog ++ blocksStr ++ getEpilog in
      --if (LLIR.getName f) /= "sum" then
        (global ncx2, strRes)
      --else
        --error ( printf "localsSize:%s\n\nncx0:%s\n\nncx1:%s\n\nncx2:%s\n\n%s" (show localsSize) (show ncx0) (show ncx1) (show ncx2) (show (map (\y -> getRef ncx2 $ ArgRef (y-1) (name ncx2) ) [1..argsLength] ) ) )

getBlockInstrs :: LLIR.VFunction -> LLIR.VBlock -> (Bool,[LLIR.VInstruction])
getBlockInstrs f block =
  let instructions :: [String] = LLIR.blockInstructions block
      term = last instructions
      termI = instCastU f $ InstRef term
      instructions2 :: [String] = case termI of 
        VCondBranch _ _ _ _ -> filter (\x -> case do
            inst <- instCast f $ InstRef x
            _ <- case inst of
              VBinOp _ op _ _ -> if elem op ["<","<=",">",">=","u<","u<=","u>","u>=","==","!="] then Just True else Nothing
              _ -> Nothing
            uses <- return $ getUses inst f
            _ <- if 1 == length uses then Just True else Nothing
            if ( getName $ getUseInstr2 f (uses !! 0) ) == term then Just True else Nothing
          of
            Just _ -> False
            _ -> True
          ) instructions
        _ -> instructions
      instrs = map (\x -> instCastU f $ InstRef x) instructions2
      in ( (length instructions)/=(length instructions2), instrs )

makeOneReg :: String -> String -> String -> (String,String,[String])
makeOneReg a b c = if (isMemoryS a) && (isMemoryS b) then (c,b,move a c) else (a,b,[])

swapBinop :: String -> String
swapBinop a
  | a == "==" = "=="
  | a == "!=" = "!="
  | a == ">" = "<"
  | a == ">=" = "<="
  | a == "<" = ">"
  | a == "<=" = ">="
  | a == "u>" = "u<"
  | a == "u>=" = "<u="
  | a == "u<" = "u>"
  | a == "u<=" = "u>="

genBlock :: FxContext -> LLIR.VBlock -> String -> LLIR.VFunction -> (FxContext, String)
genBlock cx block name f =
  let instructions = LLIR.blockInstructions block
      term = last instructions
      (fastTerm, instructions2) = getBlockInstrs f block
      instructions3 = if fastTerm then take ((length instructions2)-1) instructions2 else instructions2
      (ncx, s) = foldl (\(cx, acc) instruction ->
          let (ncx, str) = genInstruction cx instruction in
                (ncx, acc ++ ( "# " ++ (show instruction) ++ "\n" ) ++ str))
          (cx, "")
          instructions3
      blockName = LLIR.blockFunctionName block ++ "_" ++ LLIR.blockName block
      setupGlobals = if blockName /= "main_entry" then "" else genSetupGlobals (global cx)
      fastEnd = if not fastTerm then "" else let
        termI = instCastU f $ InstRef term
        (_,cond,tB, fB) = case termI of
          VCondBranch a c t f -> (a, c, t, f)
          _ -> error "badcond"
        cmpI  = instCastU f $ cond
        (_,op0,a1,a2) = case cmpI of
          VBinOp a b c d -> (a,b,c,d)
          _ -> error "badbin"
        r1 :: String = getRef cx a1
        r2 :: String = getRef cx a2
      	phis = (LLIR.getPHIs (function cx) tB) ++ (LLIR.getPHIs (function cx) fB)
      	cors = concat $ map (\(VPHINode pname hm) ->
            let var = locStr $ getVar cx pname
                str :: String = CodeGen.blockName cx
                val = getRef cx (hml hm str "genBlock")
                in move val var
          ) phis
        (x1,x2,mvs) = makeOneReg r1 r2 "%rax"
        (y1,y2,op) = if isImmediateS x1 then (x2, x1, swapBinop op0) else (x1, x2, op0)
        mp = HashMap.fromList [("==","je"),("!=","jne"),("u<","jb"),("u<=","jbe"),("u>","ja"),("u>","jae"),("<","jl"),("<=","jle"),(">","jg"),(">=","jge")]
        insts = ["# " ++ (show cmpI), "# "++ (show termI), printf "cmpq %s, %s" y2 y1, printf "%s %s_%s" (hml mp op "reverse cmp") (CodeGen.name cx) tB, printf "jmp %s_%s" (CodeGen.name cx) fB]
        in arrayToLine $ cors ++ mvs ++ insts
      in (ncx, blockName ++ ":\n" ++ setupGlobals ++ s ++ fastEnd)

genSetupGlobals cx =
  concat $ map (\(name, size) -> arrayToLine $ move ("$" ++ (show size)) name ) $ globalArrays cx

arrayToLine :: [String] -> String
arrayToLine ar = concat $ map (\x -> "  " ++ x ++ "\n") ar

genUOp :: String -> String -> String
genUOp op reg = case op of
  "-" -> printf "negq %s" reg
  "!" -> printf "xorq $1, %s" reg

isMemory :: InstLoc -> Bool
isMemory (Memory _ _ ) = True
isMemory _ = False

isMemoryS :: String -> Bool
isMemoryS s = ( (last s) == ')' ) || ( (take (length ".global") s) == ".global" )

isRegisterS :: String -> Bool
isRegisterS s = (head s) == '%'

isImmediateS :: String -> Bool
isImmediateS s = (head s) == '$'

move :: String -> String -> [String]
move loc1 loc2 =
  if loc1 == loc2 then [] else
  if (isMemoryS loc1) && (isMemoryS loc2)
    then [printf "movq %s, %s" loc1 "%rax", printf "movq %s, %s" "%rax" loc2 ]
    else [printf "movq %s, %s" loc1 loc2]

makeReg :: String -> String -> (String,[String])
makeReg reg tmp = if isRegisterS reg then (reg, []) else (tmp, move reg tmp)

genInstruction cx (VAllocation result tp size) =
  let s = case size of
                 Just i -> i
                 Nothing -> 0
      -- reserve first 8-byte number to store the length of the array
      var = getVar cx result
      -- in case of an array, skip first byte
      stackOffset = case var of
        Memory loc off -> off
        _ -> error "badd var for allocation"
      destination = (show stackOffset) ++ "(%rbp)"

      ncx :: FxContext = case size of
        -- if array, store location of its length lookup at the head
        Just i ->
		let cx2 = setVariableLoc cx (result) (Memory "%rbp" $ stackOffset + 8)
                    cx3 = setVariableLoc cx2 (result ++ "@len" ) (Memory "%rbp" $ stackOffset)
                    in cx3
        Nothing -> cx
      ncx2 = ncx
      zeroingCode = case size of
        Just sz ->
          "  # bzero\n" ++
          "  cld\n" ++
          "  leaq " ++ (locStr $ getVar ncx2 result ) ++ ", %rdi\n" ++
          "  movq $" ++ (show sz) ++ ", %rcx\n" ++
          "  movq $0, %rax\n" ++
          "  rep stosq\n" ++
          "  # /bzero\n"
        Nothing -> ""
      in (ncx2, (if s > 0 then arrayToLine ( move ("$" ++ (show s)) destination ) else "") ++ zeroingCode )

genInstruction cx (VUnOp result op val) =
  let loc =  getRef cx val
      var  = getVar cx result
      vloc = locStr var
      oploc = case var of
        Register _ -> vloc
        _ -> "%rax"
      insts = move loc oploc ++ [ genUOp op oploc ] ++ move oploc vloc
      in (cx, arrayToLine insts)

genInstruction cx (VPHINode _ _) = (cx, "")

genInstruction cx (VBinOp result op val1 val2) =
    let loc1 = getRef cx val1
        loc2 = getRef cx val2
        var  = getVar cx result
        vloc = locStr var
        oploc = case var of
          Register _ -> vloc
          _ -> "%rax"
        cp = move oploc vloc
        in (cx,
          (
            if ((op == "/") || (op == "%")) then
              -- in A/B require A in rax, rdx empty
              let (nreg, inst0) = if isImmediateS loc2 then makeReg loc2 "%rbx" else (loc2,[])
                  (instA, out) :: ([String], String) = genOpB op loc1 nreg in
                  (arrayToLine ( inst0 ++ instA ++ (move out vloc) ) )
            else
              (arrayToLine $ move loc1 oploc)
              ++ ( arrayToLine $ genOp op loc2 oploc ) ++ ( arrayToLine cp )
          ) )

genInstruction cx (VMethodCall name isCallout fname args) =
  -- push arguments
  let (ncx, nargs) = foldl (\(cx, acc) arg ->
                              let (ncx, narg) = genArg cx arg in
                                    (ncx, acc ++ [narg]))
                           (cx, []) args
      precall = getPreCall nargs
      cleanRax = "  movq $0, %rax\n"
      postcall = getPostCall $ length args
      destination = locStr $ getVar cx name
      (ncx2, exitMessage) = if fname == "exit" && isCallout then genExitMessage cx (args !! 0) else (ncx, "") in
        (ncx2, exitMessage ++ precall ++ cleanRax ++ "  callq " ++ fname ++ "\n  movq %rax, " ++ destination ++ "\n" ++ postcall)

genInstruction cx (VStore _ val var) =
  let loc1 = getRef cx val
      loc2 = getRef cx var
      in (cx, arrayToLine $ move loc1 loc2)

genInstruction cx (VLookup result val) =
  let loc = getRef cx val
      destination = locStr $ getVar cx result
      in (cx, arrayToLine $ move loc destination)

genInstruction cx (VArrayStore _ val arrayRef idxRef) =
  let arr = case arrayRef of
              InstRef s -> lookupVariable cx s
              GlobalRef s -> ".global_" ++ s
              _ -> "bad array store " ++ (show arrayRef)
      isGlobal = case arrayRef of
        GlobalRef _ -> True
        _ -> False
      idx = getRef cx idxRef
      loc = getRef cx val in
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
      idx = getRef cx idxRef
      destination = locStr $ getVar cx result
      in (cx,
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
         destination = locStr $ getVar cx result
        in (cx,
   "  movq " ++ access ++ ", %rax\n" ++
   "  movq %rax, " ++ destination ++ "\n")


genInstruction cx (VReturn _ maybeRef) =
  case maybeRef of
    Just ref -> (cx, "  movq " ++ (snd (genAccess cx ref)) ++ ", %rax\n" ++ "  movq %rbp, %rsp\n  pop %rbp\n  ret\n" )
    Nothing -> if name cx == "main" then (cx,  "  movq %rbp, %rsp\n  xorq %rax, %rax\n  pop %rbp\n  ret\n" ) else (cx,  "  movq %rbp, %rsp\n  pop %rbp\n  ret\n" )

-- TODO MOVE CMP / etc
genInstruction cx (VCondBranch result cond true false) =
  let loc :: String = getRef cx cond
      phis = (LLIR.getPHIs (function cx) true) ++ (LLIR.getPHIs (function cx) false)
      cors = concat $ map (\(VPHINode pname hm) ->
            let var = locStr $ getVar cx pname
                val = getRef cx (hml hm (blockName cx) "condBr" )
                in move val var
          ) phis
      (reg, inst1) :: (String, [String]) = makeReg loc "%rax"
      insts = inst1 ++ [printf "testq %s, %s" reg reg, printf "jnz %s_%s" (name cx) true, printf "jz %s_%s" (name cx) false]
      in ( cx, arrayToLine $ cors ++ insts )

genInstruction cx (VUnreachable _) =
  (cx, "  # unreachable instruction\n")

genInstruction cx (VUncondBranch result dest) =
  let phis = LLIR.getPHIs (function cx) dest
      cors :: [String] = concat $ map (\(VPHINode pname hm) ->
          let var = locStr $ getVar cx pname
              val = getRef cx (hml hm (blockName cx) "uncondBr")
              in move val var
        ) phis
      in (cx, arrayToLine $ cors ++ [printf "jmp %s_%s" (name cx) dest ])

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
genOpB :: String -> String -> String -> ([String], String)
genOpB "/" arg1 arg2 = ((move arg1 "%rax") ++ ["cqto", printf "idivq %s" arg2], "%rax")
genOpB "%" arg1 arg2 = ((move arg1 "%rax") ++ ["cqto", printf "idivq %s" arg2], "%rdx")

genArg :: FxContext -> ValueRef -> (FxContext, (String, Int))
genArg cx x =
  let (ncx, asm) = genAccess cx x in
  (ncx, (asm, 8))

getRef :: FxContext -> ValueRef -> String
getRef cx (InstRef ref) = lookupVariable cx ref

getRef cx (ConstInt i)  = "$" ++ (show i)

getRef cx (ConstString s) =
  let (ncx, id) = getConstStrId cx s in
    "$" ++ id

getRef cx (ConstBool b) = "$" ++ (if b then "1" else "0")

getRef cx (ArgRef i funcName) =
  if i < 6 then lookupVariable cx $ funcName ++ "@" ++ (show i) else (show $ 16 + 8 * (i - 6)) ++ "(%rbp)"

getRef cx (GlobalRef name) =
  ".global_" ++ name

genAccess :: FxContext -> ValueRef -> (FxContext, String)
genAccess cx (InstRef ref) =
  (cx, lookupVariable cx ref)

genAccess cx (FunctionRef i) =
  (cx, "$" ++ i)

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
  HashMap.foldWithKey (\cnst label str->
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
