{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
module OPT where

import Data.List
import Data.Maybe
import qualified Data.Map as HashMap
import qualified Data.Set as Set
import qualified LLIR
import LLIR
import Text.Printf
import Data.Word
import Debug.Trace

-- NEED TO TO MEM2REG AS REQUISITE
mem2reg :: Builder -> Builder
mem2reg builder =
  let pm = pmod builder
      fxs :: HashMap.Map String VFunction = functions pm
      (pm2, dbg) :: (PModule, [IO()]) = HashMap.fold (
        \fx (newPm, dbgs) -> let (retPm, retDbgs) = mem2reg_function newPm fx
            in (retPm, dbgs ++ retDbgs)) (pm, []) fxs
      in builder{pmod=pm2,debugs=( (debugs builder) ++ dbg ) }

gmem2reg :: Builder -> Builder
gmem2reg builder =
  let pm = pmod builder
      fxs :: HashMap.Map String VFunction = functions pm
      (pm2, dbg) :: (PModule, [IO()]) = HashMap.fold (
        \fx (newPm, dbgs) -> let (retPm, retDbgs) = gmem2reg_function newPm fx
            in (retPm, dbgs ++ retDbgs)) (pm, []) fxs
      in builder{pmod=pm2,debugs=( (debugs builder) ++ dbg ) }

cAssert :: Builder -> Builder
cAssert builder =
    let pm = pmod builder
        fxs :: HashMap.Map String VFunction = functions pm
        fxs2 = HashMap.map cAssert_function fxs
        pm2 = pm{functions=fxs2}
        in builder{pmod=pm2}

getReachable :: VFunction -> String -> Set.Set String -> Set.Set String
getReachable func str s1 =
  if str `Set.member` s1 then s1 else foldl (\acc x -> getReachable func x acc) (s1 `Set.union` (Set.singleton str) ) ( blockSuccessors $ (HashMap.!) (blocks func) str )

cAssert_function :: VFunction -> VFunction
cAssert_function func =
    let blockDoms = invertMap $ blockDominators func
    in foldl
            (\accf blockName ->
                let block :: VBlock = hml (blocks func) blockName "cassert1"
                    blockInstrs :: [String] = blockInstructions block
                    lastInstrN :: String = last blockInstrs
                    lastInstr :: VInstruction = hml (functionInstructions accf) lastInstrN "cassert5"
                    in case lastInstr of
                        (VCondBranch name cond tblockN fblockN) ->
                          case cond of
                            InstRef a ->
                              let inst = hml (functionInstructions accf) a "cassert2"
                                  trueDomBlocks = getReachable func tblockN Set.empty
                                  falseDomBlocks = getReachable func fblockN Set.empty
                                  tDomBlocks :: [String] = Set.toList $ Set.difference trueDomBlocks (falseDomBlocks `Set.union` (Set.singleton blockName))
                                  fDomBlocks :: [String] = Set.toList $ Set.difference falseDomBlocks (trueDomBlocks `Set.union` (Set.singleton blockName))
                                  r1 :: VFunction = replaceBlockUses accf inst tDomBlocks (ConstBool True)
                                  r2 :: VFunction = replaceBlockUses r1 inst fDomBlocks (ConstBool False)
                                  errS :: String = printf "tdom:%s\nfdom:%s\ninst:%s\nF:%s\nafter:%s\n" (show tDomBlocks) (show fDomBlocks) (show inst) (show accf) (show r2)
                                  in --if (getName inst) == "%21" then error errS else
                                     r2
                            _ -> accf
                        _ -> accf) func (blockOrder func)


isTPure :: VInstruction -> Bool
isTPure (VUnOp _ _ _ ) = True
isTPure (VBinOp _ _ _ _ ) = True
isTPure (VStore _ _ _) = False
isTPure (VLookup _ _) = False
isTPure (VAllocation _ _ _) = False
isTPure (VArrayStore _ _ _ _) = False
isTPure (VArrayLookup _ _ _) = False
isTPure (VArrayLen _ _) = True
isTPure (VMethodCall _ _ _ _) = False
isTPure (VReturn _ _) = False
isTPure (VCondBranch _ _ _ _) = False
isTPure (VUncondBranch _ _) = False
isTPure (VUnreachable _ ) = False
isTPure (VPHINode _ _) = False

loopOpts :: Builder -> Builder
loopOpts builder =
  let pm = pmod builder
      fxs :: HashMap.Map String VFunction = functions pm
      (pm2,dbgs) = HashMap.fold (\y (x,dbgs) -> let (x2,dbgs2) = loops_function x y in (x2,dbgs ++ dbgs2) ) (pm,[]) fxs
      in builder{pmod=pm2,debugs=(debugs builder) ++ dbgs }

ploopOpts :: Builder -> Builder
ploopOpts builder =
  let pm = pmod builder
      fxs :: HashMap.Map String VFunction = functions pm
      (pm2,dbgs) = HashMap.fold (\y (x,dbgs) -> let (x2,dbgs2) = ploops_function x y in (x2,dbgs ++ dbgs2) ) (pm,[]) fxs
      in builder{pmod=pm2,debugs=(debugs builder) ++ dbgs }

data LoopInfo = LoopInfo {-loops-}[LoopInfo] {-not loops-}[String]

getLoop func domTree headerN blockNames =
  let inLoop :: [String] = filter (\x -> ( Set.member (x) ((HashMap.!) domTree headerN )) && ( Set.member headerN ((HashMap.!) domTree x )) ) blockNames
      l2 = filter (\x -> ( not $ elem x inLoop) && (all (\x -> elem x inLoop) (blockPredecessors $ hml (blocks func) x "gl" ) ) && (isUnreachable func x) ) blockNames
      in inLoop ++ l2

data Loop = Loop {
  funcName :: String,
  header :: String,
  subLoops :: [Loop],
  loopBlocks :: [String]
} deriving (Eq, Show);

getEntranceBlocks :: VFunction -> Loop -> [String]
getEntranceBlocks func loop = filter (\y -> not $ elem y (loopBlocks loop) ) ( blockPredecessors (hml (blocks func) (header loop)  "eb") )

getExitBlocks :: VFunction -> Loop -> [(String,String)]
getExitBlocks func loop =
  let lb = loopBlocks loop
      in concat $ map (\x -> filter (\(y,x) -> not $ elem y (loopBlocks loop) ) $ map (\z -> (z,x) ) $ blockSuccessors (hml (blocks func) x "eb") ) lb

getLoops :: VFunction -> [String] -> [Loop]
getLoops func blockNames =
  let domTree :: HashMap.Map String (Set.Set String) = reachable blockNames func
      loopHeaders ::[String] = filter (\b ->
        let bpu :: [String] = ( blockPredecessors $ (HashMap.!) (blocks func) b )
            bp :: [String] = filter (\x -> elem x blockNames) bpu
            in (length bp > 0)
               && ( Set.member b ((HashMap.!) domTree b ) )
               && not ( all (\x -> if HashMap.member x domTree then Set.member b ((HashMap.!) domTree x ) else False ) bpu )
        ) blockNames
      loops :: [(String,[String])] = map (\b -> (b, getLoop func domTree b blockNames)) loopHeaders
      loopR :: [Loop] = map (\(head,bks) -> Loop (getName func) head (getLoops func $ delete head bks) bks) loops
      in --if blockNames /= ( blockOrder func) then error $ printf "bks:%s\n DT:%s\n" (show blockNames) (show domTree) else
         loopR

addToDepth :: [Loop] -> Int -> String -> Int
addToDepth loops depth instrBlock =
    let nextLoop :: [Loop] = filter (\loop -> elem instrBlock (loopBlocks loop)) loops
        in if length nextLoop == 0
            then depth
            else addToDepth (subLoops (nextLoop !! 0)) (depth + 1) instrBlock

getInstructionLoopDepth :: VFunction -> VInstruction -> Int
getInstructionLoopDepth func instr =
    let loops :: [Loop] = getLoops func (blockOrder func)
        funcBlocks :: [VBlock] = map (\blockName -> (HashMap.!) (blocks func) blockName) (blockOrder func)
        instrBlock :: VBlock = (filter (\block -> elem (getName instr) (blockInstructions block)) funcBlocks) !! 0
        in addToDepth loops 0 (blockName instrBlock)

licm :: PModule -> Loop -> (Bool, PModule, [IO()] )
licm pm loop =
  let func = hml (functions pm) (funcName loop) "licmL"
      loopInsts = map (\x -> hml (functionInstructions func) x "licm2" ) (concat $ map (\bn -> blockInstructions $ hml (blocks func) bn "par2") (loopBlocks loop) )
      movable :: [VInstruction] = filter (\x -> (isTPure x) && all (\y -> case getUseValue func y of Just (InstRef f) -> (not $ elem f (map getName loopInsts) );_ -> True ) (getUsed x) ) loopInsts
      fixed :: VFunction = foldl (\f inst ->
                                        let bkN :: String = getInstructionParent f inst
                                            bk = hml (blocks f) bkN "licm"
                                            bk2 = bk{blockInstructions = delete (getName inst) (blockInstructions bk) }
                                            in f{blocks=HashMap.insert (getName bk2) bk2 (blocks f)}) func movable
      enters :: [String] = getEntranceBlocks func loop
      enterB :: [VBlock] = map (\x -> hml (blocks fixed) x ".2" ) enters
      ebi = blockInstructions ( enterB !! 0 )
      enterB2 = (enterB !! 0){blockInstructions = (take ((length ebi)-1) ebi) ++ (map getName movable) ++ [ebi !! ((length ebi) - 1)]}
      exits :: [(String,String)] = getExitBlocks func loop
      func2 = fixed{blocks=HashMap.insert (getName enterB2) enterB2 (blocks fixed)}
      in if (length movable) == 0 then (False, pm, []) else --[printf "MI!!! in func %s saw loop with head :%s\nenters:%s exits:%s\nloop:%s\n\n\n" (funcName loop) (header loop) (show enters) (show exits) (show $ loopBlocks loop)]) else
         if (length enterB) /= 1 then (False, pm, []) else --[printf "MI!!! in func %s saw loop with head :%s\nenters:%s exits:%s\nloop:%s\n\n\n" (funcName loop) (header loop) (show enters) (show exits) (show $ loopBlocks loop)]) else
         (True, pm{functions=HashMap.insert (getName func2) func2 (functions pm)}, []) -- [printf "movable:%s\n" (show movable)] )


parallelize :: PModule -> Loop -> (Bool, PModule, [IO()] )
parallelize pm loop =
  let func = hml (functions pm) (funcName loop) "parL"
      loopInsts :: [VInstruction] = map (\x -> hml (functionInstructions func) x "par" ) (concat $ map (\bn -> blockInstructions $ hml (blocks func) bn "par2") (loopBlocks loop) )
      methodInsts :: [VInstruction] = filter (\inst -> case inst of VMethodCall _ _ n _ -> not ((n=="exit")||(n=="printf")); _ -> False ) loopInsts
      readInsts :: [(ValueRef,Maybe ValueRef)] = catMaybes $ map (\inst -> case inst of VStore _ _ v -> Just (v,Nothing); VArrayStore _ _ v idx-> Just (v,Just idx); _ -> Nothing) loopInsts
      writeInsts ::[(ValueRef,Maybe ValueRef)] = catMaybes $ map (\inst -> case inst of VLookup _ v -> Just (v,Nothing); VArrayLookup _ v idx -> Just (v,Just idx); _ -> Nothing) loopInsts
      phis :: [VInstruction] = getPHIs func (header loop)
      enters :: [String] = getEntranceBlocks func loop
      exits :: [(String,String)] = getExitBlocks func loop
      uses :: [ValueRef] = catMaybes $ concat $ map (\x -> map (\y -> getUseValue func y) (getUsed x) ) loopInsts
      needs :: [String] = catMaybes $ map (\x -> case x of InstRef y -> if elem y (map getName loopInsts) then Nothing else Just y; _ -> Nothing) uses
      in if (length methodInsts) /= 0 then (False, pm, [printf "MI!!! in func %s saw loop with head :%s\nenters:%s exits:%s\nloop:%s\n\n\n" (funcName loop) (header loop) (show enters) (show exits) (show $ loopBlocks loop)]) else
         if any (\(v,idx) -> let ft = filter (\(v2,ix) -> if v /= v2 then False else (ix == Nothing) || (ix/=idx) {- || not linear in var -} ) writeInsts in (length ft) > 0  ) readInsts then (False,pm,[printf "WI!!! in func %s saw loop with head :%s\nenters:%s exits:%s\nwrite:%s\nread:%s\nloop:%s\n\n\n" (funcName loop) (header loop) (show enters) (show exits) (show writeInsts) (show readInsts) (show $ loopBlocks loop)]) else -- TODO ENSURE INDEXED
         if (length phis) /= 1 then (False, pm, [printf "LP!!! in func %s saw loop with head :%s\nenters:%s exits:%s\nloop:%s\n\n\n" (funcName loop) (header loop) (show enters) (show exits) (show $ loopBlocks loop)]) else
         if (length enters) /= 1 then (False, pm, [printf "ET!!! in func %s saw loop with head :%s\nenters:%s exits:%s\nloop:%s\n\n\n" (funcName loop) (header loop) (show enters) (show exits) (show $ loopBlocks loop)]) else
         if (length exits) /= 1 then (False, pm, [printf "EX!!! in func %s saw loop with head :%s\nenters:%s exits:%s\nloop:%s\n\n\n" (funcName loop) (header loop) (show enters) (show exits) (show $ loopBlocks loop)]) else
         if (enters !! 0) /= "entry" then (False, pm, [printf "bad name for entrance to parallel region %s\n" (enters !! 0)]) else
         let insts = HashMap.filterWithKey (\k _ -> any (\x -> elem k $ blockInstructions (hml (blocks func) x "pl") ) (loopBlocks loop) ) (functionInstructions func)
             bks = HashMap.filterWithKey (\k _ -> elem k (loopBlocks loop) ) (blocks func)
             fn = (getName func) ++ ".p"
             (nm,pm2) = createID pm
             (nm2,pm3) = createID pm2
             (nm3,pm4) = createID pm3
             (nm4,pm5) = createID pm4
             (nm5,pm6) = createID pm5
             (nm6,pm7) = createID pm6
             (nm7,pm8) = createID pm7
             (nm8,pm9) = createID pm8
             (nm9,pm10) = createID pm9
             (nm10,pm11) = createID pm10
             (beg0,fpm) = foldl (\(beg0,pm) inst ->
                let (nm,pm1) = createID pm
                    (nm2,pm2) = createID pm1
                    bld = Builder pm2 (LLIR.Context (getName func) "entry") []
                    ty = getType bld (InstRef inst)
                    gn = "glob_" ++ (tail inst)
                    pm3 = pm2{globals=HashMap.insert gn (ty,Nothing) (globals pm1)}
                    in (beg0 ++ [((nm,nm2),(gn,inst))],pm3) ) ([],pm11) needs
             beg = map ( fst . fst) beg0
             phi = phis !! 0
             lower = case phi of VPHINode n mp -> (HashMap.!) mp ( enters !! 0 )
             cmpName :: String = case branchI of VCondBranch _ cond _ _ -> case cond of InstRef ref -> ref
             cmp :: VInstruction = (HashMap.!) (functionInstructions func) cmpName
             upper :: ValueRef = case cmp of VBinOp _ _ _ a -> a
             cmper :: ValueRef = case cmp of VBinOp _ _ a _ -> a

             bks2 = HashMap.insert "entry" (VBlock (getName newF) "entry" (beg++[nm3, nm4, nm5, nm6, nm7, nm8, nm9, nm10,nm]) [] [header loop]) bks
             bks3 = HashMap.insert (fst $ exits !! 0) (VBlock (getName newF) (fst $ exits !! 0) [nm2] [snd $ exits !! 0] []) bks2
             eb = hml bks (snd $ exits !! 0) "pl"
             ebi = blockInstructions eb
             branchI :: VInstruction = (HashMap.!) (functionInstructions func) ( ebi !! ((length ebi) - 1) )
             cmpIdx :: Int = case elemIndex cmpName ebi of Just a -> a
             bks4 = HashMap.insert (snd $ exits !! 0) eb{blockInstructions=(take cmpIdx ebi) ++ [nm3, nm4] ++ (drop cmpIdx ebi)} bks3
             insts2 = HashMap.insert nm (VUncondBranch nm (header loop)) insts
             insts3 = HashMap.insert nm2 (VReturn nm2 Nothing) insts2

             insts4 = HashMap.insert nm3 (VBinOp nm3 "-" upper lower ) insts3

             insts5 = HashMap.insert nm4 (VBinOp nm4 "+" (ArgRef 0 fn ) (ConstInt 1) ) insts4
             insts6 = HashMap.insert nm5 (VBinOp nm5 "*" (ArgRef 0 fn ) (InstRef nm3) ) insts5
             insts7 = HashMap.insert nm6 (VBinOp nm6 "*" (InstRef nm4) (InstRef nm3) ) insts6
             insts8 = HashMap.insert nm7 (VBinOp nm7 "/" (InstRef nm5) (ConstInt 8) ) insts7
             insts9 = HashMap.insert nm8 (VBinOp nm8 "/" (InstRef nm6) (ConstInt 8) ) insts8
             insts10 = HashMap.insert nm9 (VBinOp nm9 "+" (InstRef nm7) lower ) insts9
             insts11 = HashMap.insert nm10 (VBinOp nm10 "+" (InstRef nm8) lower ) insts10

             insts12 = HashMap.insert cmpName (VBinOp cmpName "<" cmper (InstRef nm10) ) insts11
             insts13 = HashMap.insert (getName phi) (VPHINode (getName phi) (HashMap.insert "entry" (InstRef nm9) $ HashMap.delete (enters !! 0) (case phi of (VPHINode _ mp) -> mp)) ) insts12
             finsts = foldl ( \insts ((nm,nm2),(gn,inst)) -> HashMap.insert nm (VLookup nm (GlobalRef gn)) insts ) insts13 beg0
--             insts6 = HashMap.insert vr ( case cmp of VBinOp a b c d -> (VBinOp d a b (InstRef nm4) ) ) insts5
             bks5 = HashMap.map (\x -> x{blockFunctionName=fn}) bks4
             newF0 = VFunction fn LLIR.TVoid [LLIR.TInt] finsts bks5 (["entry"] ++ (loopBlocks loop) ++ [(fst $ exits !! 0)])
             newF = foldl ( \f ((nm,nm2),(gn,inst)) -> replaceAllUsesValRef f (InstRef inst) (InstRef nm) ) newF0 beg0
             np = fpm{functions=HashMap.insert (getName newF) newF (functions fpm)}
             (mn,np2) = createID np
             (mn2,np3) = createID np2
             (mn3,np4) = createID np3
             toDel = delete (snd $ exits !! 0) (loopBlocks loop)

             nc = VBlock {blockFunctionName=getName func, blockName=(snd $ exits !! 0),
                          blockInstructions=(map (snd . fst) beg0) ++ [mn,mn2,mn3],
                          blockPredecessors=[enters!!0],
                          blockSuccessors=[snd $ exits !! 0]}
             ins = (functionInstructions func)
             ins2 = HashMap.filterWithKey (\k _ -> not $ HashMap.member k insts13 ) ins
             ins3 = HashMap.insert mn (VMethodCall mn True "set_num_threads" [(ConstInt 8)] ) ins2
             ins4 = HashMap.insert mn2 (VMethodCall mn2 True "create_and_run_threads" [(FunctionRef (getName newF))] ) ins3
             ins5 = HashMap.insert mn3 (VUncondBranch mn3 (fst $ exits !! 0)) ins4
             enterB = (HashMap.!) (blocks func) (enters !! 0)
             brN = last $ blockInstructions enterB
             ins6 = HashMap.insert brN (case (HashMap.!) ins5 brN of VUncondBranch n _ -> VUncondBranch n (snd $ exits !! 0); VCondBranch n c t f -> if t == (header loop) then VCondBranch n c (snd $ exits !! 0 ) f else VCondBranch n c t (snd $ exits !! 0 ) ) ins5
             fins = foldl ( \insts ((nm,nm2),(gn,inst)) -> HashMap.insert nm2 (VStore nm2 (InstRef inst) (GlobalRef gn)) insts ) ins6 beg0

             f2 = func{blockOrder = filter (\x -> not $ elem x toDel) (blockOrder func), functionInstructions=fins, blocks=HashMap.insert (getName nc) nc (blocks func)}
             np5 = np4{functions=HashMap.insert (getName f2) f2 (functions np4)}
             in (True, np5, [printf "in func %s saw loop with head :%s\nenters:%s exits:%s\nloop:%s\n\nneeds:%s\nnewF:%s\n\n\n" (funcName loop) (header loop) (show enters) (show exits) (show $ loopBlocks loop) (show needs) (show np5)] )


runAllLoopsP :: PModule -> Loop -> (Bool, PModule, [IO()] )
runAllLoopsP pm loop=
  let subs@(changed, pm2, dbg) = parallelize pm loop
      in if changed then subs else
        let s3@(c2,pm3,dbg2) = foldl (\o@(c,f,dbg) lp -> if c then o else let (c2,f2,dbg2) = runAllLoopsP f lp in (c2,f2,dbg++dbg2) ) (False, pm,[]) (subLoops loop)
            in if c2 then (c2,pm3,dbg++dbg2) else
               (c2,pm,dbg++dbg2)

ploops_function :: PModule -> VFunction -> (PModule, [IO()])
ploops_function pm func =
  let loops = getLoops func (blockOrder func)
      (changed,pm2,dbgs) = foldl (\o@(c,f,dbg) lp-> if c then o else let (c2,f2,dbg2) = runAllLoopsP f lp in (c2,f2,dbg++dbg2) ) (False, pm,[]) loops
      in if changed then
         (pm2,dbgs)
         else (pm,dbgs)

runAllLoops :: PModule -> Loop -> (Bool, PModule, [IO()] )
runAllLoops pm loop=
  let subs@(changed, pm2, dbg) = foldl (\o@(c,f,dbg) lp -> if c then o else let (c2,f2,dbg2) = runAllLoops f lp in (c2,f2,dbg++dbg2) ) (False, pm,[]) (subLoops loop)
      in if changed then subs else
        let s3@(c2,pm3,dbg2) = licm pm loop
            in if c2 then (c2,pm3,dbg++dbg2) else
               (c2,pm,dbg++dbg2)

loops_function :: PModule -> VFunction -> (PModule, [IO()])
loops_function pm func =
  let loops = getLoops func (blockOrder func)
      (changed,pm2,dbgs) = foldl (\o@(c,f,dbg) lp-> if c then o else let (c2,f2,dbg2) = runAllLoops f lp in (c2,f2,dbg++dbg2) ) (False, pm,[]) loops
      in if changed then
         let (pm3,d1) = loops_function pm2 (hml (functions pm) (getName func) "lf") in (pm3, dbgs ++ d1)
         else (pm2,dbgs)


cfold :: Builder -> Builder
cfold builder =
  let pm = pmod builder
      fxs :: HashMap.Map String VFunction = functions pm
      (cmbs) = HashMap.map (cfold_function (globals pm) ) fxs
      pm2 = pm{functions=HashMap.map fst cmbs}
      in builder{pmod=pm2,debugs=( (debugs builder) ++ (concat $ map snd $ HashMap.elems cmbs) ) }

isConstInt :: ValueRef -> Bool
isConstInt (ConstInt a) = True
isConstInt _ = False

getConstInt :: ValueRef -> Integer
getConstInt (ConstInt a) = a
getConstInt _ = error "not constInt"

isConstBool :: ValueRef -> Bool
isConstBool (ConstBool a) = True
isConstBool _ = False

getConstBool :: ValueRef -> Bool
getConstBool (ConstBool a) = a
getConstBool _ = error "not constBool"

forceInt :: Maybe Int -> Int
forceInt (Just a) = a
forceInt _ = error "cant force nothing from maybe"

cfold_inst :: VInstruction -> VFunction -> (VFunction,Bool)
cfold_inst inst@(VCondBranch name (ConstBool b) tb fb) func =
    let block :: VBlock = getParentBlock inst func
        dest :: String = if b then tb else fb
        ndest :: String = if b then fb else tb
        block2 :: VBlock = block{blockSuccessors=[dest]}
        f0 :: VFunction = updateBlockF block2 func
        f1 :: VFunction = removePredecessor (hml (blocks f0) ndest "cfold rpred") (getName block) f0
        f2 :: VFunction = updateInstructionF (VUncondBranch name dest) f1
        in (f2, True)

{-
cfold_inst :: VInstruction -> VFunction -> (VFunction,Bool)
cfold_inst inst@(VCondBranch name ir@(InstRef ref) tb fb) func =
    let block :: VBlock = getParentBlock inst func
        bins = blockInstructions block
        inst0 = hml (functionInstructions func) (bins !! 0) "cfi"
        in if length bins /= 2 then (func, False) else
           if (getName inst0) /= (ref) then (func, False) else
           if not $ all (\x isUnconditional func x) (blockPredecessors block) then (func, False) else
           let f0 = foldl (\x -> replacePredecessor () ) func (blockPredecessors block)
        dest :: String = if b then tb else fb
        ndest :: String = if b then fb else tb
        block2 :: VBlock = block{blockSuccessors=[dest]}
        f0 :: VFunction = updateBlockF block2 func
        f1 :: VFunction = removePredecessor (hml (blocks f0) ndest "cfold rpred") (getName block) f0
        f2 :: VFunction = updateInstructionF (VUncondBranch name dest) f1
        in (f2, True)
-}

cfold_inst inst@(VUncondBranch name succ) func =
-- if (name /= "%13") && (name /= "%6") then error $ printf "inst:%s\nPRE:%s\nPOST:%s" (show inst) (show func) (succ ++ "|" ++ (getName $ getParentBlock inst func) ) else
    let post = hml (blocks func) succ $ printf "cfold rpred\n %s\n" (show func)
        in if 1 /= (length $ blockPredecessors post) then (func, False)
        else let
          block :: VBlock = getParentBlock inst func
          bname = getName block
          in if succ == bname then (deleteBlock block func, True) else
          let pi = blockInstructions block
              block2 :: VBlock = block{blockSuccessors=(blockSuccessors post), blockInstructions=(take ((length pi)-1) pi) ++ (blockInstructions post)}
              f0 :: VFunction = updateBlockF block2 func
              f1 :: VFunction = deleteInstruction (hml (functionInstructions f0) (last pi) "upd") f0
              f2 :: VFunction = foldl (\f bn->
                 let b = hml (blocks f) bn "cfold bfix"
                     b2 = b{blockPredecessors=(delete succ (blockPredecessors b)) ++ [bname]}
                     phis = getPHIs f bn
                     f2 = f{blocks=HashMap.insert bn b2 (blocks f)}
                     nf = foldl (\f (VPHINode nam hm) ->
                        let hm2 = HashMap.insert bname (hml hm succ "mergebb") hm
                            hm3 = HashMap.delete succ hm2
                            in updateInstructionF (VPHINode nam hm3 ) f ) f2 phis
                     in nf ) f1 (blockSuccessors post)
              f3 = deleteBlockNI post f2
              in --if (name == "%7") then error $ printf "bs:%s\ninst:%s\nPRE:%s\nPOST:%s" (show $ blockSuccessors post) (show inst) (show func) (show f3) else
                 (f3, True)


cfold_inst phi@(VPHINode n mp) func =
  let vals = HashMap.elems mp
      nphi :: [ValueRef] = filter (\x -> x /= (InstRef $ n) ) vals
      in if all (== head nphi) (tail nphi) then
           (replaceAndRemove (head nphi) func phi,True)
         else
           (func,False)


cfold_inst inst@(VUnOp name op op1) func =
    if (isConstInt op1) then
       let x1 = getConstInt op1
           u1 :: Word64 = fromIntegral x1
           rval = case op of
              "-" -> ConstInt $ -x1
           f1 = replaceAllUses func inst rval
           f2 = deleteInstruction inst f1
           in (f2,True)
    else if (isConstBool op1) then
       let x1 = getConstBool op1
           rval = case op of
              "!" -> ConstBool $ not x1
           f1 = replaceAllUses func inst rval
           f2 = deleteInstruction inst f1
           in (f2,True)
    else (func,False)

cfold_inst inst@(VBinOp name op op1 op2) func =
    if ( (op == "+") || (op == "-") ) && (isConstInt op2) && (getConstInt op2 == 0) then
       let rval = op1
           f1 = replaceAllUses func inst rval
           f2 = deleteInstruction inst f1
           in (f2,True)
    else if ( (op == "+") ) && (isConstInt op1) && (getConstInt op1 == 0) then
       let rval = op2
           f1 = replaceAllUses func inst rval
           f2 = deleteInstruction inst f1
           in (f2,True)
    else if ( (op == "-") ) && (isConstInt op1) && (getConstInt op1 == 0) then
       let f2 :: VFunction = updateInstructionF (VUnOp name "-" op2 ) func
           in (f2,True)
    else if (isConstInt op1) && (isConstInt op2) then
       let x1 = getConstInt op1
           x2 = getConstInt op2
           u1 :: Word64 = fromIntegral x1
           u2 :: Word64 = fromIntegral x2
           rval = case op of
              "==" -> ConstBool $ x1 == x2
              "!=" -> ConstBool $ x1 /= x2
              "<=" -> ConstBool $ x1 <= x2
              "<" -> ConstBool $ x1 < x2
              ">=" -> ConstBool $ x1 >= x2
              ">" -> ConstBool $ x1 > x2
              "u<=" -> ConstBool $ u1 <= u2
              "u<" -> ConstBool $ u1 < u2
              "u>=" -> ConstBool $ u1 >= u2
              "u>" -> ConstBool $ u1 > u2
              "+" -> ConstInt $ x1 + x2
              "-" -> ConstInt $ x1 - x2
              "*" -> ConstInt $ x1 * x2
              "/" -> ConstInt $ x1 `div` x2
              "%" -> ConstInt $ x1 `mod` x2
           f1 = replaceAllUses func inst rval
           f2 = deleteInstruction inst f1
           in (f2,True)
    else if (isConstBool op1) && (isConstBool op2) then
       let x1 = getConstBool op1
           x2 = getConstBool op2
           rval = case op of
              "==" -> ConstBool $ x1 == x2
              "!=" -> ConstBool $ x1 /= x2
              "&" -> ConstBool $ x1 && x2
              "|" -> ConstBool $ x1 || x2
           f1 = replaceAllUses func inst rval
           f2 = deleteInstruction inst f1
           in (f2,True)
    else (func,False)

cfold_inst _ func = (func, False)

cfold_function :: HashMap.Map String (VType, Maybe Int) -> VFunction -> (VFunction, [IO()])
cfold_function globals func =
  let insts = functionInstructions func
      foldf = \(func, changed) inst ->
        if changed /= Nothing then (func, changed) else
        case inst of
          VArrayLen _ al ->
            case al of
              GlobalRef nam ->
                let rval = ConstInt$ toInteger $ forceInt $ snd $ hml globals nam "globalref"
                    f1 = replaceAllUses func inst rval
                    f2 = deleteInstruction inst f1
                    in (f2, Just inst)
              InstRef nam ->
                let str :: String = printf "instref f:%s" (show func)
                    rinst :: VInstruction = hml (functionInstructions func) nam $ str
                    len :: Int = case rinst of
                      VAllocation _ _ (Just n) -> n
                      a -> error $ printf "bad allocation len :%s" $ show a
                    rval = ConstInt$ toInteger $ len
                    f1 = replaceAllUses func inst rval
                    f2 = deleteInstruction inst f1
                    in (f2,Just inst)
              a -> error $ printf "Invalid thing to take len of %s\n:inst:%s\nfunc:%s" (show a) (show inst) (show func)
          _ -> let (f2, cd) = cfold_inst inst func in (f2, if cd then Just inst else Nothing )
      (nfunc, changed) = foldl foldf (func, Nothing) insts
      dbgs :: [IO()] = [] -- [printf "inst:%s\nBEFORE:%s\nAFTER:%s\n" (show changed) (show func) (show nfunc)]
      in if changed /= Nothing then
         let (f2,d1) = cfold_function globals nfunc in (f2, dbgs ++ d1)
         else (func,dbgs)

isPure :: VInstruction -> Bool
isPure (VUnOp _ _ _ ) = True
isPure (VBinOp _ _ _ _ ) = True
isPure (VStore _ _ _) = False
isPure (VLookup _ _) = True
isPure (VAllocation _ _ _) = True
isPure (VArrayStore _ _ _ _) = False
isPure (VArrayLookup _ _ _) = True
isPure (VArrayLen _ _) = True
isPure (VReturn _ _) = False
isPure (VCondBranch _ _ _ _) = False
isPure (VUncondBranch _ _) = False
isPure (VMethodCall _ _ _ _) = False
isPure (VUnreachable _ ) = False
isPure (VPHINode _ _) = True


isPure2 :: VInstruction -> Bool
isPure2 (VUnOp _ _ _ ) = True
isPure2 (VBinOp _ _ _ _ ) = True
isPure2 (VStore _ _ _) = False
isPure2 (VLookup _ _) = False
isPure2 (VAllocation _ _ _) = True
isPure2 (VArrayStore _ _ _ _) = False
isPure2 (VArrayLookup _ _ _) = False
isPure2 (VArrayLen _ _) = True
isPure2 (VReturn _ _) = False
isPure2 (VCondBranch _ _ _ _) = False
isPure2 (VUncondBranch _ _) = False
isPure2 (VMethodCall _ _ _ _) = False
isPure2 (VUnreachable _ ) = False
isPure2 (VPHINode _ _) = True

dce :: Builder -> Builder
dce builder =
    let pm = pmod builder
        fxs :: HashMap.Map String VFunction = functions pm
        fxs2 = HashMap.map dce_function fxs
        pm2 = pm{functions=fxs2}
        in builder{pmod=pm2}

selemIndex :: Eq a => a -> [a] -> Int
selemIndex a b = case elemIndex a b of Just a -> a


cse :: Builder -> Builder
cse builder =
  let pm = pmod builder
      fxs :: HashMap.Map String VFunction = functions pm
      (cmbs) = HashMap.map (\x -> let domTree = blockDominators x in cse_function domTree x ) fxs
      pm2 = pm{functions=HashMap.map fst cmbs}
      in builder{pmod=pm2,debugs=( (debugs builder) ++ (concat $ map snd $ HashMap.elems cmbs) ) }

cse_function :: ( HashMap.Map String (Set.Set String) ) -> VFunction -> (VFunction, [IO()])
cse_function domTree func =
  let blockNames = blockOrder func
      (changed, f2) = foldl (\(changed0,f) bn ->
        if changed0 /= Nothing then (changed0,f) else
        let doms = Set.toList $ Set.delete bn $ hml domTree bn "csef"
            vb = hml (blocks f) bn "cse2"
            getInst = \x -> hml (functionInstructions f) x "cse3"
            bins = filter isPure2 $ map getInst (blockInstructions vb)
            (changed1,f2) = --if bn /= "entry" then error $ printf "%s:%s\n" bn (show doms) else
                            foldl (\(changed2,f) b2 -> if changed2 /= Nothing then (changed2,f) else
                                                       let vb2 = hml (blocks f) b2 "cse4"
                                                           bins2 = map (\x -> hml (functionInstructions f) x "cse5" ) (blockInstructions vb2)
                                                           (c2, f2) = foldl (\(changed3,f) inst1 -> if changed3 /= Nothing then (changed3, f) else
                                                                                                    foldl (\(changed4,f) inst2 -> --if ( (getName inst2) == "%44" ) && ( (getName inst1) == "%32" ) then error $ printf "bn:%s\ndoms:%s\ninst2:%s\ninst1:%s\neq:%s\nF:%s" bn (show doms) (show inst2) (show inst1) (show $ valueEq f inst1 inst2 ) (show f) else
                                                                                                                                  if changed4 /= Nothing then (changed4,f) else if not $ valueEq f inst1 inst2 then (changed4,f) else
                                                                                                                                    (Just (inst1, inst2), replaceAndRemove (InstRef $ getName inst1) f inst2 )
                                                                                                          ) (Nothing, func) bins
                                                                            ) (Nothing, func) bins2
                                                           in (c2, f2)
                                  ) (Nothing,func) doms
            in if changed1 /= Nothing then (changed1,f2) else
              let binsts = (blockInstructions vb)
                  (c2, f3) = foldl (\(changed5,f) inst1 -> if changed5 /= Nothing then (changed5, f) else
                                    foldl (\(changed6,f) inst2 -> if changed6 /= Nothing then (changed6,f) else if (
                          let repBName = getName inst2
                              repDName = getName inst1
                              in (selemIndex repBName binsts) >= (selemIndex repDName binsts)
                               ) || (not $ valueEq f inst1 inst2) then (changed6,f) else
                                 --error $ printf "bn:%s\ninst2:%s\ninst1:%s\neq:%s\nbk:%s\nprev:%s\nF:%s" bn (show inst2) (show inst1) (show $ valueEq f inst1 inst2 ) (show vb) (show func) (show f)
                                 (Just (inst2,inst1), replaceAndRemove (InstRef $ getName inst2) f inst1 )
                         ) (Nothing, func) bins
                      ) (Nothing, func) bins
                  in (c2, f3)
        ) (Nothing,func) blockNames
      dbgs :: [IO()] = [] -- [printf "inst:%s\nBEFORE:%s\nAFTER:%s\n" (show changed) (show func) (show f2)]
      in if changed /= Nothing then
         let (f3,d1) = cse_function domTree f2 in (f3, dbgs ++ d1)
         else (func,dbgs)

dce_function :: VFunction -> VFunction
dce_function func =
    let (f, c) = foldl (\(accFunc, changed) instr ->
            if (length $ getUses instr accFunc) == 0 && (isPure instr)
                then (deleteInstruction instr accFunc, True)
                else (accFunc, changed)) (func, False) (HashMap.elems $ functionInstructions func)
        in if c then dce_function f else f

partitionStoreLoadOther :: VFunction -> [Use] -> ([Use], [Use], [Use])
partitionStoreLoadOther func uses =
  let isaLoad = \use ->
        case do
          ui <- getUseInstr func use
          mv <- getUseValue func use
          return $ case ui of
            VLookup _ a -> if a == mv then True else False
            _ -> False
        of
          Just v -> v
          _ -> False
      (loads, other1) = partition isaLoad uses
      (stores, others) = partition (\use ->
          case do
            ui <- getUseInstr func use
            mv <- getUseValue func use
            return $ case ui of
              VStore _ _ a -> if a == mv then True else False
              _ -> False
          of
            Just v -> v
            _ -> False) other1
      in (stores, loads, others)

maybeToError2 :: Maybe a -> [IO()] -> Either [IO()] a
maybeToError2 (Just a) _ = Right a
maybeToError2 Nothing b = Left b


mem2reg_function :: PModule -> VFunction -> (PModule, [IO()])
mem2reg_function pm func =
  let allocas :: [VInstruction] = (getAllocas func)
      foldf = \(pm, func, changed, dbg) alloca ->
        if changed then (pm, func, True, dbg) else
        -- attempt change
        let uses0 :: [Use] = getUses alloca func
            isUse :: (VInstruction -> Bool) = \inst -> any (\x -> if (getName inst) == (useInstruction x) then True else False) uses0
            (_, loads0, _) = partitionStoreLoadOther func uses0
            lastValueInBlocks :: HashMap.Map String (Maybe ValueRef) = HashMap.empty
            phis :: HashMap.Map String (Maybe ValueRef) = HashMap.empty
            (_, _, pm2, newFunc,changed0, dbg2) = foldl (\(phis, bmap, accPm, acc,changed, dbg) loadu -> case do
                    loadf <- maybeToError2 (getUseInstr acc loadu) $ [printf "load failed :( for %s\n" (show loadu)]
                    (phis2, bmap2, accPm2, valM) <- getPreviousStoresInPreds2 isUse phis bmap accPm acc ( InstRef $ getName alloca ) loadf
                    let acc2 = (HashMap.!) (functions accPm2) (getName acc)
                    val <- maybeToError2 valM [printf "invalid lookup for %s\n" (show loadu)]
                    --val <- getPreviousStoreValue prevStore
                    let replU = replaceAllUses acc2 loadf val
                    let res :: (VFunction, [IO()])= (deleteInstruction loadf replU, []) -- [printf "PHIS:%s\n%s\nprev ID:%s\nfinID:%s\n" (show phis) (show loadf) (show $ lastId accPm) (show $ lastId accPm2), printf "previous store %s\n" (show valM), printf "FUNC:\n %s\n" (show $ deleteInstruction loadf replU) ])
                    let strs :: [String] = [printf "PHIS:%s\n%s\nprev ID:%s\nfinID:%s\n" (show phis) (show loadf) (show $ lastId accPm) (show $ lastId accPm2), printf "previous store %s\n" (show valM), printf "FUNC:\n %s\n" (show $ deleteInstruction loadf replU) ]
                    return $ (res,bmap2, phis2, accPm2)
                of
                    Left dbg2 -> (phis, bmap, accPm, acc,False, dbg ++ dbg2)
                    Right ((a,dbg2),bmap2, phis2, accPm2) -> (phis2, bmap2, accPm2{functions=(HashMap.insert (getName a) a (functions accPm2))}, a,True, dbg ++ dbg2 )
                ) (phis, lastValueInBlocks, pm, func,False, []) loads0
            --(newFunc, changed0) = (func, False)
            uses :: [Use] = getUses alloca newFunc
            (stores, loads, others) = partitionStoreLoadOther newFunc uses
            dbg3 = dbg ++ dbg2 ++ [] -- [printf "Uses %s | loads=%s\n" (show uses0) (show loads0)]
        in
          if (length uses) == (length stores) then
             let nfunc2 = deleteAllUses newFunc alloca
                 nfunc  = deleteInstruction alloca nfunc2
                 pmF = pm2{functions=(HashMap.insert (getName nfunc) nfunc (functions pm2))}
                 in (pmF, nfunc, True, dbg3 )
            else (pm2, newFunc, changed0, dbg3)
      (npm, nfunc, changed, dbgs) = foldl foldf (pm, func, False, []) allocas
      in if changed then
         let (npm2, dbg2) = mem2reg_function npm nfunc in (npm2, dbgs ++ dbg2)
         else (npm, dbgs)

gmem2reg_function :: PModule -> VFunction -> (PModule, [IO()])
gmem2reg_function pm func =
  let allocas :: [ValueRef] = HashMap.elems $ HashMap.mapWithKey (\x (t,a) -> GlobalRef x ) $ HashMap.filterWithKey (\x (t,a) -> a == Nothing) (globals pm)
      foldf :: (PModule, VFunction, Bool, [IO()]) -> ValueRef -> (PModule, VFunction, Bool, [IO()]) = \prevA@(pm, func, changed, dbg) alloca@(GlobalRef gv) ->
        if changed then prevA else
        -- attempt change
        let uses0 :: [Use] = getUsesValRef alloca func
            allInst = HashMap.elems $ functionInstructions func
            isUse :: (VInstruction -> Bool) = \inst -> not ( isPureWRT inst gv pm )
            (_, loadsm0, _) = partitionStoreLoadOther func uses0
            eblkI = blockInstructions ( hml (blocks func) "entry" "gm2r" )
            (eblkL,_) = foldl (\(acc,f) inst -> if f then (acc,f) else case hml (functionInstructions func) inst "gm2r2" of (VLookup _ _) -> (acc++[inst],f); _ -> (acc,True) ) ([], False) eblkI
            loads0 = filter (\x -> not $ elem (useInstruction x) eblkL ) loadsm0
            lastValueInBlocks :: HashMap.Map String (Maybe ValueRef) = HashMap.empty
            phis :: HashMap.Map String (Maybe ValueRef) = HashMap.empty
            (_, _, pm2, newFunc,changed0, dbg2) = foldl (\init@(phis, bmap, accPm, acc,changed, dbg) loadu -> case do
                    loadf <- maybeToError2 (getUseInstr acc loadu) $ [] -- [printf "load failed :(\n"]
                    (phis2, bmap2, accPm2, valM) <- getPreviousStoresInPreds2 isUse phis bmap accPm acc alloca loadf
                    acc2 <- maybeToError2 (HashMap.lookup (getName acc) (functions accPm2)) []
                    val <- maybeToError2 valM []
                    let replU = replaceAllUses acc2 loadf val
                    let res :: (VFunction, [IO()])= (deleteInstruction loadf replU, [])--[printf "PHIS:%s\n%s\nprev ID:%s\nfinID:%s\n" (show phis) (show loadf) (show $ lastId accPm) (show $ lastId accPm2), printf "previous store %s\n" (show valM), printf "FUNC:\n %s\n" (show $ deleteInstruction loadf replU) ])
                    return $ (res,bmap2, phis2, accPm2)
                of
                    Left dbg2 -> (phis, bmap, accPm, acc,False, dbg ++ dbg2)
                    Right ((a,dbg2),bmap2, phis2, accPm2) -> (phis2, bmap2, accPm2{functions=(HashMap.insert (getName a) a (functions accPm2))}, a,True, dbg ++ dbg2 )
                ) (phis, lastValueInBlocks, pm, func,False, []) loads0
            --(newFunc, changed0) = (func, False)
            dbg3 = dbg ++ dbg2 -- ++ [printf "Uses %s | loads=%s\n" (show uses0) (show loads0)]
        in
          (pm2, newFunc, changed0, dbg3)
      (npm, nfunc, changed, dbgs) :: (PModule, VFunction, Bool, [IO()]) = foldl foldf (pm, func, False, []) allocas
      dbgs0 = dbgs
      in if changed then
         let (npm2, dbg2) = gmem2reg_function npm nfunc in (npm2, dbgs0 ++ dbg2)
         else (npm, dbgs0)

optimize :: Builder -> Builder
optimize b = cfold $ {- ploopOpts $ -} loopOpts $ cfold $ dce $ cAssert $ cse $ gmem2reg $ mem2reg b
--optimize b = cfold $ loopOpts $ cfold $ dce $ cAssert $ cse $ gmem2reg $ mem2reg b

unsafeElemIndex :: Eq a => a -> [a] -> Int
unsafeElemIndex item array =
    case elemIndex item array of
        Just a -> a
        Nothing -> -1

getPreviousStoreValue :: VInstruction -> Either [IO()] ValueRef
getPreviousStoreValue instr =
    case instr of
        VStore _ a _ -> Right a
        VPHINode a b -> Right $ InstRef a
        _ -> Left [printf "getPrevious store didn't return a store?!!\n"]

unsafeGetOp :: VInstruction -> Int -> ValueRef
unsafeGetOp instr index =
    case getOp instr index of
        Just a -> a
        Nothing -> ConstInt 0

storesToBlockVals :: VFunction -> [VInstruction] -> [(String, ValueRef)]
storesToBlockVals func stores =
    map (\store -> (getInstructionParent func store, unsafeGetOp store 0)) stores

slice from to xs = take (to - from + 1) (drop from xs)

-- Helps eliminates unnecessary loads.
getPreviousStoreInBlock2 :: ( VInstruction -> Bool ) -> VFunction -> ValueRef -> VInstruction -> Either [IO()] (Maybe ValueRef)
getPreviousStoreInBlock2 isUse func alloca instr =
    do
        let prevInstrs :: [VInstruction] = getInstructionsBefore func instr
        lastOther <- foldl (\acc inst -> case inst of VLookup _ _ -> acc; _ -> if isUse inst then Right inst else acc ) (Left []) prevInstrs
        let val = case lastOther of VStore _ a b -> if b == alloca then Just a else Nothing; b -> Nothing
        return $ val

getPreviousValInBlock2 :: ( VInstruction -> Bool ) -> VFunction -> ValueRef -> VInstruction -> Either [IO()] (Maybe ValueRef)
getPreviousValInBlock2 isUse func alloca instr =
    do
        let prevInstrs :: [VInstruction] = getInstructionsBefore func instr
        lastOther <- foldl (\acc inst -> case inst of VLookup _ a -> if a == alloca then Right inst else acc; _ -> if isUse inst then Right inst else acc ) (Left []) prevInstrs
        let val = case lastOther of VStore _ a b -> if b == alloca then Just a else Nothing; VLookup n a -> if a == alloca then Just $ InstRef n else Nothing; b -> Nothing
        return $ val

getPreviousStoresInPreds2 :: ( VInstruction -> Bool ) -> HashMap.Map String (Maybe ValueRef) -> HashMap.Map String (Maybe ValueRef) -> PModule -> VFunction -> ValueRef -> VInstruction -> Either [IO()] (HashMap.Map String (Maybe ValueRef), HashMap.Map String (Maybe ValueRef), PModule, Maybe ValueRef)
getPreviousStoresInPreds2 isUse phis bmap pm func alloca instr =
    let prevStoreInBlock = getPreviousStoreInBlock2 isUse func alloca instr
        in case prevStoreInBlock of
             Right p -> Right (phis, bmap, pm, p)
             Left _ ->
                    case HashMap.lookup (getInstructionParent func instr) phis of
                      Just a -> Right $ (phis, bmap, pm, a)
                      Nothing -> do
                        let funcBlocks :: HashMap.Map String VBlock = (blocks func)
                        let blockName :: String = getInstructionParent func instr
                        block :: VBlock <- maybeToError2 (HashMap.lookup blockName funcBlocks) []
                        let preds :: [String] = blockPredecessors block
                        case length preds of
                          0 -> case getPreviousValInBlock2 isUse func alloca instr of
                                 Right a -> Right (phis, bmap, pm, a)
                                 _ -> let (instrName, npm0) = createID pm
                                          phi :: VInstruction = VLookup instrName alloca
                                          block2 :: VBlock = block{blockInstructions=([(getName phi)] ++ (blockInstructions block))}
                                          func2 :: VFunction = func{blocks=(HashMap.insert blockName block2 (blocks func)), functionInstructions=(HashMap.insert (getName phi) phi (functionInstructions func))}
                                          npm :: PModule = npm0{functions=(HashMap.insert (getName func2) func2 (functions npm0))}
                                          phis2 = HashMap.insert blockName (Just $ InstRef $ getName phi) phis
                                          in Right $ (phis2, bmap, npm, Just $ InstRef $ getName phi)
                          _ -> case HashMap.lookup blockName phis of
                                 Just a -> Right (phis,bmap,pm,a)
                                 Nothing ->
                                   let (instrName, npm0) = createID pm
                                       phi :: VInstruction = VPHINode instrName (HashMap.empty)
                                       block2 :: VBlock = block{blockInstructions=([(getName phi)] ++ (blockInstructions block))}
                                       func2 :: VFunction = func{blocks=(HashMap.insert blockName block2 (blocks func)), functionInstructions=(HashMap.insert (getName phi) phi (functionInstructions func))}
                                       npm :: PModule = npm0{functions=(HashMap.insert (getName func2) func2 (functions npm0))}
                                       phis2 = HashMap.insert blockName (Just $ InstRef $ getName phi) phis
                                       (newPmOrErrors, stores,bmap2,phis3) :: (Either [IO()] PModule, [Maybe ValueRef],HashMap.Map String (Maybe ValueRef),HashMap.Map String (Maybe ValueRef) ) = foldl (\(accPmOrErrors, accStores, bmap, phis) p ->
                                           case accPmOrErrors of
                                             Left errs -> (Left errs, [], bmap, phis)
                                             Right pm ->
                                               let predBlock :: VBlock = hml funcBlocks p "pred"
                                                   f2 :: VFunction = hml (functions pm) (getName func) "pred2"
                                                   lastInstrName :: String = last $ blockInstructions predBlock
                                                   lastInstr = hml (functionInstructions f2) lastInstrName "lin"
                                                   lk :: Maybe (Maybe ValueRef) = HashMap.lookup p bmap
                                                   in case lk of
                                                     Just a -> (Right pm, accStores ++ [a], bmap, phis )
                                                     Nothing ->
                                                       let axc = getPreviousStoresInPreds2 isUse phis bmap pm f2 alloca lastInstr
                                                           in case axc of
                                                             Left errs -> (Left errs, [], bmap, phis)
                                                             Right (phis2, bm2, pm2, val) ->
                                                               let bm3 = HashMap.insert p val bm2
                                                               in (Right pm2, accStores ++ [val], bm3, phis2)
                                           ) (Right npm, [], bmap, phis2) preds
                                       in case newPmOrErrors of
                                         Left errs -> Left errs
                                         Right npm ->
--                                           if "%15" == getName instr then error $ printf "npm:%s\nstores:%s\nbmap2:%s\n,phis3:%s\n" (show npm) (show stores) (show bmap2) (show phis3) else
                                           let nl = Data.Maybe.catMaybes stores
                                               in
                                               if length nl /= length stores then Right (phis, bmap, pm, Nothing)
                                               else
                                               let nphi = filter (\x -> x /= (InstRef $ getName phi) ) nl
                                                   f = hml (functions npm) (getName func) "fp"
                                                   in
                                                   if all (== head nphi) (tail nphi) then
                                                      let val = head nphi
                                                          bmapF = HashMap.map (\x -> if x == (Just $ InstRef $ getName phi) then Just $ val else x) bmap2
                                                          phisF = HashMap.map (\x -> if x == (Just $ InstRef $ getName phi) then Just $ val else x) phis3
                                                          f2 = replaceAllUses f phi val
                                                          nf = deleteInstruction phi f2
                                                          fpm :: PModule = npm{functions=(HashMap.insert (getName nf) nf (functions npm))}
                                                          in Right (phisF, bmapF, fpm, Just val)
                                                   else
                                                      let mapper :: HashMap.Map String ValueRef = HashMap.fromList $ zip preds nl
                                                          bmapF = bmap2
                                                          phisF = phis3
                                                          nf = updateInstructionF (VPHINode (getName phi) mapper ) f
                                                          fpm :: PModule = npm{functions=(HashMap.insert (getName nf) nf (functions npm))}
                                                          in Right (phisF, bmapF, fpm, Just $ InstRef $ getName phi)


reachableCompute :: (Set.Set String) -> HashMap.Map String (Set.Set String) -> VFunction -> HashMap.Map String (Set.Set String)
reachableCompute valid state func =
  let newState :: HashMap.Map String (Set.Set String) = Set.foldl
       (\accState bn ->
         let block = (HashMap.!) (blocks func) bn
             updatedDomSet =
                 foldl (\domSet predName ->
                          let predDom = hml accState predName "reachC"
                              in domSet `Set.union` predDom) (hml accState bn "rechU") (filter (\x -> HashMap.member x accState) $ blockPredecessors block)
             in HashMap.insert bn (updatedDomSet `Set.intersection` valid) accState
       )
       state valid
  in
    if state /= newState
    then reachableCompute valid newState func
    else state

reachable:: [String] -> VFunction -> HashMap.Map String (Set.Set String)
reachable validL func =
  let valid = Set.fromList validL
      initState :: HashMap.Map String (Set.Set String) = HashMap.fromList $ map (\k -> (k,(Set.fromList $ blockPredecessors (hml (blocks func) k "reach")) `Set.intersection` valid )) validL
  in reachableCompute valid initState func

blockDominatorsCompute :: HashMap.Map String (Set.Set String) -> VFunction -> HashMap.Map String (Set.Set String)
blockDominatorsCompute state func =
  let blcks = blocks func
      newState :: HashMap.Map String (Set.Set String) = HashMap.foldl
       (\accState block ->
         let bn = blockName block in
         if bn == "entry" then accState else
           let updatedDomSet =
                 foldl (\domSet predName ->
                          let predDom = HashMap.lookup predName accState in
                          case predDom of
                            Just set -> domSet `Set.intersection` set
                            Nothing -> domSet)
                 (HashMap.keysSet blcks) (blockPredecessors block)
           in
             HashMap.insert bn (updatedDomSet `Set.union` (Set.singleton bn)) accState
       )
       state blcks
  in
    if state /= newState
    then blockDominatorsCompute newState func
    else state

blockDominators :: VFunction -> HashMap.Map String (Set.Set String)
blockDominators func =
  let initState :: HashMap.Map String (Set.Set String) =
        HashMap.foldl
        (\acc block ->
          let set = if (blockName block) == "entry"
                    then (Set.singleton (blockName block))
                    else (HashMap.keysSet (blocks func))
          in
            HashMap.insert (blockName block) set acc)
        HashMap.empty (blocks func)
  in
    blockDominatorsCompute initState func

invertMap :: HashMap.Map String (Set.Set String) -> HashMap.Map String (Set.Set String)
invertMap normalMap =
    foldl
    (\accMap (key, valueSet) ->
        Set.fold
        (\value accMap2 ->
            case HashMap.lookup value accMap2 of
                Just v -> HashMap.insert value (v `Set.union` (Set.singleton key)) accMap2
                Nothing -> HashMap.insert value (Set.singleton key) accMap2)
        accMap valueSet)
    HashMap.empty (HashMap.assocs normalMap)
