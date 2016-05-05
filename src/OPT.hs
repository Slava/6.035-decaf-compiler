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

cse :: Builder -> Builder
cse builder =
  let pm = pmod builder
      fxs :: HashMap.Map String VFunction = functions pm
      fxs2 = HashMap.map cse_function fxs
      pm2 = pm{functions=fxs2}
      in builder{pmod=pm2}

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
                                  tDomBlocks :: [String] = Set.toList $ Set.difference trueDomBlocks falseDomBlocks
                                  fDomBlocks :: [String] = Set.toList $ Set.difference falseDomBlocks trueDomBlocks
                                  r1 :: VFunction = replaceBlockUses accf inst tDomBlocks (ConstBool True)
                                  r2 :: VFunction = replaceBlockUses r1 inst fDomBlocks (ConstBool False)
                                  errS :: String = printf "tdom:%s\nfdom:%s\ninst:%s\nF:%s\nafter:%s\n" (show tDomBlocks) (show fDomBlocks) (show inst) (show accf) (show r2)
                                  in --error errS
                                     r2
                            _ -> accf
                        _ -> accf) func (blockOrder func)

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
        block2 :: VBlock = block{blockSuccessors=[ndest]}
        f0 :: VFunction = updateBlockF block2 func
        f1 :: VFunction = removePredecessor (hml (blocks f0) ndest "cfold rpred") (getName block) f0
        f2 :: VFunction = updateInstructionF (VUncondBranch name dest) f1
        in (f2, True)

-- TODO if block has only itself as predecessor
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
              in --if (name /= "%13") && (name /= "%6") then error $ printf "inst:%s\nPRE:%s\nPOST:%s" (show inst) (show func) (show f3) else 
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
        if changed then (func, True) else
        case inst of
          VArrayLen _ al ->
            case al of
              GlobalRef nam ->
                let rval = ConstInt$ toInteger $ forceInt $ snd $ hml globals nam "globalref"
                    f1 = replaceAllUses func inst rval
                    f2 = deleteInstruction inst f1
                    in (f2,True)
              InstRef nam ->
                let str :: String = printf "instref f:%s" (show func)
                    rinst :: VInstruction = hml (functionInstructions func) nam $ str
                    len :: Int = case rinst of
                      VAllocation _ _ (Just n) -> n
                      a -> error $ printf "bad allocation len :%s" $ show a
                    rval = ConstInt$ toInteger $ len
                    f1 = replaceAllUses func inst rval
                    f2 = deleteInstruction inst f1
                    in (f2,True)
              a -> error $ printf "Invalid thing to take len of %s\n:inst:%s\nfunc:%s" (show a) (show inst) (show func)
          _ -> cfold_inst inst func
      (nfunc, changed) = foldl foldf (func, False) insts
      dbgs :: [IO()] = [printf "func:%s\n" (show nfunc)]
      in if changed then
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

dce :: Builder -> Builder
dce builder =
    let pm = pmod builder
        fxs :: HashMap.Map String VFunction = functions pm
        fxs2 = HashMap.map dce_function fxs
        pm2 = pm{functions=fxs2}
        in builder{pmod=pm2}

selemIndex :: Eq a => a -> [a] -> Int
selemIndex a b = case elemIndex a b of Just a -> a

cse_function :: VFunction -> VFunction
cse_function func =
  let blockNames = blockOrder func
      domTree = blockDominators func
      (changed, f2) = foldl (\(changed,f) bn ->
        if changed then (changed,f) else
        let doms = Set.toList $ Set.delete bn $ hml domTree bn "csef"
            vb = hml (blocks f) bn "cse2"
            getInst = \x -> hml (functionInstructions f) x "cse3"
            bins = map getInst (blockInstructions vb)
            (changed,f2) = --if bn /= "entry" then error $ printf "%s:%s\n" bn (show doms) else 
                           foldl (\(changed,f) b2 ->
                let vb2 = hml (blocks f) b2 "cse4"
                    bins2 = map (\x -> hml (functionInstructions f) x "cse5" ) (blockInstructions vb2)
                    (c2, f2) = foldl (\(changed,f) inst1 -> if changed then (changed, f) else
                        foldl (\(changed,f) inst2 -> --if ( (getName inst2) == "%44" ) && ( (getName inst1) == "%32" ) then error $ printf "bn:%s\ndoms:%s\ninst2:%s\ninst1:%s\neq:%s\nF:%s" bn (show doms) (show inst2) (show inst1) (show $ valueEq f inst1 inst2 ) (show f) else 
                           if changed then (changed,f) else if not $ valueEq f inst1 inst2 then (changed,f) else 
                             (True, replaceAndRemove (InstRef $ getName inst1) f inst2 ) 
                           ) (False, f) bins
                      ) (False, f) bins2
                    in (c2, f2)
              ) (False,f) doms
            in if changed then (changed,f2) else
              let binsts = (blockInstructions vb)
                  (c2, f3) = foldl (\(changed,f) inst1 -> if changed then (changed, f) else
                                    foldl (\(changed,f) inst2 -> if changed then (changed,f) else if (
                          let repBName = getName inst2
                              repDName = getName inst1
                              in (selemIndex repBName binsts) >= (selemIndex repDName binsts)
                               ) || (not $ valueEq f inst1 inst2) then (changed,f) else 
                                 --error $ printf "bn:%s\ninst2:%s\ninst1:%s\neq:%s\nF:%s" bn (show inst2) (show inst1) (show $ valueEq f inst1 inst2 ) (show f)
                                 (True, replaceAndRemove (InstRef $ getName inst2) f inst1 ) 
                         ) (False, f) bins
                      ) (changed, f2) bins
                  in (c2, f3)
        ) (False,func) blockNames
      in if changed then cse_function f2 else f2

dce_function :: VFunction -> VFunction
dce_function func =
    foldl (\accFunc instr ->
        if (length $ getUses instr accFunc) == 0 && (isPure instr)
            then deleteInstruction instr accFunc
            else accFunc) func (HashMap.elems $ functionInstructions func)

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
            isUse :: (VInstruction -> Bool) = \inst -> any (\x -> (getName inst) == (useInstruction x) ) uses0
            (_, loads0, _) = partitionStoreLoadOther func uses0
            lastValueInBlocks :: HashMap.Map String (Maybe ValueRef) = HashMap.empty
            phis :: HashMap.Map String (Maybe ValueRef) = HashMap.empty
            (_, _, pm2, newFunc,changed0, dbg2) = foldl (\(phis, bmap, accPm, acc,changed, dbg) loadu -> case do
                    loadf <- maybeToError2 (getUseInstr acc loadu) $ [] -- [printf "load failed :(\n"]
                    (phis2, bmap2, accPm2, valM) <- getPreviousStoresInPreds2 isUse phis bmap accPm acc ( InstRef $ getName alloca ) loadf
                    acc2 <- maybeToError2 (HashMap.lookup (getName acc) (functions accPm2)) []
                    val <- maybeToError2 valM []
                    --val <- getPreviousStoreValue prevStore
                    let replU = replaceAllUses acc2 loadf val
                    let res :: (VFunction, [IO()])= (deleteInstruction loadf replU, [])--[printf "PHIS:%s\n%s\nprev ID:%s\nfinID:%s\n" (show phis) (show loadf) (show $ lastId accPm) (show $ lastId accPm2), printf "previous store %s\n" (show valM), printf "FUNC:\n %s\n" (show $ deleteInstruction loadf replU) ])
                    let strs :: [String] = [printf "PHIS:%s\n%s\nprev ID:%s\nfinID:%s\n" (show phis) (show loadf) (show $ lastId accPm) (show $ lastId accPm2), printf "previous store %s\n" (show valM), printf "FUNC:\n %s\n" (show $ deleteInstruction loadf replU) ]
                    return $ (res,bmap2, phis2, accPm2)
                of
                    Left dbg2 -> (phis, bmap, accPm, acc,False, dbg ++ dbg2)
                    Right ((a,dbg2),bmap2, phis2, accPm2) -> (phis2, bmap2, accPm2{functions=(HashMap.insert (getName a) a (functions accPm2))}, a,True, dbg ++ dbg2 )
                ) (phis, lastValueInBlocks, pm, func,False, []) loads0
            --(newFunc, changed0) = (func, False)
            uses :: [Use] = getUses alloca newFunc
            (stores, loads, others) = partitionStoreLoadOther newFunc uses
            dbg3 = dbg ++ dbg2 -- ++ [printf "Uses %s | loads=%s\n" (show uses0) (show loads0)]
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
optimize b = cfold $ dce $ cAssert $ cse $ gmem2reg $ mem2reg b

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
        lastOther <- foldl (\acc inst -> if isUse inst then Right inst else acc ) (Left []) prevInstrs
        let val = case lastOther of VStore _ a b -> if b == alloca then Just a else Nothing; _ -> Nothing
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
                          0 -> let (instrName, npm0) = createID pm
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
