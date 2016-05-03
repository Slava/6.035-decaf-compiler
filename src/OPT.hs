{-# LANGUAGE ScopedTypeVariables #-}
module OPT where

import Data.List
import Data.Maybe
import qualified Data.Map as HashMap
import qualified Data.Set as Set
import qualified LLIR
import LLIR
import Text.Printf

-- NEED TO TO MEM2REG AS REQUISITE
mem2reg :: Builder -> Builder
mem2reg builder =
  let pm = pmod builder
      fxs :: HashMap.Map String VFunction = functions pm
      (pm2, dbg) :: (PModule, [IO()]) = HashMap.fold (
        \fx (newPm, dbgs) -> let (retPm, retDbgs) = mem2reg_function newPm fx
            in (retPm, dbgs ++ retDbgs)) (pm, []) fxs
      in builder{pmod=pm2,debugs=( (debugs builder) ++ dbg ) }

cse :: Builder -> Builder
cse builder =
  let pm = pmod builder
      fxs :: HashMap.Map String VFunction = functions pm
      fxs2 = HashMap.map cse_function fxs
      pm2 = pm{functions=fxs2}
      in builder{pmod=pm2}

cse_function :: VFunction -> VFunction
cse_function func = func

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
  let allocas = getAllocas func
      foldf = \(pm, func, changed, dbg) alloca ->
        if changed then (pm, func, True, dbg) else
        -- attempt change
        let uses0 :: [Use] = getUses alloca func
            (_, loads0, _) = partitionStoreLoadOther func uses0
            lastValueInBlocks :: HashMap.Map String (Maybe ValueRef) = HashMap.empty
            phis :: HashMap.Map String (Maybe ValueRef) = HashMap.empty
            (_, _, pm2, newFunc,changed0, dbg2) = foldl (\(phis, bmap, accPm, acc,changed, dbg) loadu -> case do
                    loadf <- maybeToError2 (getUseInstr acc loadu) $ [] -- [printf "load failed :(\n"]
                    (phis2, bmap2, accPm2, valM) <- getPreviousStoresInPreds phis bmap accPm acc alloca loadf
                    acc2 <- maybeToError2 (HashMap.lookup (getName acc) (functions accPm2)) []
                    val <- maybeToError2 valM []
                    --val <- getPreviousStoreValue prevStore
                    let replU = replaceAllUses acc2 loadf val
                    let res :: (VFunction, [IO()])= (deleteInstruction loadf replU, [printf "%s\nprev ID:%s\nfinID:%s\n" (show loadf) (show $ lastId accPm) (show $ lastId accPm2), printf "previous store %s\n" (show valM), printf "FUNC:\n %s\n" (show $ deleteInstruction loadf replU) ])
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
                 in (pmF, nfunc, True, dbg3 ++ [printf "!!!!\n%s!!!!\n" (show nfunc)])
            else (pm2, newFunc, changed0, dbg3)
      (npm, nfunc, changed, dbgs) = foldl foldf (pm, func, False, []) allocas
      in if changed then
         let (npm2, dbg2) = mem2reg_function npm nfunc in (npm2, dbgs ++ dbg2)
         else (npm, dbgs)

optimize :: Builder -> Builder
optimize b = cse $ mem2reg b

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

-- Helps eliminates unnecessary loads.
getPreviousStoreInBlock :: VFunction -> VInstruction -> VInstruction -> Either [IO()] (Maybe ValueRef)
getPreviousStoreInBlock func alloca instr =
    do
        let prevInstrs = getInstructionsBefore func instr
        prevStore <- maybeToError2 (getLastStore alloca prevInstrs) []--[printf "failed to find last store for %s\n" (show instr)]
        val <- case prevStore of
          VStore _ a _ -> Right a
          _ -> Left [printf "getPrevious store didnt return a store?\n"]
        let prevOther = getLastOther alloca prevInstrs
        let val2 = case prevOther of
                    Nothing -> Just val
                    Just a -> if unsafeElemIndex a prevInstrs < unsafeElemIndex prevStore prevInstrs then Just val else Nothing
        return $ val2

getPreviousStoresInPreds :: HashMap.Map String (Maybe ValueRef) -> HashMap.Map String (Maybe ValueRef) -> PModule -> VFunction -> VInstruction -> VInstruction -> Either [IO()] (HashMap.Map String (Maybe ValueRef), HashMap.Map String (Maybe ValueRef), PModule, Maybe ValueRef)
getPreviousStoresInPreds phis bmap pm func alloca instr =
    let prevStoreInBlock = getPreviousStoreInBlock func alloca instr
    in case prevStoreInBlock of
        Right p -> Right (phis, bmap, pm, p)
        Left _ ->
            do
                let funcBlocks :: HashMap.Map String VBlock = (blocks func)
                let blockName :: String = getInstructionParent func instr
                block :: VBlock <- maybeToError2 (HashMap.lookup blockName funcBlocks) []
                let preds :: [String] = blockPredecessors block
                case length preds of
                  0 -> error "block with 0 preds??\n"
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
                                       let predBlock :: VBlock = (HashMap.!) funcBlocks p
                                           f2 :: VFunction = (HashMap.!) (functions pm) (getName func)
                                           lastInstrName :: String = last $ blockInstructions predBlock
                                           lastInstr = (HashMap.!) (functionInstructions f2) lastInstrName
			                   lk :: Maybe (Maybe ValueRef) = HashMap.lookup p bmap
			                   in case lk of
			                     Just a -> (Right pm, accStores ++ [a], bmap, phis )
			                     Nothing ->
			                       let axc = getPreviousStoresInPreds phis bmap pm func alloca lastInstr
                                                   in case axc of
                                                     Left errs -> (Left errs, [], bmap, phis)
                                                     Right (phis2, bm2, pm2, val) ->
                                                       let bm3 = HashMap.insert blockName val bm2
                                                       in (Right pm2, accStores ++ [val], bm3, phis2)
                                   ) (Right npm, [], bmap, phis2) preds
                               in case newPmOrErrors of
                                 Left errs -> Left errs
                                 Right npm ->
                                   let nl = Data.Maybe.catMaybes stores
                                       in 
                                       if length nl /= length stores then Right (phis, bmap, pm, Nothing)
                                       else
                                       let nphi = filter (\x -> x /= (InstRef $ getName phi) ) nl
                                           f = (HashMap.!) (functions npm) (getName func)
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
                                                  nf = updateInstructionF (VPHINode (getName phi) mapper ) blockName f
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
