{-# LANGUAGE ScopedTypeVariables #-}
module OPT where

import Data.List
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
            (pm2, newFunc,changed0, dbg2) = foldl (\(accPm, acc,changed, dbg) loadu -> case do
                    loadf <- maybeToError2 (getUseInstr acc loadu) $ [] -- [printf "load failed :(\n"]
                    (accPm2, prevStore) <- getPreviousStoresInPreds accPm acc alloca loadf
                    acc2 <- maybeToError2 (HashMap.lookup (getName acc) (functions accPm2)) []
                    val <- getPreviousStoreValue prevStore
                    let replU = replaceAllUses acc2 loadf val
                    let res :: (VFunction, [IO()])= (deleteInstruction loadf replU, [])--[printf "%s\n" (show loadf), printf "previous store %s\n" (show valS), printf "FUNC:\n %s\n" (show $ deleteInstruction loadf replU) ])
                    return $ res
                of
                    Left dbg2 -> (accPm, acc,False, dbg ++ dbg2)
                    Right (a,dbg2) -> (accPm{functions=(HashMap.insert (getName a) a (functions accPm))}, a,True, dbg ++ dbg2 )
                ) (pm, func,False, []) loads0
            --(newFunc, changed0) = (func, False)
            uses :: [Use] = getUses alloca newFunc
            (stores, loads, others) = partitionStoreLoadOther newFunc uses
            dbg3 = dbg ++ dbg2 -- ++ [printf "Uses %s | loads=%s\n" (show uses0) (show loads0)]
        in
          if (length uses) == (length stores) then
             let nfunc2 = deleteAllUses newFunc alloca
                 nfunc  = deleteInstruction alloca nfunc2
                  in (pm2{functions=(HashMap.insert (getName nfunc) nfunc (functions pm2))}, nfunc, True, dbg3)
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
getPreviousStoreInBlock :: VFunction -> VInstruction -> VInstruction -> Either [IO()] VInstruction
getPreviousStoreInBlock func alloca instr =
    do
        let prevInstrs = getInstructionsBefore func instr
        prevStore <- maybeToError2 (getLastStore alloca prevInstrs) []--[printf "failed to find last store for %s\n" (show instr)]
        let prevOther = getLastOther alloca prevInstrs
        _ <- if case prevOther of
                    Nothing -> True
                    Just a -> unsafeElemIndex a prevInstrs < unsafeElemIndex prevStore prevInstrs
             then Right True else Left []--[printf "bad instruction between load/store %s :(\n" (show prevOther)]
        return prevStore

getPreviousStoresInPreds :: PModule -> VFunction -> VInstruction -> VInstruction -> Either [IO()] (PModule, VInstruction)
getPreviousStoresInPreds pm func alloca instr =
    let prevStoreInBlock = getPreviousStoreInBlock func alloca instr
    in case prevStoreInBlock of
        Left _ ->
            do
                let funcBlocks :: HashMap.Map String VBlock = (blocks func)
                let blockName :: String = getInstructionParent func instr
                block :: VBlock <- maybeToError2 (HashMap.lookup blockName funcBlocks) []
                let preds :: [String] = blockPredecessors block
                if length preds == 1
                    then
                        do
                            prevBlock :: VBlock <- maybeToError2 (HashMap.lookup (head preds) funcBlocks) []
                            let lastInstrName :: String = last $ blockInstructions prevBlock
                            lastInstr :: VInstruction <- maybeToError2 (HashMap.lookup lastInstrName (functionInstructions func)) []
                            getPreviousStoresInPreds pm func alloca lastInstr
                    else if length preds < 1
                        then Left [printf "How does a block have 0 preds??\n"]
                        else
                            let (newPmOrErrors, stores) :: (Either [IO()] PModule, [VInstruction]) = foldl (\(accPmOrErrors, accStores) p ->
                                    case accPmOrErrors of
                                        Left errs -> (Left errs, [])
                                        Right tempPm ->
                                            let f = HashMap.lookup (getName func) (functions tempPm)
                                                in case f of
                                                    Just f2 ->
                                                        let predBlockMaybe :: Maybe VBlock = HashMap.lookup p (blocks f2)
                                                            in case predBlockMaybe of
                                                                Just predBlock ->
                                                                    let lastInstrName :: String = last $ blockInstructions predBlock
                                                                        in case HashMap.lookup lastInstrName (functionInstructions f2) of
                                                                            Just lastInstr -> case getPreviousStoresInPreds tempPm f2 alloca lastInstr of
                                                                                Left errs -> (Left errs, [])
                                                                                Right (predModule, predStore) -> (Right predModule, accStores ++ [predStore])
                                                                            Nothing -> (Left [printf "Instruction doesn't exist??\n"], [])
                                                                Nothing -> (Left [printf "Block doesn't exist??\n"], [])
                                                    Nothing -> (Left [printf "Function mystically dissappeared because why not\n"], [])
                                                    ) (Right pm, []) preds
                                in case newPmOrErrors of
                                    Left errs -> Left errs
                                    Right npm ->
                                        let (instrName, npm2) = createID npm
                                            newFunc = HashMap.lookup (getName func) (functions npm2)
                                            in case newFunc of
                                                Just f ->
                                                    let newInstr :: VInstruction = VPHINode instrName (HashMap.fromList $ storesToBlockVals f stores)
                                                        block2 :: VBlock = block{blockInstructions=([(getName newInstr)] ++ (blockInstructions block))}
                                                        newFunc :: VFunction = f{blocks=(HashMap.insert blockName block2 (blocks f)), functionInstructions=(HashMap.insert (getName newInstr) newInstr (functionInstructions f))}
                                                        newPModule :: PModule = npm2{functions=(HashMap.insert (getName newFunc) newFunc (functions npm2))}
                                                        in Right (newPModule, newInstr)
                                                Nothing -> Left [printf "Function mystically dissappeared because why not\n"]
        Right p -> Right (pm, p)

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
