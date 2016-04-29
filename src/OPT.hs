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
      fxdbg :: HashMap.Map String (VFunction, [IO()]) = HashMap.map mem2reg_function fxs
      dbg = HashMap.fold (\(_, dbgs) acc -> acc ++ dbgs ) [] fxdbg
      fxs2 = HashMap.map fst fxdbg
      pm2 = pm{functions=fxs2}
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


mem2reg_function :: VFunction -> (VFunction, [IO()])
mem2reg_function func =
  let allocas = getAllocas func
      foldf = \(func, changed, dbg) alloca ->
        if changed then (func, True, dbg) else
        -- attempt change
        let uses0 :: [Use] = getUses alloca func
            (_, loads0, _) = partitionStoreLoadOther func uses0
            (newFunc,changed0, dbg2) = foldl (\(acc,changed, dbg) loadu -> case do
                    loadf <- maybeToError2 (getUseInstr acc loadu) $ [] -- [printf "load failed :(\n"]
                    valS <- getPreviousStore acc alloca loadf
                    val <- getPreviousStoreValue acc alloca loadf
                    let replU = replaceAllUses acc loadf val
                    let res :: (VFunction, [IO()] )= (deleteInstruction loadf replU, [])--[printf "%s\n" (show loadf), printf "previous store %s\n" (show valS), printf "FUNC:\n %s\n" (show $ deleteInstruction loadf replU) ])
                    return $ res
                of
                    Left dbg2 -> (acc,False, dbg ++ dbg2)
                    Right (a,dbg2) -> (a,True, dbg ++ dbg2 )
                ) (func,False, []) loads0
            --(newFunc, changed0) = (func, False)
            uses :: [Use] = getUses alloca newFunc
            (stores, loads, others) = partitionStoreLoadOther newFunc uses
            dbg3 = dbg ++ dbg2 -- ++ [printf "Uses %s | loads=%s\n" (show uses0) (show loads0)]
        in
          if (length uses) == (length stores) then
             let nfunc2 = deleteAllUses newFunc alloca
                 nfunc  = deleteInstruction alloca nfunc2
                  in (nfunc, True, dbg3)
            else (newFunc, changed0, dbg3)
      (nfunc, changed, dbgs) = foldl foldf (func, False, []) allocas
      in if changed then
         let (nf, dbg2) = mem2reg_function nfunc in (nf, dbgs ++ dbg2)
         else (func, dbgs)

optimize :: Builder -> Builder
optimize b = cse $ mem2reg b

unsafeElemIndex :: Eq a => a -> [a] -> Int
unsafeElemIndex item array =
    case elemIndex item array of
        Just a -> a
        Nothing -> -1

getPreviousStoreValue :: VFunction -> VInstruction -> VInstruction -> Either [IO()] ValueRef
getPreviousStoreValue func alloca instr =
    do
        i <- getPreviousStore func alloca instr
        case i of
            VStore _ a _ -> Right a
            _ -> Left [printf "getPrevious store didn't return a store?!!\n"]

-- Helps eliminates unnecessary loads.
getPreviousStore :: VFunction -> VInstruction -> VInstruction -> Either [IO()] VInstruction
getPreviousStore func alloca instr =
    do
        let prevInstrs = getInstructionsBefore func instr
        prevStore <- maybeToError2 (getLastStore alloca prevInstrs) []--[printf "failed to find last store for %s\n" (show instr)]
        let prevOther = getLastOther alloca prevInstrs
        _ <- if case prevOther of
                    Nothing -> True
                    Just a -> unsafeElemIndex a prevInstrs < unsafeElemIndex prevStore prevInstrs
             then Right True else Left []--[printf "bad instruction between load/store %s :(\n" (show prevOther)]
        return prevStore

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
