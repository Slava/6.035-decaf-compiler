{-# LANGUAGE ScopedTypeVariables #-}
module OPT where

import Data.List
import qualified Data.Map as HashMap
import qualified LLIR
import LLIR

-- NEED TO TO MEM2REG AS REQUISITE
mem2reg :: Builder -> Builder
mem2reg builder =
  let pm = pmod builder
      fxs :: HashMap.Map String VFunction = functions pm
      fxs2 = HashMap.map mem2reg_function fxs
      pm2 = pm{functions=fxs2}
      in builder{pmod=pm2}

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

mem2reg_function :: VFunction -> VFunction
mem2reg_function func =
  let allocas = getAllocas func
      foldf = \(func, changed) alloca -> if changed then (func, True) else
        -- attempt change
        let uses0 :: [Use] = getUses alloca func
            (_, loads0, _) = partitionStoreLoadOther func uses0
            (newFunc,changed0) = foldl (\(acc,changed) loadu -> case do
                    loadf <- getUseInstr acc loadu
                    val <- getPreviousStoreValue func alloca loadf
                    let replU = replaceAllUses func loadf val
                    return $ deleteInstruction loadf replU
                of
                    Nothing -> (acc,False)
                    Just a -> (a,True)
                ) (func,False) loads0
            --(newFunc, changed0) = (func, False)
            uses :: [Use] = getUses alloca newFunc
            (stores, loads, others) = partitionStoreLoadOther newFunc uses
        in
          if (length uses) == (length stores) then
             let nfunc2 = deleteAllUses newFunc alloca
                 nfunc  = deleteInstruction alloca nfunc2
                  in (nfunc, True)
            else (newFunc, changed0)
      (nfunc, changed) = foldl foldf (func, False) allocas
      in if changed then mem2reg_function nfunc else func

optimize :: Builder -> Builder
optimize b = cse $ mem2reg b

unsafeElemIndex :: Eq a => a -> [a] -> Int
unsafeElemIndex item array =
    case elemIndex item array of
        Just a -> a
        Nothing -> -1

getPreviousStoreValue :: VFunction -> VInstruction -> VInstruction -> Maybe ValueRef
getPreviousStoreValue func alloca instr =
    do
        i <- getPreviousStore func alloca instr
        case i of
            VStore _ a _ -> Just a
            _ -> Nothing

-- Helps eliminates unnecessary loads.
getPreviousStore :: VFunction -> VInstruction -> VInstruction -> Maybe VInstruction
getPreviousStore func alloca instr =
    do
        let prevInstrs = getInstructionsBefore func instr
        prevStore <- getLastStore alloca prevInstrs
        let prevOther = getLastOther alloca prevInstrs
        _ <- if case prevOther of
                    Nothing -> True
                    Just a -> unsafeElemIndex a prevInstrs < unsafeElemIndex prevStore prevInstrs
             then Just True else Nothing
        return prevStore
