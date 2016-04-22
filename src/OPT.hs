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
        let uses :: [Use] = getUses alloca func
            (stores, loads, others) = partitionStoreLoadOther func uses
        in
          if (length uses) == (length stores) then
            let nfunc  = deleteInstruction alloca func
                nfunc2 = foldl (\func use ->
                  case getUseInstr func use of
                    Just inst -> deleteInstruction inst func
                    Nothing -> func) nfunc uses
                in (nfunc2, True)
            else (func, False)
      (nfunc, changed) = foldl foldf (func, False) allocas
      in if changed then mem2reg_function nfunc else func

optimize :: Builder -> Builder
optimize b = cse $ mem2reg b
