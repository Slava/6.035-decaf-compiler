{-# LANGUAGE ScopedTypeVariables #-}
module OPT where

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

mem2reg_function :: VFunction -> VFunction
mem2reg_function func = func

optimize :: Builder -> Builder
optimize b = cse $ mem2reg b
