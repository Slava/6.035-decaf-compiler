{-# OPTIONS -Wall #-}
{-# LANGUAGE ScopedTypeVariables #-}

module LLIR where

-- Imports
import qualified Prelude
import Text.Printf (printf)
import ParseTypes
import qualified Data.Map as HashMap


-- Data Types
data Value = VInstruction
           | VFunction
           | VConstant
