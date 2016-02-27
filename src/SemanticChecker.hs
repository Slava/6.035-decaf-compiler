module SemanticChecker where

import ParseTypes
import Data.Map

data Data = Var { vName :: String, vType :: ParseTypes.Type }
          | Method { mName :: String
                   , mArgs :: [(String, ParseTypes.Type)]
                   , mRetType :: ParseTypes.Type }
          | Callout String
          deriving (Eq, Show)

data Module = Module {
  parent :: Maybe Module,
  lookup :: Map String Data
} deriving (Eq, Show)

getIR :: ParseTypes.Program -> Either String ParseTypes.Program
getIR ast =
  Right ast
