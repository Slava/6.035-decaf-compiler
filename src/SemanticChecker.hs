module SemanticChecker where

import ParseTypes
import Data.Map

data DataType = DBool 
              | DInt
              | DArray DataType
              | DFunction DataType [DataType]
                deriving (Eq, Show);

data Data = Data {
	vName :: String,
        vType :: DataType
} deriving (Eq, Show)

data Module = Module {
  parent :: Maybe Module,
  lookup :: Map String Data
} deriving (Eq, Show)

data Dummy = Dummy deriving(Eq, Show)

semanticVerify :: Program -> Module -> [Either Dummy IO()] -> (Module, [Either Dummy IO()])

semanticVerify (Program p) (Module m ) = 
   foldl (\acc x -> semanticVerify x (fst acc) (snd acc) ) (m,[]) p

semanticVerify :: Declaration -> Module -> [Either Dummy IO()] -> (Module, [Either Dummy IO()])
semanticVerify (Declaration p) (Module m ) = (m, [printf "saw %s\n" (show p) ])

