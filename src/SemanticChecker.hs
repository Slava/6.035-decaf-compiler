module SemanticChecker where

import Text.Printf (printf)
import ParseTypes
import qualified Data.Map

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
  lookup :: Data.Map.Map String Data
} deriving (Eq, Show)

data Dummy = Dummy deriving(Eq, Show)

semanticVerify :: a -> Module -> [Either Dummy IO()] -> (Module, [Either Dummy IO()])

semanticVerify (Program p) (Module m ) = 
   foldl (\acc x -> semanticVerify x (fst acc) (snd acc) ) (m,[]) p

semanticVerify (Declaration p) (Module m ) = (m, [printf "saw %s\n" (show p) ])

