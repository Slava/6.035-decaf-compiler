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

semanticVerifyProgram :: Program -> Module -> [Either Dummy (IO())] -> (Module, [Either Dummy (IO())]) 
semanticVerifyDeclaration :: Declaration -> Module -> [Either Dummy (IO())] -> (Module, [Either Dummy (IO())]) 

semanticVerifyProgram (Program p) m ar= 
   foldl (\acc x -> semanticVerifyDeclaration x (fst acc) (snd acc) ) (m,ar) p


semanticVerifyDeclaration (Callout name) m ar = (m, [Right $ printf "saw %s\n" (show $ Callout name) ])

semanticVerifyDeclaration (Fields tup ) m ar = (m, [Right $ printf "saw %s\n" (show $ Fields tup ) ])

semanticVerifyDeclaration (Method rt name args body) m ar = (m, [Right $ printf "saw %s\n" (show $ Method rt name args body) ])

