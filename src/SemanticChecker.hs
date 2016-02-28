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
semanticVerifyProgram (Program p) m ar =
  foldl (\acc x -> semanticVerifyDeclaration x (fst acc) (snd acc)) (m, ar) p

semanticVerifyDeclaration :: Declaration -> Module -> [Either Dummy (IO())] -> (Module, [Either Dummy (IO())])
semanticVerifyDeclaration (Callout name) m ar = (m, [Right $ printf "saw %s\n" (show $ Callout name)])

semanticVerifyDeclaration (Fields tup ) m ar = (m, [Right $ printf "saw %s\n" (show $ Fields tup)])

semanticVerifyDeclaration (Method rt name args body) m ar =
  let block = semanticVerifyBlock body m ar in block

semanticVerifyBlock :: Block -> Module -> [Either Dummy (IO())] -> (Module, [Either Dummy (IO())])
semanticVerifyBlock (Block (decls, statements)) m ar =
  let (m2, ar2) = (foldl (\acc x -> semanticVerifyDeclaration x (fst acc) (snd acc)) (m, ar) decls) in
    let (m3, ar3) = (foldl (\acc x -> semanticVerifyStatement x (fst acc) (snd acc)) (m2, ar2) statements) in
      (m3, ar3)

semanticVerifyStatement :: Statement -> Module -> [Either Dummy (IO())] -> (Module, [Either Dummy (IO())])
semanticVerifyStatement (Assignment (lexpr, rexpr)) m ar = (m, [Right $ printf "saw %s\n" (show $ Assignment (lexpr, rexpr))])

semanticVerifyStatement (MethodCallStatement methodCall) m ar = (m, [Right $ printf "saw %s\n" (show $ MethodCallStatement methodCall)])

semanticVerifyStatement (BreakStatement) m ar = (m, [Right $ printf "saw %s\n" (show $ BreakStatement)])

semanticVerifyStatement (ContinueStatement) m ar = (m, [Right $ printf "saw %s\n" (show $ ContinueStatement)])

semanticVerifyStatement (ReturnStatement expr) m ar = (m, [Right $ printf "saw %s\n" (show $ ReturnStatement expr)])

semanticVerifyStatement (LoopStatement lCond lBody lInit lIncr) m ar = (m, [Right $ printf "saw %s\n" (show $ LoopStatement lCond lBody lInit lIncr)])

semanticVerifyStatement (IfStatement ifCond ifTrue ifFalse) m ar = (m, [Right $ printf "saw %s\n" (show $ IfStatement ifCond ifTrue ifFalse)])
