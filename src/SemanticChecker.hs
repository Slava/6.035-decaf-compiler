module SemanticChecker where
import GHC.Generics

import Prelude
import Text.Printf (printf)
import ParseTypes
import qualified Data.Map as HashMap


import Data.Aeson
import Data.Aeson.Encode.Pretty (encodePretty)
import qualified Data.ByteString.Lazy (putStrLn)

data DataType = DBool
              | DInt
              | DArray DataType Int {- Type and bounds -}
              | DFunction DataType [DataType]
              | InvalidType
                deriving (Eq, Show);

data Data = Data {
  vName :: String,
  vType :: DataType
} deriving (Eq, Show)

data Module = Module {
  parent :: Maybe Module,
  lookup :: HashMap.Map String Data
} deriving (Eq, Show)

addToModule :: Module -> DataType -> String -> (Module, Bool {- if failed -} )
addToModule (Module parent lookup) dtype dname =
  ( Module parent ( HashMap.insert dname (Data dname dtype) lookup ) , not $ HashMap.member dname lookup )

makeChild :: Module -> Module
makeChild m = Module (Just m) HashMap.empty

stringToType :: Type -> DataType
stringToType (Type n) = if n == "int" then DInt else if n == "boolean" then DBool else InvalidType

createArrayType :: DataType -> Maybe Int -> DataType
createArrayType typ (Just size) = DArray typ size
createArrayType typ Nothing = typ


data Dummy = Dummy deriving(Eq, Show)

semanticVerifyProgram :: Program -> Module -> [Either Dummy (IO ())] -> (Module, [Either Dummy (IO ())])
semanticVerifyProgram (Program p) m ar =
  foldl (\acc x -> semanticVerifyDeclaration x (fst acc) (snd acc)) (m, ar) p

semanticVerifyDeclaration :: Declaration -> Module -> [Either Dummy (IO ())] -> (Module, [Either Dummy (IO ())])
semanticVerifyDeclaration (Callout name) m ar = (m, ar ++ [Right $ printf "saw %s\n" (show $ Callout name)])

semanticVerifyDeclaration (Fields (stype, fields) ) m ar =
  let typ = stringToType stype in
    foldl ( \(m2,ar) (name, size) ->
      let (m2, success) = addToModule m (createArrayType typ size) name in (m2, if success then ar ++ [ Right $ printf "Declared variable %s\n" name ] else ar ++ [ Right $ printf "Could not redefine variable %s\n" name ] ) ) (m, ar) fields

semanticVerifyDeclaration (Method rt name args body) m ar =
  let (m2, success) = addToModule m (DFunction (stringToType rt) (map (stringToType . (\(Argument (x,_)) -> x)) args)) name in
    let ar2 = if success then ar ++ [ Right $ printf "Declared function %s\n" name ] else ar ++ [ Right $ printf "Could not redefine function %s\n" name ] in
      let m3 = makeChild m2 in
        let (m4, ar3) = foldl // TODO
          let block = semanticVerifyBlock body m2 ar2 in
            block

semanticVerifyBlock :: Block -> Module -> [Either Dummy (IO ())] -> (Module, [Either Dummy (IO ())])
semanticVerifyBlock (Block (decls, statements)) m ar =
  let (m2, ar2) = (foldl (\acc x -> semanticVerifyDeclaration x (fst acc) (snd acc)) (m, ar) decls) in
    let (m3, ar3) = (foldl (\acc x -> semanticVerifyStatement x (fst acc) (snd acc)) (m2, ar2) statements) in
      (m3, ar3)

{-(map (Right . Data.ByteString.Lazy.putStrLn . encodePretty) decls ) ++ -}

semanticVerifyStatement :: Statement -> Module -> [Either Dummy (IO ())] -> (Module, [Either Dummy (IO ())])
semanticVerifyStatement (Assignment (lexpr, rexpr)) m ar =
  let (m2, ar2) = semanticVerifyExpression lexpr m ar in
    let (m3, ar3) = semanticVerifyExpression rexpr m2 ar2 in
      (m3, ar3)

semanticVerifyStatement (MethodCallStatement methodCall) m ar = (m, ar ++ [Right $ printf "saw %s\n" (show $ MethodCallStatement methodCall)])

semanticVerifyStatement (BreakStatement) m ar = (m, ar ++ [Right $ printf "saw %s\n" (show $ BreakStatement)])

semanticVerifyStatement (ContinueStatement) m ar = (m, ar ++ [Right $ printf "saw %s\n" (show $ ContinueStatement)])

semanticVerifyStatement (ReturnStatement expr) m ar = (m, ar ++ [Right $ printf "saw %s\n" (show $ ReturnStatement expr)])

semanticVerifyStatement (LoopStatement lCond lBody lInit lIncr) m ar = (m, ar ++ [Right $ printf "saw %s\n" (show $ LoopStatement lCond lBody lInit lIncr)])

semanticVerifyStatement (IfStatement ifCond ifTrue ifFalse) m ar = (m, ar ++ [Right $ printf "saw %s\n" (show $ IfStatement ifCond ifTrue ifFalse)])

semanticVerifyExpression :: Expression -> Module -> [Either Dummy (IO ())] -> (Module, [Either Dummy (IO ())])
semanticVerifyExpression (BinOpExpression (op, lexpr, rexpr)) m ar = (m, ar ++ [Right $ printf "saw %s\n" (show $ BinOpExpression (op, lexpr, rexpr))])

semanticVerifyExpression (NegExpression expr) m ar = (m, ar ++ [Right $ printf "saw %s\n" (show $ NegExpression expr)])

semanticVerifyExpression (NotExpression expr) m ar = (m, ar ++ [Right $ printf "saw %s\n" (show $ NotExpression expr)])

semanticVerifyExpression (LengthExpression expr) m ar = (m, ar ++ [Right $ printf "saw %s\n" (show $ LengthExpression expr)])

semanticVerifyExpression (LocationExpression loc) m ar = (m, ar ++ [Right $ printf "saw %s\n" (show $ LocationExpression loc)])

semanticVerifyExpression (LiteralExpression lit) m ar = (m, ar ++ [Right $ printf "saw %s\n" (show $ LiteralExpression lit)])

semanticVerifyExpression (MethodCallExpression methodCall) m ar = (m, ar ++ [Right $ printf "saw %s\n" (show $ MethodCallExpression methodCall)])

semanticVerifyExpression (CondExpression cCond cTrue cFalse) m ar = (m, ar ++ [Right $ printf "saw %s\n" (show $ CondExpression cCond cTrue cFalse)])
