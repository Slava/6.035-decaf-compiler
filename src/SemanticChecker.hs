{-# OPTIONS -Wall #-}

module SemanticChecker where
import GHC.Generics

import Prelude
import Text.Printf (printf)
import ParseTypes
import qualified Data.Map as HashMap


import Data.Aeson
import Data.Aeson.Encode.Pretty (encodePretty)
import qualified Data.ByteString.Lazy (putStrLn)

data DataType = DCallout
              | DBool
              | DInt
              | DArray DataType (Maybe Int) {- Type and bounds -}
              | DFunction DataType [DataType]
              | DVoid
              | DString
              | DChar
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

moduleLookup :: Module -> String -> Maybe DataType
moduleLookup (Module parent m) s =
  case HashMap.lookup s m of
    Just (Data _ a) -> Just a
    Nothing -> case parent of
      Just a -> moduleLookup a s
      Nothing -> Nothing

makeChild :: Module -> Module
makeChild m = Module (Just m) HashMap.empty

stringToType :: Type -> DataType
stringToType (Type n) = if n == "int" then DInt else if n == "boolean" then DBool else InvalidType

arrayInnerType :: DataType -> DataType
arrayInnerType (DArray n _) = n
arrayInnerType DCallout = InvalidType
arrayInnerType DBool = InvalidType
arrayInnerType DInt = InvalidType
arrayInnerType (DFunction a b) = InvalidType
arrayInnerType DVoid = InvalidType
arrayInnerType InvalidType = InvalidType

createArrayType :: DataType -> Maybe Int -> DataType
createArrayType typ (Just size) = DArray typ (Just size)
createArrayType typ Nothing = typ


data Dummy = Dummy deriving(Eq, Show)

combineCx :: Either [IO ()] Dummy -> Either [IO ()] Dummy -> Either [IO ()] Dummy
combineCx cx (Right Dummy) =
  cx

combineCx (Right Dummy) newCx =
  newCx

combineCx (Left ls) (Left newLs) =
  Left (ls ++ newLs)


semanticVerifyProgram :: Program -> Module -> Either [IO ()] Dummy -> (Module, Either [IO ()] Dummy)
semanticVerifyProgram (Program p) m ar =
  foldl (\acc x -> semanticVerifyDeclaration x (fst acc) (snd acc)) (m, ar) p

semanticVerifyDeclaration :: Declaration -> Module -> Either [IO ()] Dummy -> (Module, Either [IO ()] Dummy)
semanticVerifyDeclaration (Callout name) m ar =
  let (m2, success) = addToModule m DCallout name
      res = (if success then Right Dummy else Left [ printf "Could not redefine callout %s\n" name ] )
      ar2 = (combineCx ar res) in
      (m2, ar2)

semanticVerifyDeclaration (Fields (stype, fields) ) m ar =
  let typ = stringToType stype in
    foldl ( \(m2,ar) (name, size) ->
      let (m2, success) = addToModule m (createArrayType typ size) name
          res = (if success then Right Dummy else Left [ printf "Could not redefine variable %s\n" name ] )
          ar2 = (combineCx ar res) in
          (m2, ar2)
    ) (m, ar) fields

semanticVerifyDeclaration (Method rt name args body) m ar =
  let (m2, success) = addToModule m (DFunction (stringToType rt) (map (stringToType . (\(Argument (x,_)) -> x)) args)) name
      ar2 = if success then (combineCx ar (Right Dummy)) else (combineCx ar (Left [ printf "Could not redefine function %s\n" name ]))
      m3 = makeChild m2
      (m4, ar3) = foldl (\(m2,ar) (Argument (t, s)) ->
        let (m2, success) = addToModule m (stringToType t) s
            res = (if success then Right Dummy else Left [ printf "Could not redefine argument %s\n" s ] )
            ar2 = combineCx ar res in
            (m2, ar2)
        ) (m3, ar2) args
      block = semanticVerifyBlock body m4 ar3 in
        block

semanticVerifyBlock :: Block -> Module -> Either [IO ()] Dummy -> (Module, Either [IO ()] Dummy)
semanticVerifyBlock (Block (decls, statements)) m ar =
  let (m2, ar2) = (foldl (\acc x -> semanticVerifyDeclaration x (fst acc) (snd acc)) (m, ar) decls) in
    let (m3, ar3) = (foldl (\acc x -> semanticVerifyStatement x (fst acc) (snd acc)) (m2, ar2) statements) in
      (m3, ar3)

{-(map (Right . Data.ByteString.Lazy.putStrLn . encodePretty) decls ) ++ -}

semanticVerifyStatement :: Statement -> Module -> Either [IO ()] Dummy -> (Module, Either [IO ()] Dummy)
semanticVerifyStatement (Assignment (lexpr, rexpr)) m ar =
  let (m2, ar2, ty2) = semanticVerifyExpression lexpr m ar
      (m3, ar3, ty3) = semanticVerifyExpression rexpr m2 ar2
      res = if ty2 == ty3 then (Right Dummy) else Left [printf "Type of assignment incorrect -- expected %s, received %s\n" (show ty2) (show ty3) ]
      ar4 = combineCx ar3 res in
        (m3, ar4)

semanticVerifyStatement (MethodCallStatement methodCall) m ar = (m, combineCx ar (Left [printf "saw %s\n" (show $ MethodCallStatement methodCall)]))

semanticVerifyStatement (BreakStatement) m ar = (m, combineCx ar (Left [printf "saw %s\n" (show $ BreakStatement)]))

semanticVerifyStatement (ContinueStatement) m ar = (m, combineCx ar (Left [printf "saw %s\n" (show $ ContinueStatement)]))

-- TODO: CHECK CORRECT TYPES
semanticVerifyStatement (ReturnStatement expr) m ar =
  let (m2, ar2, typ) = semanticVerifyExpression expr m ar in
    (m2, ar2)

-- TODO: HANDLE SCOPING STUFF
semanticVerifyStatement (LoopStatement lCond lBody lInit lIncr) m ar =
  let (m2, ar2, ty2) = semanticVerifyExpression lCond m ar
      (m3, ar3) = semanticVerifyBlock lBody m ar
      (m4, ar4) = case lInit of
        Just sta  -> semanticVerifyStatement sta m ar
        Nothing   -> (m, Right Dummy)
      cx1 = combineCx ar3 $ if ty2 == DInt then Right Dummy else Left [ printf "Loop condition expected expression of type bool but got %s\n" (show ty2) ]
      cx2 = combineCx cx1 ar4 in
        (m, cx2)

semanticVerifyStatement (IfStatement ifCond ifTrue ifFalse) m ar =
  let (m2, ar2, ty2) = semanticVerifyExpression ifCond m ar
      (m3, ar3) = semanticVerifyBlock ifTrue m ar2
      (m4, ar4) = semanticVerifyBlock ifFalse m ar3
      res = if ty2 == DInt then Right Dummy else Left [ printf "Type of conditional in ternary incorrect -- expected %s, received %s\n" (show DBool) (show ty2) ]
      ar5 = combineCx ar4 res in
        (m, ar5)

semanticVerifyExpression :: Expression -> Module -> Either [IO ()] Dummy -> (Module, Either [IO ()] Dummy, DataType)

-- TODO: CHECK CORRECT TYPES
semanticVerifyExpression (BinOpExpression (op, lexpr, rexpr)) m ar =
  let (m2, ar2, ty2) = semanticVerifyExpression lexpr m ar
      (m3, ar3, ty3) = semanticVerifyExpression rexpr m2 ar2
      expcTypes = expectedOperandTypes op
      returnType = returnOperatorType op
      cx1 = combineCx ar3 (if ty2 `elem` expcTypes then Right Dummy else Left [ printf "Incorrect type of left operand for op %s: %s\n" op (show ty2) ])
      cx2 = combineCx cx1 (if ty3 == ty2 then Right Dummy else Left [ printf "Incorrect type of right operand for op %s: %s; Expected: %s\n" op (show ty3)  (show ty2)]) in
        (m3, cx2, returnType)

semanticVerifyExpression (NegExpression expr) m ar =
  let (m2, ar2, ty2) = semanticVerifyExpression expr m ar
      res = if ty2 == DInt then Right Dummy else Left [ printf "Type of negation expression incorrect -- expected %s, received %s\n" (show DInt) (show ty2) ]
      ar3 = combineCx ar2 res in
        (m2, ar3, DInt)

semanticVerifyExpression (NotExpression expr) m ar =
  let (m2, ar2, ty2) = semanticVerifyExpression expr m ar
      res = if ty2 == DBool then Right Dummy else Left [printf "Type of not expression incorrect -- expected %s, received %s\n" (show DBool) (show ty2) ]
      ar3 = combineCx ar2 res in
        (m2, ar3, DBool)

semanticVerifyExpression (LengthExpression expr) m ar =
  let (m2, ar2, ty2) = semanticVerifyExpression expr m ar
      ar3 = combineCx ar2 $ case ty2 of
         DArray _ _ -> Right Dummy
         x -> Left [ printf "Type of length expression incorrect -- expected array, received %s\n" (show ty2) ]
      in
        (m2, ar3, DInt)

semanticVerifyExpression (LiteralExpression lit) m ar =
  (m, combineCx ar (Right Dummy), litType lit)

semanticVerifyExpression (MethodCallExpression methodCall) m ar = (m, combineCx ar (Right Dummy), InvalidType)

semanticVerifyExpression (CondExpression cCond cTrue cFalse) m ar =
  let (m2, ar2, ty2) = semanticVerifyExpression cCond m ar
      (m3, ar3, ty3) = semanticVerifyExpression cTrue m2 ar2
      (m4, ar4, ty4) = semanticVerifyExpression cFalse m3 ar3
      ar5 = combineCx ar4 $ if ty2 == DInt then (Right Dummy) else (Left [ printf "Type of conditional in ternary incorrect -- expected %s, received %s\n" (show DBool) (show ty2) ])
      ar6 = combineCx ar5 $ if ty3 == ty4 then (Right Dummy) else (Left [ printf "Types in ternary don't match %s %s\n" (show ty3) (show ty4) ]) in
        (m4, ar6, ty3)

semanticVerifyExpression (LocationExpression loc) m ar =
  case (moduleLookup m loc) of
    Nothing -> (m, combineCx ar (Left [printf "Variable %s not in scope\n" loc]), InvalidType)
    Just a  -> (m, combineCx ar (Right Dummy), a)

semanticVerifyExpression (LookupExpression loc expr ) m ar =
  let (m2, ar2, ty2) = semanticVerifyExpression (LocationExpression loc) m ar
      (m3, ar3, ty3) = semanticVerifyExpression expr m ar
      ar4 = combineCx ar3 (case ty2 of
         DArray _ _ -> Right Dummy
         x -> Left [ printf "Type of array lookup expression incorrect -- expected array, received %s\n" (show ty2) ])
      ar5 = if ty3 == DInt then Right Dummy else Left [ printf "Type of array lookup expression incorrect -- expected %s, received %s\n" (show DInt) (show ty3) ] in
        (m3, ar5, arrayInnerType ty2)


litType :: Literal -> DataType
litType (StringLiteral s) = DString
litType (CharLiteral s) = DChar
litType (IntLiteral s) = DInt
litType (BoolLiteral s) = DBool

expectedOperandTypes :: String -> [DataType]
expectedOperandTypes op
  | op == "+"   =  [DInt]
  | op == "-"   =  [DInt]
  | op == "*"   =  [DInt]
  | op == "/"   =  [DInt]
  | op == "%"   =  [DInt]
  | op == "<"   =  [DInt]
  | op == ">"   =  [DInt]
  | op == ">="  =  [DInt]
  | op == "<="  =  [DInt]
  | op == "=="  =  [DInt, DBool]
  | op == "!="  =  [DInt, DBool]
  | op == "&&"  =  [DBool]
  | op == "||"  =  [DBool]

returnOperatorType :: String -> DataType
returnOperatorType op
  | op == "+"   =  DInt
  | op == "-"   =  DInt
  | op == "*"   =  DInt
  | op == "/"   =  DInt
  | op == "%"   =  DInt
  | op == "<"   =  DBool
  | op == ">"   =  DBool
  | op == ">="  =  DBool
  | op == "<="  =  DBool
  | op == "=="  =  DBool
  | op == "!="  =  DBool
  | op == "&&"  =  DBool
  | op == "||"  =  DBool
