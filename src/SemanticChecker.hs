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
              | DFunction DataType [Data]
              | DVoid
              | DString
              | DChar
              | InvalidType
                deriving (Eq, Show);

data ScopeType = Loop
               | Function DataType
               | Other
                 deriving (Eq, Show);

data Data = Data {
  vName :: String,
  vType :: DataType
} deriving (Eq, Show)

data Module = Module {
  parent     :: Maybe Module,
  lookup     :: HashMap.Map String Data,
  scopeType  :: ScopeType
} deriving (Eq, Show)

addToModule :: Module -> DataType -> String -> (Module, Bool {- if failed -} )
addToModule (Module parent lookup scopeType) dtype dname =
  ( Module parent ( HashMap.insert dname (Data dname dtype) lookup ) scopeType , not $ HashMap.member dname lookup )

moduleLookup :: Module -> String -> Maybe DataType
moduleLookup (Module parent m _) s =
  case HashMap.lookup s m of
    Just (Data _ a) -> Just a
    Nothing -> case parent of
      Just a -> moduleLookup a s
      Nothing -> Nothing

scopeLookup :: Module -> Maybe ScopeType
scopeLookup (Module parent _ scopeType) =
  case scopeType of
    Loop -> Just Loop
    _    -> case parent of
      Just a  -> scopeLookup a
      Nothing -> Nothing

functionTypeLookup :: Module -> Maybe DataType
functionTypeLookup (Module parent _ scopeType) =
    case scopeType of
      Function t -> Just t
      _          -> case parent of
        Just a  -> functionTypeLookup a
        Nothing -> Nothing

makeChild :: Module -> ScopeType -> Module
makeChild m s = Module (Just m) HashMap.empty s

stringToType :: Type -> DataType
stringToType (Type n) = if n == "int" then DInt else if n == "boolean" then DBool else if n == "void" then DVoid else InvalidType

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
type Context = Either [IO ()] Dummy

combineCx :: Context -> Context -> Context
combineCx cx (Right Dummy) =
  cx

combineCx (Right Dummy) newCx =
  newCx

combineCx (Left ls) (Left newLs) =
  Left (ls ++ newLs)

debug :: [IO ()] -> [IO ()]
--debug a = a
debug a = []

semanticVerifyProgram :: Program -> Module -> Context -> (Module, Context)
semanticVerifyProgram (Program p) m ar =
  let (m2, d2) = foldl (\acc x -> semanticVerifyDeclaration x (fst acc) (snd acc)) (m, ar) p
      val = moduleLookup m2 "main"
      d3 = combineCx d2 (case val of
              Nothing -> Left [printf "Program does not contain main method\n"]
              Just typ -> if ( typ == (DFunction DInt []) ) || ( typ == (DFunction DBool []) ) || ( typ == (DFunction DVoid []) ) then Right Dummy else Left [printf "Main declared as incorrect type: expected %s got %s\n" (show (DFunction DVoid [])) (show typ)]) in
      (m2, d3)

semanticVerifyDeclaration :: Declaration -> Module -> Context -> (Module, Context)
semanticVerifyDeclaration (Callout name) m ar =
  let (m2, success) = addToModule m DCallout name
      res = (if success then Right Dummy else Left [ printf "Could not redefine callout %s\n" name ] )
      ar2 = (combineCx ar res) in
      (m2, ar2)

semanticVerifyDeclaration (Fields (stype, fields) ) m ar =
  let typ = stringToType stype in
    foldl ( \(m,ar) (name, size) ->
      let ar2 = case size of
             Just sz -> if sz > 0 then ar else (combineCx ar (Left [printf "Array size must be greater than 0\n"])) 
             Nothing -> ar
          (m2, success) = addToModule m (createArrayType typ size) name
          res = (if success then Right Dummy else Left [ printf "Could not redefine variable %s\n" name ] )
          ar3 = (combineCx ar2 res) in
          (m2, ar3)
    ) (m, ar) fields

semanticVerifyDeclaration (Method rt name args body) m ar =
  let (m2, success) = addToModule m (DFunction (stringToType rt) (map (\(Argument (t,n)) -> Data n (stringToType t)) args)) name
      ar2 = if success then (combineCx ar (Right Dummy)) else (combineCx ar (Left [ printf "Could not redefine function %s\n" name ]))
      m3 = makeChild m2 (Function $ stringToType rt) 
      (m4, ar3) = foldl (\(m,ar) (Argument (t, s)) ->
        let (m2, success) = addToModule m (stringToType t) s
            res = (if success then Right Dummy else Left [ printf "Could not redefine argument %s\n" s ] )
            ar2 = combineCx ar res in
            (m2, ar2)
        ) (m3, ar2) args
      block = semanticVerifyBlock body m4 ar3 in
        block

semanticVerifyBlock :: Block -> Module -> Context -> (Module, Context)
semanticVerifyBlock (Block (decls, statements)) m ar =
  let (m2, ar2) = (foldl (\acc x -> semanticVerifyDeclaration x (fst acc) (snd acc)) (m, ar) decls) in
    let (m3, ar3) = (foldl (\acc x -> semanticVerifyStatement x (fst acc) (snd acc)) (m2, ar2) statements) in
      (m3, ar3)

{-(map (Right . Data.ByteString.Lazy.putStrLn . encodePretty) decls ) ++ -}

semanticVerifyStatement :: Statement -> Module -> Context -> (Module, Context)
semanticVerifyStatement (Assignment (lexpr, rexpr)) m ar =
  let (m2, ar2, ty2) = semanticVerifyExpression lexpr m ar
      (m3, ar3, ty3) = semanticVerifyExpression rexpr m2 ar2
      res = if ty2 == ty3 then (Right Dummy) else Left [printf "Type of assignment incorrect -- expected %s, received %s\n" (show ty2) (show ty3) ]
      ar4 = combineCx ar3 res in
        (m3, ar4)

semanticVerifyStatement (MethodCallStatement methodCall) m ar =
 let (m2, ar2, t) = semanticVerifyExpression (MethodCallExpression methodCall) m ar in
 (m2, ar2)

semanticVerifyStatement (BreakStatement) m ar =
  -- TODO: should check that the break statement is within a loop
  let res = if scopeLookup m == Just Loop then (Right Dummy) else Left [printf "Break statements must occur in loop\n"]
      ar2 = combineCx ar res in
        (m, ar2)

semanticVerifyStatement (ContinueStatement) m ar =
  -- TODO: should check that the break statement is within a loop
  let res = if scopeLookup m == Just Loop then (Right Dummy) else Left [printf "Continue statements must occur in loop\n"]
      ar2 = combineCx ar res in
        (m, ar2)

semanticVerifyStatement (ReturnStatement expr) m ar =
  let (m2, ar2, typ) = case expr of
        Just exp -> semanticVerifyExpression exp m ar 
        Nothing  -> (m, ar, DVoid) 
      ar3 = case functionTypeLookup m of
        Just t -> if t == typ then (Right Dummy) else Left [printf "Return statement should return type %s, got type %s\n" (show t) (show typ) ]
        Nothing -> Left [printf "Function didn't have return type\n"]
      cx1 = combineCx ar2 ar3 in
        (m, cx1)

semanticVerifyStatement (LoopStatement lCond lBody lInit lIncr) m ar =
  let (m2, ar2, ty2) = semanticVerifyExpression lCond m ar
      (m4, ar4) = case lInit of
        Just (id, expr)  ->
          case (moduleLookup m2 id) of
            Just _  ->
              let (m3, ar3, ty3) = semanticVerifyExpression expr m2 ar2 in
                (m3, combineCx ar3 $ if ty3 == DInt then Right Dummy else Left [ printf "Initializer in loop must be of type int, got type %s\n" (show ty3) ])
            Nothing -> (m2, combineCx ar2 $ Left [ printf "Identifier in loop assignment not defined\n" ])
        Nothing          -> (m2, ar2)
      (m5, ar5) = case lIncr of
        Just inc  -> (m4, combineCx ar4 $ if inc > 0 then Right Dummy else Left [ printf "Increment in for loop must be positive integer\n" ])
        Nothing   -> (m4, ar4)
      m6 = makeChild m4 Loop
      (m7, ar7) = semanticVerifyBlock lBody m6 ar5
      cx1 = combineCx ar7 $ if ty2 == DBool then Right Dummy else Left [ printf "Loop condition expected expression of type bool but got %s\n" (show ty2) ] in
        (m, cx1)

semanticVerifyStatement (IfStatement ifCond ifTrue ifFalse) m ar =
  let (m2, ar2, ty2) = semanticVerifyExpression ifCond m ar
      m3 = makeChild m Other
      (m4, ar4) = semanticVerifyBlock ifTrue m3 ar2
      (m5, ar5) = semanticVerifyBlock ifFalse m3 ar4
      res = if ty2 == DBool then Right Dummy else Left [ printf "Type of conditional in ternary incorrect -- expected %s, received %s\n" (show DBool) (show ty2) ]
      ar6 = combineCx ar5 res in
        (m, ar6)

semanticVerifyExpression :: Expression -> Module -> Context -> (Module, Context, DataType)

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

semanticVerifyExpression (MethodCallExpression (name, args)) m cx =
  case (moduleLookup m name) of
    Nothing -> (m, combineCx cx (Left [printf "Method or %s not in scope\n" name]), InvalidType)
    Just (DFunction retType argTypes) ->
      let res = verifyArgs args argTypes name m cx in
      (m, res, retType)
    Just DCallout -> (m, cx, DInt)
    Just a -> (m, combineCx cx (Left [printf "%s is not a callable method\n" name]), InvalidType)

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
        (m3, combineCx ar4 ar5, arrayInnerType ty2)


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

verifyArgs :: [CalloutArg] -> [Data] -> String -> Module -> Context -> Context
verifyArgs args argTypes methodName m cx =
  if (length args) /= (length argTypes) then
    Left [(printf "Wrong number of arguments passed: %d instead of %d for method %s\n" (length args) (length argTypes) methodName)]
  else
    let l = zip args argTypes in
    foldl (\cx (arg, (Data name t)) -> case arg of
              CalloutStringLit lit -> combineCx cx (checkArg DString t name methodName)
              CalloutExpression expr ->
                let (m2, cx2, exprType) = (semanticVerifyExpression expr m cx) in
                combineCx cx2 (checkArg exprType t name methodName)
              ) cx l

checkArg passedType origType name methodName =
  if passedType == origType then
    Right Dummy
  else
    Left [(printf "Wrong type of passed argument %s for method call %s: %s when %s is expected\n" name methodName (show passedType) (show origType))]
