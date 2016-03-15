{-# OPTIONS -Wall #-}

module SemanticChecker where

import Prelude
import Text.Printf (printf)
import ParseTypes
import qualified Data.Map as HashMap
import qualified LLIR

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

stringToVType :: Type -> LLIR.VType
stringToVType (Type n) = if n == "int" then LLIR.TInt else if n == "boolean" then LLIR.TBool else LLIR.TVoid

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

type Context = Either [IO ()] LLIR.Builder

combineCx2 :: Context -> Bool -> IO () -> Context
combineCx2 cx True _ =
  cx

combineCx2 (Right _) False io =
  Left [io]

combineCx2 (Left ls) False io =
  Left (ls ++ [io])

addInstruction :: Context -> (LLIR.Builder -> LLIR.Builder) -> Context
addInstruction (Right b) f = Right $ f b
addInstruction (Left a) _ = Left a

maybeToError :: Context -> Maybe a -> IO () -> Either [IO()] a
maybeToError _ (Just a) _ = Right a
maybeToError (Left ls) Nothing io = Left (ls ++ [io])
maybeToError (Right _) Nothing io = Left [io]

semanticVerifyProgram :: Program -> Module -> (Module, Context)
semanticVerifyProgram (Program p) m =
  let builder = LLIR.createBuilder
      (m2, d2) = foldl (\acc x -> semanticVerifyDeclaration x (fst acc) (snd acc)) (m, Right builder) p
      d3 = do
        typ <- maybeToError d2 (moduleLookup m2 "main") (printf "Program does not contain main method\n")
        combineCx2 d2 ( ( typ == (DFunction DInt []) ) || ( typ == (DFunction DBool []) ) || ( typ == (DFunction DVoid []) ) ) (printf "Main declared as incorrect type: expected %s got %s\n" (show (DFunction DVoid [])) (show typ) )
      in (m2, d3)

semanticVerifyDeclaration :: Declaration -> Module -> Context -> (Module, Context)
semanticVerifyDeclaration (Callout name) m ar =
  let (m2, success) = addToModule m DCallout name
      ar2 = combineCx2 ar success ( printf "Could not redefine callout %s\n" name )
      ar3 = addInstruction ar2 $ LLIR.createCallout name
      in (m2, ar3)

semanticVerifyDeclaration (Fields (stype, fields) ) m ar =
  let typ = stringToType stype in
    foldl ( \(m,ar) (name, size) ->
      let ar2 = case size of
             Just sz -> combineCx2 ar (sz > 0) $ printf "Array size must be greater than 0\n"
             Nothing -> ar
          (m2, success) = addToModule m (createArrayType typ size) name
          ar3 = combineCx2 ar2 success ( printf "Could not redefine variable %s\n" name )
          in (m2, ar3)
    ) (m, ar) fields

semanticVerifyDeclaration (Method rt name args body) m ar =
  let (m2, success) = addToModule m (DFunction (stringToType rt) (map (\(Argument (t,n)) -> Data n (stringToType t)) args)) name
      ar2 = combineCx2 ar success ( printf "Could not redefine function %s\n" name )
      m3 = makeChild m2 (Function $ stringToType rt)
      (m4, ar3) = foldl (\(m,ar) (Argument (t, s)) ->
        let (m2, success) = addToModule m (stringToType t) s
            ar2 = combineCx2 ar success ( printf "Could not redefine argument %s\n" s )
            in (m2, ar2)
        ) (m3, ar2) args
      ar4 = addInstruction ar3 $ LLIR.createFunction name (stringToVType rt) (map (\(Argument (t,n)) -> (stringToVType t)) args)
      block = semanticVerifyBlock body m4 ar4 in
        block

semanticVerifyBlock :: Block -> Module -> Context -> (Module, Context)
semanticVerifyBlock (Block (decls, statements)) m ar =
  let (m2, ar2) = (foldl (\acc x -> semanticVerifyDeclaration x (fst acc) (snd acc)) (m, ar) decls)
      (m3, ar3) = (foldl (\acc x -> semanticVerifyStatement x (fst acc) (snd acc)) (m2, ar2) statements)
      in (m3, ar3)

{-(map (Right . Data.ByteString.Lazy.putStrLn . encodePretty) decls ) ++ -}

semanticVerifyStatement :: Statement -> Module -> Context -> (Module, Context)
semanticVerifyStatement (Assignment (lexpr, rexpr)) m ar =
  let (m2, ar2, ty2) = semanticVerifyExpression lexpr m ar
      (m3, ar3, ty3) = semanticVerifyExpression rexpr m2 ar2
      ar4 = combineCx2 ar3 (ty2==ty3) ( printf "Type of assignment incorrect -- expected %s, received %s\n" (show ty2) (show ty3) )
      in (m3, ar4)

semanticVerifyStatement (MethodCallStatement methodCall) m ar =
  let (m2, ar2, t) = semanticVerifyExpression (MethodCallExpression methodCall) m ar
  in (m2, ar2)

semanticVerifyStatement (BreakStatement) m ar =
  let ar2 = combineCx2 ar (scopeLookup m == Just Loop) (printf "Break statements must occur in loop\n")
  in (m, ar2)

semanticVerifyStatement (ContinueStatement) m ar =
  let ar2 = combineCx2 ar (scopeLookup m == Just Loop) (printf "Continue statements must occur in loop\n")
  in (m, ar2)

semanticVerifyStatement (ReturnStatement expr) m ar =
  let (m2, ar2, typ) = case expr of
        Just exp -> semanticVerifyExpression exp m ar
        Nothing  -> (m, ar, DVoid)
      ar3 = do
        t <- maybeToError ar2 (functionTypeLookup m) (printf "Function didn't have return type")
        combineCx2 ar2 (t == typ) ( printf "Return statement should return type %s, got type %s\n" (show t) (show typ) )
      in (m, ar3)

semanticVerifyStatement (LoopStatement lCond lBody lInit lIncr) m ar =
  let (m2, ar2, ty2) = semanticVerifyExpression lCond m ar
      (m4, ar4) = case lInit of
        Just (id, expr)  ->
          let ar3 = combineCx2 ar2 ((moduleLookup m2 id)/=Nothing) (printf "Identifier in loop assignment not defined\n")
              (m3, ar4, ty3) = semanticVerifyExpression expr m2 ar3
              ar5 = combineCx2 ar4 (ty3==DInt) (printf "Initializer in loop must be of type int, got type %s\n" (show ty3))
              in (m3, ar5)
        Nothing          -> (m2, ar2)
      (m5, ar5) = case lIncr of
        Just inc  -> (m4, combineCx2 ar4 (inc > 0) (printf "Increment in for loop must be positive integer\n") )
        Nothing   -> (m4, ar4)
      m6 = makeChild m4 Loop
      (m7, ar7) = semanticVerifyBlock lBody m6 ar5
      cx1 = combineCx2 ar7 (ty2 == DBool) $ printf "Loop condition expected expression of type bool but got %s\n" (show ty2)
      in (m, cx1)

semanticVerifyStatement (IfStatement ifCond ifTrue ifFalse) m ar =
  let (m2, ar2, ty2) = semanticVerifyExpression ifCond m ar
      m3 = makeChild m Other
      (m4, ar4) = semanticVerifyBlock ifTrue m3 ar2
      (m5, ar5) = semanticVerifyBlock ifFalse m3 ar4
      ar6 = combineCx2 ar5 (ty2==DBool) $ printf "Type of conditional in ternary incorrect -- expected %s, received %s\n" (show DBool) (show ty2)
      in (m, ar6)

semanticVerifyExpression :: Expression -> Module -> Context -> (Module, Context, DataType)

-- TODO: CHECK CORRECT TYPES
semanticVerifyExpression (BinOpExpression (op, lexpr, rexpr)) m ar =
  let (m2, ar2, ty2) = semanticVerifyExpression lexpr m ar
      (m3, ar3, ty3) = semanticVerifyExpression rexpr m2 ar2
      expcTypes = expectedOperandTypes op
      returnType = returnOperatorType op
      cx1 = combineCx2 ar3 (ty2 `elem` expcTypes) $ printf "Incorrect type of left operand for op %s: %s\n" op (show ty2)
      cx2 = combineCx2 cx1 (ty3 == ty2) $ printf "Incorrect type of right operand for op %s: %s; Expected: %s\n" op (show ty3) (show ty2)
      in (m3, cx2, returnType)

semanticVerifyExpression (NegExpression expr) m ar =
  let (m2, ar2, ty2) = semanticVerifyExpression expr m ar
      ar3 = combineCx2 ar2 (ty2 == DInt) $ printf "Type of negation expression incorrect -- expected %s, received %s\n" (show DInt) (show ty2)
      in (m2, ar3, DInt)

semanticVerifyExpression (NotExpression expr) m ar =
  let (m2, ar2, ty2) = semanticVerifyExpression expr m ar
      ar3 = combineCx2 ar2 (ty2 == DBool) $ printf "Type of not expression incorrect -- expected %s, received %s\n" (show DBool) (show ty2)
      in (m2, ar3, DBool)

semanticVerifyExpression (LengthExpression expr) m ar =
  let (m2, ar2, ty2) = semanticVerifyExpression expr m ar
      ar3 = combineCx2 ar2 ((arrayInnerType ty2) /= InvalidType) $ printf "Type of length expression incorrect -- expected array, received %s\n" (show ty2)
      in (m2, ar3, DInt)

semanticVerifyExpression (LiteralExpression lit) m ar =
  (m, ar, litType lit)

semanticVerifyExpression (MethodCallExpression (name, args)) m cx =
  case (moduleLookup m name) of
    Nothing -> (m, combineCx2 cx False $ printf "Method or %s not in scope\n" name, InvalidType)
    Just (DFunction retType argTypes) ->
      let res = verifyArgs args argTypes name m cx
      in (m, res, retType)
    Just DCallout -> (m, cx, DInt)
    Just a -> (m, combineCx2 cx False $ printf "%s is not a callable method\n" name, InvalidType)

semanticVerifyExpression (CondExpression cCond cTrue cFalse) m ar =
  let (m2, ar2, ty2) = semanticVerifyExpression cCond m ar
      (m3, ar3, ty3) = semanticVerifyExpression cTrue m2 ar2
      (m4, ar4, ty4) = semanticVerifyExpression cFalse m3 ar3
      ar5 = combineCx2 ar4 (ty2 == DInt) $ printf "Type of conditional in ternary incorrect -- expected %s, received %s\n" (show DBool) (show ty2)
      ar6 = combineCx2 ar5 (ty3 == ty4)  $ printf "Types in ternary don't match %s %s\n" (show ty3) (show ty4)
      in (m4, ar6, ty3)

semanticVerifyExpression (LocationExpression loc) m ar =
  case (moduleLookup m loc) of
    Nothing -> (m, combineCx2 ar False $ printf "Variable %s not in scope\n" loc, InvalidType)
    Just a  -> (m, ar, a)

semanticVerifyExpression (LookupExpression loc expr ) m ar =
  let (m2, ar2, ty2) = semanticVerifyExpression (LocationExpression loc) m ar
      (m3, ar3, ty3) = semanticVerifyExpression expr m ar
      ar4 = combineCx2 ar3 ((arrayInnerType ty2) /= InvalidType) $ printf "Type of array lookup expression incorrect -- expected array, received %s\n" (show ty2)
      ar5 = combineCx2 ar4 (ty3 == DInt) $ printf "Type of array lookup expression incorrect -- expected %s, received %s\n" (show DInt) (show ty3)
      in (m3, ar5, arrayInnerType ty2)


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
              CalloutStringLit lit -> combineCx2 cx (DString==t) $ checkArg DString t name methodName
              CalloutExpression expr ->
                let (m2, cx2, exprType) = (semanticVerifyExpression expr m cx) in
                combineCx2 cx2 (exprType==t) $ checkArg exprType t name methodName
              ) cx l

checkArg passedType origType name methodName =
  printf "Wrong type of passed argument %s for method call %s: %s when %s is expected\n" name methodName (show passedType) (show origType)
