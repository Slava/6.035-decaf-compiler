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


typeToVType :: DataType -> LLIR.VType
typeToVType DCallout        = LLIR.TCallout
typeToVType DBool           = LLIR.TBool
typeToVType DInt            = LLIR.TInt
typeToVType (DArray a _ )   = LLIR.TArray $ typeToVType a
typeToVType (DFunction a b) = LLIR.TFunction ( typeToVType a ) ( map (\(Data _ a) -> typeToVType a ) b )
typeToVType DVoid           = LLIR.TVoid
typeToVType DString         = LLIR.TString
typeToVType DChar           = LLIR.TVoid
typeToVType InvalidType     = LLIR.TVoid

{-
data VType            = TInt
                      | TBool
                      | TString
                      | TFunction VType [VType]
                      | TVoid
                      | TCallout
                      | TArray VType
                      | TPointer VType
-}
vTypeToType :: LLIR.VType -> DataType
vTypeToType LLIR.TCallout        = DCallout
vTypeToType LLIR.TBool           = DBool
vTypeToType LLIR.TInt            = DInt
vTypeToType LLIR.TString         = DString
vTypeToType LLIR.TVoid           = DVoid
vTypeToType (LLIR.TArray a )   = DArray (vTypeToType a) Nothing
vTypeToType (LLIR.TFunction a b) = DFunction ( vTypeToType a ) ( map (\a -> Data "str" $ vTypeToType a ) b )
vTypeToType (LLIR.TPointer _)       = InvalidType

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
  lookup     :: HashMap.Map String LLIR.ValueRef,
  scopeType  :: ScopeType
} deriving (Eq, Show)

addToModule :: Module -> LLIR.ValueRef -> String -> (Module, Bool {- if failed -} )
addToModule (Module parent lookup scopeType) dtype dname =
  ( Module parent ( HashMap.insert dname dtype lookup ) scopeType , not $ HashMap.member dname lookup )

moduleLookup :: Module -> String -> Maybe LLIR.ValueRef
moduleLookup (Module parent m _) s =
  case HashMap.lookup s m of
    Just a -> Just a
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

data Context = Context {
  contextErrors  :: [IO ()],
  contextBuilder ::LLIR.Builder
}

getType :: Context -> (LLIR.ValueRef) -> LLIR.VType
getType (Context errs builder) vref = LLIR.getType builder vref

combineCx2 :: Context -> Bool -> IO () -> Context
combineCx2 cx True _ = cx
combineCx2 (Context ios bld) False io = Context (ios ++ [io]) bld

combineCxE :: Context -> Bool -> IO () -> Either Context Context
combineCxE cx True _ = Right cx
combineCxE (Context ios bld) False io = Left $ Context (ios ++ [io]) bld

unify :: Either Context Context -> Context
unify (Left a)  = a
unify (Right a) = a

addDebug :: Context -> (IO() ) -> Context
addDebug (Context ios b) io = Context ios $ LLIR.addDebug b io

addInstruction :: Context -> (LLIR.Builder -> LLIR.Builder) -> Context
addInstruction (Context ios b) f =
  let builder = b--LLIR.addDebug b $ printf "adding instruction \n"
      in (Context ios $ f builder)

addInstruction2 :: Context -> (LLIR.Builder -> (LLIR.ValueRef, LLIR.Builder) ) -> (LLIR.ValueRef,Context)
addInstruction2 (Context ios b) f =
  let (ref, b2) = f b
      builder = b2--LLIR.addDebug b2 $ printf "adding instruction2\n"
      in (ref, (Context ios builder))

maybeToError :: Context -> Maybe a -> IO () -> Either Context a
maybeToError (Context ios b) Nothing io = Left $ Context (ios++[io]) b
maybeToError (Context ios b) (Just a) _ = Right a

semanticVerifyProgram :: Program -> Module -> (Module, Context)
semanticVerifyProgram (Program p) m =
  let builder = LLIR.createBuilder
      (m2, d2) = foldl (\acc x -> semanticVerifyDeclaration x (fst acc) (snd acc)) (m, Context [] builder) p
      d3 = unify $ do
        func <- maybeToError d2 (moduleLookup m2 "main") (printf "Program does not contain main method\n")
        let typ = getType d2 func
        combineCxE d2 ( ( typ == (LLIR.TFunction LLIR.TInt []) ) || ( typ == (LLIR.TFunction LLIR.TBool []) ) || ( typ == (LLIR.TFunction LLIR.TVoid []) ) ) (printf "Main declared as incorrect type: expected %s got %s\n" (show (LLIR.TFunction LLIR.TVoid [])) (show typ) )
      in (m2, d3)

semanticVerifyDeclaration :: Declaration -> Module -> Context -> (Module, Context)
semanticVerifyDeclaration (Callout name) m ar =
  let (m2, success) = addToModule m (LLIR.CalloutRef name) name
      ar2 = combineCx2 ar success ( printf "Could not redefine callout %s\n" name )
      ar3 = addInstruction ar2 $ LLIR.createCallout name
      in (m2, ar3)

semanticVerifyDeclaration (Fields (stype, fields) ) m ar =
  let typ = stringToType stype
      (mf, arf) = foldl ( \(m,ar) (name, size) ->
          let ar2 = case size of
                 Just sz -> combineCx2 ar (sz > 0) $ printf "Array size must be greater than 0\n"
                 Nothing -> ar
              addFunc = if (scopeType m)==Other then LLIR.createGlobal name else LLIR.createAlloca
              (val, ar3) = addInstruction2 ar2 $ addFunc (typeToVType typ) size
              (m2, success) = addToModule m val name
              ar4 = combineCx2 ar3 success ( printf "Could not redefine variable %s\n" name )
              --ar5 = addDebug ar4 $ printf "adding field?\n"
              in (m2, ar4)
        ) (m, ar) fields
      in (mf, arf)

semanticVerifyDeclaration (Method rt name args body) m ar =
  let (m2, success) = addToModule m (LLIR.FunctionRef name) name
      ar2 = combineCx2 ar success ( printf "Could not redefine function %s\n" name )
      m3 = makeChild m2 (Function $ stringToType rt)
      (_,m4, ar3) = foldl (\(idx,m,ar) (Argument (t, s)) ->
        let (m2, success) = addToModule m (LLIR.ArgRef idx name) s
            ar2 = combineCx2 ar success ( printf "Could not redefine argument %s\n" s )
            in (idx+1,m2, ar2)
        ) (0,m3, ar2) args
      ar4 = addInstruction ar3 $ LLIR.createFunction name (stringToVType rt) (map (\(Argument (t,n)) -> (stringToVType t)) args)
      ar5 = addInstruction ar4 $ LLIR.setInsertionPoint (name,"entry")
      block = semanticVerifyBlock body m4 ar5 in
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
      ar3 = unify $ do
        t <- maybeToError ar2 (functionTypeLookup m) (printf "Function didn't have return type")
        combineCxE ar2 (t == typ) ( printf "Return statement should return type %s, got type %s\n" (show t) (show typ) )
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
    Just vref ->
      case getType cx vref of
        (LLIR.TFunction retType argTypes) ->
          let res = verifyArgs args (map (\x -> Data "c" $ vTypeToType x) argTypes) name m cx
            in (m, res, vTypeToType retType)
        LLIR.TCallout -> (m, cx, DInt)
        a -> (m, combineCx2 cx False $ printf "%s is not a callable method\n" name, InvalidType)

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
    Just a  -> (m, ar, vTypeToType $ LLIR.getDerivedTypeN $ getType ar a)

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
  unify $ do
    combineCxE cx ((length args) == (length argTypes)) $ printf "Wrong number of arguments passed: %d instead of %d for method %s\n" (length args) (length argTypes) methodName
    let l = zip args argTypes
    return $ foldl (\cx (arg, (Data name t)) -> case arg of
              CalloutStringLit lit -> combineCx2 cx (DString==t) $ checkArg DString t name methodName
              CalloutExpression expr ->
                let (m2, cx2, exprType) = (semanticVerifyExpression expr m cx) in
                combineCx2 cx2 (exprType==t) $ checkArg exprType t name methodName
              ) cx l


checkArg passedType origType name methodName =
  printf "Wrong type of passed argument %s for method call %s: %s when %s is expected\n" name methodName (show passedType) (show origType)
