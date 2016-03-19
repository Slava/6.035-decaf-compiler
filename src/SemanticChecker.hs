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

arrayInnerType :: LLIR.VType -> LLIR.VType
arrayInnerType (LLIR.TArray n) = n
arrayInnerType _ = LLIR.TVoid

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

addInstruction2 :: Context -> (LLIR.Builder -> (a, LLIR.Builder) ) -> (a,Context)
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

evalToType :: (Module, Context, LLIR.ValueRef) -> (Module, Context, DataType)
evalToType (m, ar, val) = (m, ar, vTypeToType $ getType ar val)

semanticVerifyStatement :: Statement -> Module -> Context -> (Module, Context)
semanticVerifyStatement (Assignment (lexpr, rexpr)) m ar =
  case lexpr of
    LocationExpression name ->
      case (moduleLookup m name) of
        Nothing -> (m, combineCx2 ar False $ printf "Variable %s not in scope\n" name)
        Just a  ->
          let (m2, ar2, val) = semanticVerifyExpression rexpr m ar
              (val2, ar3) = addInstruction2 ar2 $ LLIR.createStore val a
              ar4 = combineCx2 ar3 ((LLIR.getDerivedTypeN $ getType ar3 a)==(getType ar3 val)) $ printf "Type of assignment into array incorrect\n"
              in (m2, ar4)
    LookupExpression name expr ->
      case (moduleLookup m name) of
        Nothing -> (m, combineCx2 ar False $ printf "Variable %s not in scope\n" name)
        Just a  ->
          let (m2, ar2, val) = semanticVerifyExpression rexpr m ar
              (m3, ar3, idx) = semanticVerifyExpression rexpr m2 ar2
              (val2, ar4) = addInstruction2 ar3 $ LLIR.createArrayStore val a idx
              ar5 = combineCx2 ar4 ((arrayInnerType $ getType ar4 a)==( getType ar4 val)) $ printf "Type of assignment into array incorrect\n"
              ar6 = combineCx2 ar5 ((getType ar4 idx)==LLIR.TInt) $ printf "Type of assignment into array incorrect\n"
              in (m3, ar6)
    _ -> (m, combineCx2 ar False $ printf "Cannot assign to non variable / non array\n")

semanticVerifyStatement (MethodCallStatement methodCall) m ar =
  let (m2, ar2, t) = evalToType $ semanticVerifyExpression (MethodCallExpression methodCall) m ar
  in (m2, ar2)

semanticVerifyStatement (BreakStatement) m ar =
  let ar2 = combineCx2 ar (scopeLookup m == Just Loop) (printf "Break statements must occur in loop\n")
  in (m, ar2)

semanticVerifyStatement (ContinueStatement) m ar =
  let ar2 = combineCx2 ar (scopeLookup m == Just Loop) (printf "Continue statements must occur in loop\n")
  in (m, ar2)

semanticVerifyStatement (ReturnStatement expr) m ar =
  let (m2, ar2, typ) = case expr of
        Just exp -> evalToType $ semanticVerifyExpression exp m ar
        Nothing  -> (m, ar, DVoid)
      ar3 = unify $ do
        t <- maybeToError ar2 (functionTypeLookup m) (printf "Function didn't have return type")
        combineCxE ar2 (t == typ) ( printf "Return statement should return type %s, got type %s\n" (show t) (show typ) )
      in (m, ar3)

semanticVerifyStatement (LoopStatement lCond lBody lInit lIncr) m ar =
  let (m2, ar2, ty2) = evalToType $ semanticVerifyExpression lCond m ar
      (m4, ar4) = case lInit of
        Just (id, expr)  ->
          let ar3 = combineCx2 ar2 ((moduleLookup m2 id)/=Nothing) (printf "Identifier in loop assignment not defined\n")
              (m3, ar4, ty3) = evalToType $ semanticVerifyExpression expr m2 ar3
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
  let (m2, ar2, v2) = semanticVerifyExpression ifCond m ar
      ty2 = getType ar2 v2
      ar3 = combineCx2 ar2 (ty2 == LLIR.TBool) $ printf "Type of conditional in if statement -- expected %s, received %s\n" (show LLIR.TBool) (show ty2)
      (block1, ar4) = addInstruction2 ar3 $ LLIR.createBlock "ifTrue"
      (block2, ar5) = addInstruction2 ar4 $ LLIR.createBlock "ifFalse"
      (val, ar6) = addInstruction2 ar5 $ LLIR.createCondBranch v2 block1 block2
      (blockMerge, ar7) = addInstruction2 ar6 $ LLIR.createBlock "ifMerge"
      ar8 = addInstruction ar7 $ LLIR.setInsertionPoint block1
      (_, ar9) = semanticVerifyBlock ifTrue m2 ar8
      (_, ar10) = addInstruction2 ar9 $ LLIR.createUncondBranch blockMerge
      ar11 = addInstruction ar10 $ LLIR.setInsertionPoint block2
      (_, ar12) = semanticVerifyBlock ifFalse m2 ar11
      (_, ar13) = addInstruction2 ar12 $ LLIR.createUncondBranch blockMerge
      ar14 = addInstruction ar13 $ LLIR.setInsertionPoint blockMerge
      in (m, ar14)

semanticVerifyExpression :: Expression -> Module -> Context -> (Module, Context, LLIR.ValueRef)

semanticVerifyExpression (BinOpExpression (op, lexpr, rexpr)) m ar =
  case op of
    "&&" ->
      let (_, ar2, v2) = semanticVerifyExpression lexpr m ar
          (_, ar3, v3) = semanticVerifyExpression rexpr m ar2
          ty2 = getType ar3 v2
          ty3 = getType ar3 v3
          cx1 = combineCx2 ar3 (ty2 == LLIR.TBool) $ printf "Incorrect type of left operand for op %s: %s; Expected: boolean\n" op (show ty2)
          cx2 = combineCx2 cx1 (ty3 == LLIR.TBool) $ printf "Incorrect type of right operand for op %s: %s; Expected: boolean\n" op (show ty3)
          in semanticVerifyExpression (CondExpression lexpr rexpr (LiteralExpression $ BoolLiteral False)) m cx2
    "||" ->
      let (_, ar2, v2) = semanticVerifyExpression lexpr m ar
          (_, ar3, v3) = semanticVerifyExpression rexpr m ar2
          ty2 = getType ar3 v2
          ty3 = getType ar3 v3
          cx1 = combineCx2 ar3 (ty2 == LLIR.TBool) $ printf "Incorrect type of left operand for op %s: %s; Expected: boolean\n" op (show ty2)
          cx2 = combineCx2 cx1 (ty3 == LLIR.TBool) $ printf "Incorrect type of right operand for op %s: %s; Expected: boolean\n" op (show ty3)
          in semanticVerifyExpression (CondExpression lexpr (LiteralExpression $ BoolLiteral True) rexpr) m cx2
    _    ->
      let (m2, ar2, v2) = semanticVerifyExpression lexpr m ar
          (m3, ar3, v3) = semanticVerifyExpression rexpr m2 ar2
          ty2 = getType ar3 v2
          ty3 = getType ar3 v3
          expcTypes = expectedOperandTypes op
          cx1 = combineCx2 ar3 (ty2 `elem` expcTypes) $ printf "Incorrect type of left operand for op %s: %s\n" op (show ty2)
          cx2 = combineCx2 cx1 (ty3 == ty2) $ printf "Incorrect type of right operand for op %s: %s; Expected: %s\n" op (show ty3) (show ty2)
          (val, cx3) = addInstruction2 cx2 $ LLIR.createBinOp op v2 v3
          in (m3, cx3, val)

semanticVerifyExpression (NegExpression expr) m ar =
  let (m2, ar2, v2) = semanticVerifyExpression expr m ar
      ty2 = getType ar2 v2
      ar3 = combineCx2 ar2 (ty2 == LLIR.TInt) $ printf "Type of negation expression incorrect -- expected %s, received %s\n" (show DInt) (show ty2)
      (val, ar4) = addInstruction2 ar3 $ LLIR.createUnaryOp "-" v2
      in (m2, ar4, val)

semanticVerifyExpression (NotExpression expr) m ar =
  let (m2, ar2, v2) = semanticVerifyExpression expr m ar
      ty2 = getType ar2 v2
      ar3 = combineCx2 ar2 (ty2 == LLIR.TBool) $ printf "Type of not expression incorrect -- expected %s, received %s\n" (show DBool) (show ty2)
      (val, ar4) = addInstruction2 ar3 $ LLIR.createUnaryOp "!" v2
      in (m2, ar4, v2)

semanticVerifyExpression (LengthExpression expr) m ar =
  let (m2, ar2, v2) = semanticVerifyExpression expr m ar
      ty2 = getType ar2 v2
      ar3 = combineCx2 ar2 ((arrayInnerType ty2) /= LLIR.TBool) $ printf "Type of length expression incorrect -- expected array, received %s\n" (show ty2)
      (val, ar4) = addInstruction2 ar3 $ LLIR.createArrayLen v2
      in (m2, ar4, val)

semanticVerifyExpression (LiteralExpression lit) m ar =
  (m, ar, createLit lit)

semanticVerifyExpression (MethodCallExpression (name, args)) m cx =
  case (moduleLookup m name) of
    Nothing -> (m, combineCx2 cx False $ printf "Method or %s not in scope\n" name, LLIR.InstRef "")
    Just vref ->
      case getType cx vref of
        (LLIR.TFunction retType argTypes) ->
          let res = verifyArgs args (map (\x -> Data "c" $ vTypeToType x) argTypes) name m cx
              (m2, res2, args2) = foldl (\(m, cx, l) x -> case x of
                                      CalloutExpression x -> let (m2, cx2, val) = semanticVerifyExpression x m cx in (m2, cx2, l ++ [val])
                                      CalloutStringLit x -> (m, cx, l ++ [LLIR.ConstString x])) (m, res, []) args
              (val, res3) = addInstruction2 res2 $ LLIR.createMethodCall name args2
            in (m2, res3, val)
        LLIR.TCallout ->
          let res = cx
              (m2, res2, args2) = foldl (\(m, cx, l) x -> case x of
                                      CalloutExpression x -> let (m2, cx2, val) = semanticVerifyExpression x m cx in (m2, cx2, l ++ [val])
                                      CalloutStringLit x -> (m, cx, l ++ [LLIR.ConstString x])) (m, res, []) args
              (val, res3) = addInstruction2 res2 $ LLIR.createCalloutCall name args2
            in (m2, res3, val)
        a -> (m, combineCx2 cx False $ printf "%s is not a callable method\n" name, LLIR.InstRef "")

semanticVerifyExpression (CondExpression cCond cTrue cFalse) m ar =
  let (m2, ar2, v2) = semanticVerifyExpression cCond m ar
      (_, ar3, tv3) = semanticVerifyExpression cTrue m2 ar2
      (_, ar4, tv4) = semanticVerifyExpression cFalse m2 ar3
      ty2 = getType ar4 v2
      ty3 = getType ar4 tv3
      ty4 = getType ar4 tv4
      ar5 = combineCx2 ar4 (ty2 == LLIR.TBool) $ printf "Type of conditional in ternary incorrect -- expected %s, received %s\n" (show DBool) (show ty2)
      ar6 = combineCx2 ar5 (ty3 == ty4)  $ printf "Types in ternary don't match %s %s\n" (show ty3) (show ty4)
      (block1, ar7) = addInstruction2 ar6 $ LLIR.createBlock "condTrue"
      (block2, ar8) = addInstruction2 ar7 $ LLIR.createBlock "condFalse"
      (ptr, ar9) = addInstruction2 ar8 $ LLIR.createAlloca ty3 Nothing
      (val, ar10) = addInstruction2 ar9 $ LLIR.createCondBranch v2 block1 block2
      (blockMerge, ar11) = addInstruction2 ar10 $ LLIR.createBlock "condMerge"
      ar12 = addInstruction ar11 $ LLIR.setInsertionPoint block1
      (m3, ar13, v3) = semanticVerifyExpression cTrue m2 ar12
      (_, ar14) = addInstruction2 ar13 $ LLIR.createStore v3 ptr
      (_, ar15) = addInstruction2 ar14 $ LLIR.createUncondBranch blockMerge
      ar16 = addInstruction ar15 $ LLIR.setInsertionPoint block2
      (m4, ar17, v4) = semanticVerifyExpression cFalse m3 ar16
      (_, ar18) = addInstruction2 ar17 $ LLIR.createStore v4 ptr
      (_, ar19) = addInstruction2 ar18 $ LLIR.createUncondBranch blockMerge
      ar20 = addInstruction ar19 $ LLIR.setInsertionPoint blockMerge
      (val2, ar21) = addInstruction2 ar20 $ LLIR.createLookup ptr
      in (m4, ar21, val2)

semanticVerifyExpression (LocationExpression loc) m ar =
  case (moduleLookup m loc) of
    Nothing -> (m, combineCx2 ar False $ printf "Variable %s not in scope\n" loc, LLIR.InstRef "")
    Just a  ->
      let (val, ar2) = addInstruction2 ar $ LLIR.createLookup a
          in (m, ar2, val)

semanticVerifyExpression (LookupExpression loc expr ) m ar =
  let (m2, ar2, v2) = semanticVerifyExpression (LocationExpression loc) m ar
      (m3, ar3, v3) = semanticVerifyExpression expr m ar
      ty2 = getType ar3 v2
      ty3 = getType ar3 v3
      ar4 = combineCx2 ar3 ((arrayInnerType ty2) /= LLIR.TVoid) $ printf "Type of array lookup expression incorrect -- expected array, received %s\n" (show ty2)
      ar5 = combineCx2 ar4 (ty3 == LLIR.TInt) $ printf "Type of array lookup expression incorrect -- expected %s, received %s\n" (show DInt) (show ty3)
      (val, ar6) = addInstruction2 ar5 $ LLIR.createArrayLookup v2 v3
      in (m3, ar6, val)

createLit :: Literal -> LLIR.ValueRef
createLit (StringLiteral s) = LLIR.ConstString s
createLit (IntLiteral s) = LLIR.ConstInt s
createLit (BoolLiteral s) = LLIR.ConstBool s

expectedOperandTypes :: String -> [LLIR.VType]
expectedOperandTypes op
  | op == "+"   =  [LLIR.TInt]
  | op == "-"   =  [LLIR.TInt]
  | op == "*"   =  [LLIR.TInt]
  | op == "/"   =  [LLIR.TInt]
  | op == "%"   =  [LLIR.TInt]
  | op == "<"   =  [LLIR.TInt]
  | op == ">"   =  [LLIR.TInt]
  | op == ">="  =  [LLIR.TInt]
  | op == "<="  =  [LLIR.TInt]
  | op == "=="  =  [LLIR.TInt, LLIR.TBool]
  | op == "!="  =  [LLIR.TInt, LLIR.TBool]
  | op == "&&"  =  [LLIR.TBool]
  | op == "||"  =  [LLIR.TBool]

verifyArgs :: [CalloutArg] -> [Data] -> String -> Module -> Context -> Context
verifyArgs args argTypes methodName m cx =
  unify $ do
    combineCxE cx ((length args) == (length argTypes)) $ printf "Wrong number of arguments passed: %d instead of %d for method %s\n" (length args) (length argTypes) methodName
    let l = zip args argTypes
    return $ foldl (\cx (arg, (Data name t)) -> case arg of
              CalloutStringLit lit -> combineCx2 cx (DString==t) $ checkArg DString t name methodName
              CalloutExpression expr ->
                let (m2, cx2, exprType) = (evalToType $ semanticVerifyExpression expr m cx) in
                combineCx2 cx2 (exprType==t) $ checkArg exprType t name methodName
              ) cx l


checkArg passedType origType name methodName =
  printf "Wrong type of passed argument %s for method call %s: %s when %s is expected\n" name methodName (show passedType) (show origType)
