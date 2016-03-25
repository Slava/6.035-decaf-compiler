{-# OPTIONS -Wall #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module LLIR where

-- Imports
import Prelude
import Data.List
import Text.Printf (printf)
--import ParseTypes
import qualified Data.Map as HashMap


data VType            = TInt
                      | TBool
                      | TString
                      | TFunction VType [VType]
                      | TVoid
                      | TCallout
                      | TArray VType
                      | TPointer VType
                      deriving (Eq, Show);

{- in bytes -}
typeSize :: VType -> Int
typeSize op = case op of
  TInt       -> 8
  TBool      -> 8 -- todo fix to 1
  TString    -> 8 -- ptr
  TPointer _ -> 8 -- ptr
  TFunction _ _ -> 8 -- ptr
  TVoid      -> 0 -- ptr
  TCallout   -> 8 -- ptr
  TArray x   -> 8 -- ptr


getDerivedType :: VType -> Maybe VType
getDerivedType a =
  case a of
    TPointer ty -> Just ty
    _ -> Nothing

getDerivedTypeN :: VType -> VType
getDerivedTypeN a =
  case a of
    TPointer ty -> ty
    _ -> TVoid

getArrayType :: VType -> Maybe VType
getArrayType a =
  case a of
    TArray ty -> Just ty
    _ -> Nothing

class Namable a where
  getName :: a -> String

class Locationable a where
  setInsertionPoint :: a -> Builder -> Builder

class Value a where
  getType :: Builder -> a -> VType

data ValueRef = InstRef String
              | ConstInt Integer
              | ConstString String
              | ConstBool Bool
              | CalloutRef String
              | GlobalRef String
              | FunctionRef String
              | ArgRef Int String
  deriving(Eq, Show);

getReferenceName :: ValueRef -> String
getReferenceName (InstRef a) = a
getReferenceName (ConstInt _) = "!cint"
getReferenceName (ConstString _) = "!cstring"
getReferenceName (ConstBool _) = "!cbool"
getReferenceName (CalloutRef a) = a
getReferenceName (GlobalRef a) = a
getReferenceName (FunctionRef a) = a
getReferenceName (ArgRef _ _) = "!argref"

instance Value ValueRef where
  getType builder (InstRef str) =
    case getInstruction builder str of
      Just inst -> getType builder inst
      Nothing -> TVoid
  getType _ (ConstInt _) = TInt
  getType _ (ConstBool _) = TBool
  getType builder (GlobalRef str) =
    case HashMap.lookup str (globals $ pmod builder) of
      Just (a,Nothing) -> TPointer a
      Just (a,Just _) -> TArray a
      Nothing -> TVoid

  getType _ (ConstString _) = TString
  getType _ (CalloutRef _) = TCallout
  getType builder (FunctionRef str) =
    case getFunction builder str of
      Just func -> getType builder func
      Nothing -> TVoid
  getType builder (ArgRef idx str) =
    case do
      func <- getFunction builder str
      let args :: [VType] = arguments func
      if idx < length args then Just $ args !! idx else Nothing
    of
      Just t -> t
      Nothing -> TVoid

data VInstruction = VUnOp {- name -} String {- operand -} String {- argument name -} ValueRef
                  | VBinOp {- name -} String {- operand -} String {- argument name -} ValueRef ValueRef
                  | VStore  String {- tostore -} ValueRef {- location -} ValueRef
                  | VLookup String ValueRef
                  | VAllocation String {- type -} VType {- if array -} (Maybe Int)
                  | VArrayStore String {- tostore -} ValueRef {- array -} ValueRef {- idx -} ValueRef
                  | VArrayLookup String {- array -} ValueRef {- idx -} ValueRef
                  | VArrayLen String ValueRef
                  | VReturn String (Maybe ValueRef)
                  | VCondBranch String {-cond-} ValueRef {-true-} String {-false-} String
                  | VUnreachable String
                  | VUncondBranch String String
                  | VMethodCall String {- is-callout? -} Bool {- fname -} String {- args -} [ValueRef]
  deriving (Eq, Show);

instance Namable VInstruction where
  getName (VUnOp name _ _ ) = name
  getName (VBinOp name _ _ _ ) = name
  getName (VStore name _ _) = name
  getName (VLookup name _) = name
  getName (VAllocation name _ _) = name
  getName (VArrayStore name _ _ _) = name
  getName (VArrayLookup name _ _) = name
  getName (VArrayLen name _) = name
  getName (VReturn name _) = name
  getName (VCondBranch name _ _ _) = name
  getName (VUncondBranch name _) = name
  getName (VMethodCall name _ _ _) = name
  getName (VUnreachable name ) = name


instance Value VInstruction where
  getType _ (VUnOp _ op _ )
    | op == "-"   =  TInt
    | op == "!"   =  TBool
  getType _ (VBinOp _ op _ _)
    | op == "+"   =  TInt
    | op == "-"   =  TInt
    | op == "*"   =  TInt
    | op == "/"   =  TInt
    | op == "%"   =  TInt
    | op == "<"   =  TBool
    | op == ">"   =  TBool
    | op == ">="  =  TBool
    | op == "<="  =  TBool
    | op == "u<"   =  TBool
    | op == "u>"   =  TBool
    | op == "u>="  =  TBool
    | op == "u<="  =  TBool
    | op == "=="  =  TBool
    | op == "!="  =  TBool
    | op == "&"  =  TBool
    | op == "|"  =  TBool
  getType _ (VUnreachable _) = TVoid
  getType _ (VStore _ toStore _) = TVoid
  getType b (VLookup _ toLookup) =
    case getDerivedType $ getType b toLookup of
      Just a -> a
      Nothing -> TVoid
  getType _ (VAllocation _ a Nothing) = TPointer a
  getType _ (VAllocation _ a (Just _) ) = TArray a

  getType _ (VArrayStore _ _ _ _) = TVoid
  getType b (VArrayLookup _ toLookup _ ) =
    case getArrayType $ getType b toLookup of
      Just a -> a
      Nothing -> TVoid

  getType _ (VArrayLen _ _ ) = TInt
  getType _ (VReturn _ _ ) = TVoid
  getType _ (VCondBranch _ _ _ _) = TVoid
  getType _ (VUncondBranch _ _) = TVoid
  getType _ (VMethodCall _ True _ _) = TInt
  getType b (VMethodCall _ False name _) =
    case HashMap.lookup name $ (functions . pmod) b of
      Nothing -> TVoid
      Just a -> returnType a

data VCallout = VCallout String
  deriving(Eq, Show);

instance Value VCallout where
  getType _ _ = TCallout

instance Namable VCallout where
  getName (VCallout name) = name

data VFunction    = VFunction {
  functionName      :: String,
  returnType        :: VType,
  arguments         :: [VType],
  functionInstructions :: HashMap.Map String VInstruction,
  blocks    :: HashMap.Map String VBlock,
  blockOrder :: [String]
} deriving (Eq);

blockToString :: (HashMap.Map String VInstruction) -> VBlock -> String
blockToString hm (VBlock _ name instr) =
  " " ++ name ++ ":\n" ++ (foldl (\acc x -> acc ++ "    " ++ (
        case HashMap.lookup x hm of
          Just a -> x ++ " = " ++ (show a) ++ "\n"
          Nothing -> "INVALID_INST("++name++")\n"
        )) "" instr)

getValues :: HashMap.Map String VBlock -> [String] -> [VBlock]
getValues hm [] = []
getValues hm (idx:keys) =
  let lk :: Maybe VBlock = HashMap.lookup idx hm
      val :: [VBlock] = case lk of
        Nothing -> []
        Just a -> [a]
      in val ++ ( getValues hm keys )

instance Show VFunction where
  show (VFunction functionName returnType arguments functionInstructions blocks blockOrder) =
    "def " ++ (show returnType) ++ " "++ functionName ++ (show arguments) ++ "\n" ++ ( foldl (\acc x -> acc ++ (blockToString functionInstructions x)) "" (getValues blocks blockOrder) ) ++ "\n"

instance Value VFunction where
  getType _ (VFunction _ returnType arguments _ _ _ ) = TFunction returnType arguments

instance Namable VFunction where
  getName func = (functionName func)

data VBlock            = VBlock {
  blockFunctionName :: String,
  blockName         :: String,
  blockInstructions :: [String]
} deriving (Eq, Show);

instance Namable VBlock where
  getName block = (blockName block)

data PModule          = PModule {
  functions    :: HashMap.Map String VFunction,
  callouts     :: HashMap.Map String String,
  globals      :: HashMap.Map String (VType, Maybe Int),
  lastId       :: Int
} deriving (Eq);

instance Show PModule where
  show (PModule functions callouts globals _) =
    let cstring   = foldl (\acc (str,_) -> acc ++ "callout " ++ (show str) ++"\n") "" ( HashMap.assocs callouts )
        gstring   = foldl (\acc (str,typ) -> acc ++ "global " ++ (show typ) ++" "++ (show str) ++ "\n") "" ( HashMap.assocs globals )
        fstring   = foldl (\acc (str,func) -> acc ++ (show func) ++ "\n") "" (HashMap.assocs functions)
        in cstring ++ "\n" ++ gstring ++ "\n" ++ fstring

uniqueBlockName :: String -> VFunction -> String
uniqueBlockName str func =
  let hm :: HashMap.Map String VBlock = (blocks func)
      inMap :: Bool = HashMap.member str hm in
        case inMap of
          False -> str
          True -> uniqueBlockName (str ++ ".1") func

createID :: PModule -> (String, PModule)
createID pmod =
  let name :: String = "%" ++ (show ((lastId pmod)+1)) in
    (name, pmod{lastId=((lastId pmod)+1)})

data Context          = Context {
  contextFunctionName :: String,
  contextBlockName    :: String
  {- instructionIndex :: Int -}
} deriving (Eq, Show);

data Builder          = Builder {
  pmod     :: PModule,
  location :: Context,
  debugs   :: [IO()]
};

addDebug :: Builder -> (IO () ) -> Builder
addDebug b a = b{debugs=((debugs b)++[a])}

getFunction :: Builder -> String -> Maybe VFunction
getFunction (Builder pmod _ _) name = HashMap.lookup name (functions pmod)

getInstruction :: Builder -> String -> Maybe VInstruction
getInstruction (Builder pmod (Context fname _) _) name =
  do
    func <- HashMap.lookup fname (functions pmod)
    HashMap.lookup name (functionInstructions func)

getTerminator :: Builder -> Maybe ValueRef
getTerminator builder =
  do
    func <- getFunction builder (contextFunctionName $ location builder)
    block <- HashMap.lookup (contextBlockName $ location builder) $ blocks func
    let lst = blockInstructions block
    final <- if ( length lst )== 0 then Nothing else Just $ last lst
    fv <- HashMap.lookup final $ functionInstructions func
    case fv of
      (VReturn _ _ ) -> Just $ InstRef final
      (VCondBranch _ _ _ _) -> Just $ InstRef final
      (VUncondBranch _ _) -> Just $ InstRef final
      (VUnreachable _) -> Just $ InstRef final
      _ -> Nothing

instance Locationable (String,String) where
  setInsertionPoint (str1,str2) builder = setInsertionPoint (Context str1 str2 ) builder

instance Locationable String where
  setInsertionPoint str builder = setInsertionPoint (Context (contextFunctionName $ location builder) str ) builder

instance Locationable VBlock where
  setInsertionPoint block builder = setInsertionPoint (Context (blockFunctionName block) (blockName block) ) builder

instance Locationable Context where
  setInsertionPoint ctx builder = builder{location=ctx}

appendToBlock :: VInstruction -> VBlock -> VBlock
appendToBlock instr (VBlock a b instructions) = VBlock a b (instructions ++ [getName instr])

appendInstruction :: VInstruction -> Builder -> Builder
appendInstruction instr builderm =
  let builder0 = builderm--addDebug builderm $ printf "PAdding instr %s at %s\n" (show instr) (show $ location builderm)
      updated :: Maybe Builder =
        do
          let builder = builder0--addDebug builder0 $ printf "Adding instruction %s\n" (show instr)
          let context = location builder
          let pmod1 = pmod builder
          let fn = contextFunctionName context
          let bn = contextBlockName context
          func <- HashMap.lookup fn (functions pmod1)
          block <- HashMap.lookup bn (blocks func)
          block2 <- return $ appendToBlock instr block
          func2 <- return $ func{blocks=(HashMap.insert bn block2 (blocks func)),functionInstructions=(HashMap.insert (getName instr) instr (functionInstructions func))}
          functions2 <- return $ HashMap.insert fn func2 (functions pmod1)
          return $ builder{pmod=pmod1{functions=functions2}}
      in case updated of
        Just builder2 -> builder2
        Nothing -> builder0

createUnaryOp :: {-Operand-} String -> ValueRef -> Builder -> (ValueRef,Builder)
createUnaryOp op operand builder =
  let (name, pmod2) :: (String, PModule) = createID $ pmod builder
      builder2 :: Builder = appendInstruction (VUnOp name op operand) builder{pmod=pmod2}
      ref :: ValueRef = InstRef name in
      (ref, builder2)

createBinOp :: String -> ValueRef -> ValueRef -> Builder -> (ValueRef, Builder)
createBinOp op operand1 operand2 builder =
  let (name, pmod2) :: (String, PModule) = createID $ pmod builder
      builder2 :: Builder = appendInstruction (VBinOp name op operand1 operand2) builder{pmod=pmod2}
      ref :: ValueRef = InstRef name in
      (ref, builder2)

createGlobal :: String -> VType -> Maybe Int -> Builder -> (ValueRef, Builder)
createGlobal name op operand1 builder =
  let pmod1 = pmod builder
      pmod2 = pmod1{globals=HashMap.insert name (op,operand1) (globals pmod1)}
      builder2 :: Builder = appendInstruction (VAllocation name op operand1) builder{pmod=pmod2}
      ref :: ValueRef = GlobalRef name in
      (ref, builder2)

createAlloca :: VType -> Maybe Int -> Builder -> (ValueRef, Builder)
createAlloca op operand1 builder =
  let pmod1 = pmod builder
      (name, pmod2) :: (String, PModule) = createID pmod1
      builder2 :: Builder = appendInstruction (VAllocation name op operand1) builder{pmod=pmod2}
      builder3 = builder2--addDebug builder2 $ printf "creating alloca inst ctx:%s %s\n%s\n\n" (show $ location builder2 ) name (show $ pmod builder2)
      ref :: ValueRef = InstRef name in
      (ref, builder3)

maybeIntToInt :: Maybe Int -> Int
maybeIntToInt val = case val of
  Nothing -> 0
  Just v  -> v

zeroMemory :: (ValueRef, Builder) -> Maybe Int-> Builder
zeroMemory (mem,builder) val = 
  let typ = getDerivedTypeN $ getType builder mem
      in case typ of
         TInt   -> snd $ createStore (ConstInt  0) mem builder
         TBool  -> snd $ createStore (ConstBool False) mem builder
         TArray x -> snd $ createCalloutCall "bzero" [mem, ConstInt $ toInteger $ (maybeIntToInt val)*(typeSize x)] builder
         TVoid  -> builder
         x -> addDebug builder $ printf "wtf %s\n" (show x)


createZeroAlloca :: VType -> Maybe Int -> Builder -> (ValueRef, Builder)
createZeroAlloca op len builder0 =
  let (ref, builder) = createAlloca op len builder0
      builder2 = zeroMemory (ref, builder) len 
      in (ref, builder2)

createStore :: ValueRef -> ValueRef -> Builder -> (ValueRef, Builder)
createStore toStore loc builder =
  let pmod1 = pmod builder
      (name, pmod2) :: (String, PModule) = createID pmod1
      builder2 :: Builder = appendInstruction (VStore name toStore loc) builder{pmod=pmod2}
      ref :: ValueRef = InstRef name in
      (ref, builder2)

createLookup :: ValueRef -> Builder -> (ValueRef, Builder)
createLookup loc builder =
  let pmod1 = pmod builder
      (name, pmod2) :: (String, PModule) = createID pmod1
      builder2 :: Builder = appendInstruction (VLookup name loc) builder{pmod=pmod2}
      ref :: ValueRef = InstRef name in
      (ref, builder2)

createArrayStore :: ValueRef -> ValueRef -> ValueRef -> Builder -> (ValueRef, Builder)
createArrayStore toStore array index builder =
  let pmod1 = pmod builder
      (name, pmod2) :: (String, PModule) = createID pmod1
      builder2 :: Builder = appendInstruction (VArrayStore name toStore array index) builder{pmod=pmod2}
      ref :: ValueRef = InstRef name in
      (ref, builder2)

createArrayLookup :: ValueRef -> ValueRef -> Builder -> (ValueRef, Builder)
createArrayLookup array index builder =
  let pmod1 = pmod builder
      (name, pmod2) :: (String, PModule) = createID pmod1
      builder2 :: Builder = appendInstruction (VArrayLookup name array index) builder{pmod=pmod2}
      ref :: ValueRef = InstRef name in
      (ref, builder2)

createArrayLen :: ValueRef -> Builder -> (ValueRef, Builder)
createArrayLen array builder =
  let pmod1 = pmod builder
      (name, pmod2) :: (String, PModule) = createID pmod1
      builder2 :: Builder = appendInstruction (VArrayLen name array) builder{pmod=pmod2}
      ref :: ValueRef = InstRef name in
      (ref, builder2)

createBoundedArrayLookup :: ValueRef -> ValueRef -> Builder -> (ValueRef, Builder)
createBoundedArrayLookup array index ar1 =
  let (len, ar2)      = createArrayLen array ar1
      (inBounds, ar3) = createBinOp "u<" index len ar2
      (goodBlock,ar4) = createBlock "inbounds" ar3
      (badBlock,ar5)  = createBlock "outbounds" ar4
      (_,ar6)         = createCondBranch inBounds goodBlock badBlock ar5
      ar7             = setInsertionPoint badBlock ar6
      ar8             = createExit (-1) ar7
      (_,ar9)         = createUnreachable ar8
      ar10            = setInsertionPoint goodBlock ar9
      in createArrayLookup array index ar10

createBoundedArrayStore :: ValueRef -> ValueRef -> ValueRef -> Builder -> (ValueRef, Builder)
createBoundedArrayStore toStore array index ar1 =
  let (len, ar2)      = createArrayLen array ar1
      (inBounds, ar3) = createBinOp "u<" index len ar2
      (goodBlock,ar4) = createBlock "inbounds" ar3
      (badBlock,ar5)  = createBlock "outbounds" ar4
      (_,ar6)         = createCondBranch inBounds goodBlock badBlock ar5
      ar7             = setInsertionPoint badBlock ar6
      ar8             = createExit (-1) ar7
      (_,ar9)         = createUnreachable ar8
      ar10            = setInsertionPoint goodBlock ar9
      in createArrayStore toStore array index ar10


createReturn :: Maybe ValueRef -> Builder -> (ValueRef, Builder)
createReturn retValue builder =
  let pmod1 = pmod builder
      (name, pmod2) :: (String, PModule) = createID pmod1
      builder2 :: Builder = appendInstruction (VReturn name retValue) builder{pmod=pmod2}
      ref :: ValueRef = InstRef name in
      (ref, builder2)

createCondBranch :: ValueRef -> String -> String -> Builder -> (ValueRef, Builder)
createCondBranch cond trueBranch falseBranch builder =
  let pmod1 = pmod builder
      (name, pmod2) :: (String, PModule) = createID pmod1
      builder2 :: Builder = appendInstruction (VCondBranch name cond trueBranch falseBranch) builder{pmod=pmod2}
      ref :: ValueRef = InstRef name in
      (ref, builder2)

createUnreachable :: Builder -> (ValueRef, Builder)
createUnreachable builder =
  let pmod1 = pmod builder
      (name, pmod2) :: (String, PModule) = createID pmod1
      builder2 :: Builder = appendInstruction (VUnreachable name) builder{pmod=pmod2}
      ref :: ValueRef = InstRef name in
      (ref, builder2)

createExit :: Int -> Builder -> Builder
createExit eval build = snd $ createCalloutCall "exit" [ConstInt $ read $ show eval] build

createUncondBranch :: String -> Builder -> (ValueRef, Builder)
createUncondBranch branch builder =
  let pmod1 = pmod builder
      (name, pmod2) :: (String, PModule) = createID pmod1
      builder2 :: Builder = appendInstruction (VUncondBranch name branch) builder{pmod=pmod2}
      ref :: ValueRef = InstRef name in
      (ref, builder2)

createMethodCall :: String -> [ValueRef] -> Builder -> (ValueRef, Builder)
createMethodCall fname args builder =
  let pmod1 = pmod builder
      (name, pmod2) :: (String, PModule) = createID pmod1
      builder2 :: Builder = appendInstruction (VMethodCall name False fname args) builder{pmod=pmod2}
      ref :: ValueRef = InstRef name in
      (ref, builder2)

createCalloutCall :: String -> [ValueRef] -> Builder -> (ValueRef, Builder)
createCalloutCall fname args builder =
  let pmod1 = pmod builder
      (name, pmod2) :: (String, PModule) = createID pmod1
      builder2 :: Builder = appendInstruction (VMethodCall name True fname args) builder{pmod=pmod2}
      ref :: ValueRef = InstRef name in
      (ref, builder2)

createBlockF :: String -> VFunction -> VFunction
createBlockF str func =
  let str2 = uniqueBlockName str func
      block = VBlock (functionName func) str2 []
      in func {blocks = HashMap.insert str2 block $ blocks func, blockOrder=(blockOrder func)++[str2]}

removeEmptyBlock :: String -> Builder -> Builder
removeEmptyBlock str builder =
  let updated :: Maybe Builder =
        do
          let pmod1 = pmod builder
          let context = location builder
          let fn = contextFunctionName context
          func <- HashMap.lookup fn (functions pmod1)
          let newBlocks = HashMap.delete str (blocks func)
          func2 <- return $ func{blocks=newBlocks, blockOrder=delete str (blockOrder func)}
          functions2 <- return $ HashMap.insert fn func2 (functions pmod1)
          return $ builder{pmod=pmod1{functions=functions2}}
      in case updated of
        Just builder -> builder
        Nothing -> builder

createBlock :: String -> Builder -> (String, Builder)
createBlock str builder =
  let updated :: Maybe (String,Builder) =
        do
          let pmod1 = pmod builder
          let context = location builder
          let fn = contextFunctionName context
          func <- HashMap.lookup fn (functions pmod1)
          let str2 = uniqueBlockName str func
          block <- return $ VBlock fn str2 []
          let oldBlocks = blocks func
          let newBlocks = HashMap.insert str2 block oldBlocks
          func2 <- return $ func{blocks=newBlocks, blockOrder=(blockOrder func)++[str2]}
          functions2 <- return $ HashMap.insert fn func2 (functions pmod1)
          return $ (str2, builder{pmod=pmod1{functions=functions2}})
      in case updated of
        Just builder -> builder
        Nothing -> ("",builder)


-- assume no function exists with name currently
createFunction :: String -> VType -> [VType] -> Builder -> Builder
createFunction str ty1 argTypes builder =
  let pmod1 = pmod builder
      func = VFunction str ty1 argTypes (HashMap.empty) (HashMap.empty) []
      func2 = createBlockF "entry" func
      functions2 = HashMap.insert str func2 (functions pmod1) in
        builder{pmod=pmod1{functions=functions2}}

createCallout :: String -> Builder -> Builder
createCallout str builder =
  let pmod1 = pmod builder
      callouts1 = callouts pmod1
      callouts2 = HashMap.insert str str callouts1
      builder2 = builder--addDebug builder $ printf "Adding callout %s\n" (show str)
      in builder2{pmod=pmod1{callouts=callouts2}}

createPModule :: PModule
createPModule = PModule (HashMap.empty) (HashMap.empty) (HashMap.empty) 0

createBuilder :: Builder
createBuilder = Builder createPModule (Context "" "") []
