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

getDerivedType :: VType -> Maybe VType
getDerivedType a =
  case a of
    TPointer ty -> Just ty
    _ -> Nothing

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
              | ConstInt Int
              | ConstString String
              | CalloutRef String
              | FunctionRef String
              | ArgRef Int String
  deriving(Eq, Show);

instance Value ValueRef where
  getType builder (InstRef str) =
    case getInstruction builder str of
      Just inst -> getType builder inst
      Nothing -> TVoid
  getType _ (ConstInt _) = TInt
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
                  | VUncondBranch String String
  deriving (Eq, Show);

instance Namable VInstruction where
  getName (VUnOp name _ _ ) = name
  getName (VBinOp name _ _ _ ) = name
  getName (VStore name _ _) = name
  getName (VLookup name _) = name
  getName (VAllocation name _ _) = name
  getName (VArrayLookup name _ _) = name
  getName (VArrayLen name _) = name
  getName (VReturn name _) = name
  getName (VCondBranch name _ _ _) = name
  getName (VUncondBranch name _) = name

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
    | op == "=="  =  TBool
    | op == "!="  =  TBool
    | op == "&"  =  TBool
    | op == "|"  =  TBool
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
  blocks    :: HashMap.Map String VBlock
} deriving (Eq, Show);

instance Value VFunction where
  getType _ (VFunction _ returnType arguments _ _ ) = TFunction returnType arguments

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
  globals      :: HashMap.Map String VType,
  lastId       :: Int
} deriving (Eq, Show);

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
  location :: Context
} deriving (Eq, Show);

getFunction :: Builder -> String -> Maybe VFunction
getFunction (Builder pmod (Context fname _)) name = HashMap.lookup fname (functions pmod)

getInstruction :: Builder -> String -> Maybe VInstruction
getInstruction (Builder pmod (Context fname _)) name =
  do
    func <- HashMap.lookup fname (functions pmod)
    HashMap.lookup name (functionInstructions func)

instance Locationable (String,String) where
  setInsertionPoint (str1,str2) builder = setInsertionPoint (Context str1 str2 ) builder

instance Locationable String where
  setInsertionPoint str builder = setInsertionPoint (Context (contextFunctionName $ location builder) str ) builder

instance Locationable VBlock where
  setInsertionPoint block builder = setInsertionPoint (Context (blockFunctionName block) (blockName block) ) builder

instance Locationable Context where
  setInsertionPoint ctx (Builder pmod _) = Builder pmod ctx

appendToBlock :: VInstruction -> VBlock -> VBlock
appendToBlock instr (VBlock a b instructions) = VBlock a b (instructions ++ [getName instr])

appendInstruction :: VInstruction -> Builder -> Builder
appendInstruction instr (Builder pmod context) =
  let updated :: Maybe Builder =
        do
          let fn = contextFunctionName context
          let bn = contextBlockName context
          func <- HashMap.lookup fn (functions pmod)
          block <- HashMap.lookup bn (blocks func)
          block2 <- return $ appendToBlock instr block
          func2 <- return $ func{blocks=(HashMap.insert bn block2 (blocks func)),functionInstructions=(HashMap.insert (getName instr) instr (functionInstructions func))}
          functions2 <- return $ HashMap.insert fn func2 (functions pmod)
          return $ Builder pmod{functions=functions2} context
      in case updated of
        Just builder -> builder
        Nothing -> Builder pmod context

createUnaryOp :: {-Operand-} String -> ValueRef -> Builder -> (ValueRef,Builder)
createUnaryOp op operand (Builder pmod context) =
  let (name, pmod2) :: (String, PModule) = createID pmod
      builder2 :: Builder = appendInstruction (VUnOp name op operand) (Builder pmod2 context)
      ref :: ValueRef = InstRef name in
      (ref, builder2)

createBinOp :: String -> ValueRef -> ValueRef -> Builder -> (ValueRef, Builder)
createBinOp op operand1 operand2 (Builder pmod context) =
  let (name, pmod2) :: (String, PModule) = createID pmod
      builder2 :: Builder = appendInstruction (VBinOp name op operand1 operand2) (Builder pmod2 context)
      ref :: ValueRef = InstRef name in
      (ref, builder2)

createBlockF :: String -> VFunction -> VFunction
createBlockF str func =
  let str2 = uniqueBlockName str func
      block = VBlock (functionName func) str2 []
      in func {blocks = HashMap.insert str2 block $ blocks func }

createBlock :: String -> Builder -> (String, Builder)
createBlock str (Builder pmod context) =
  let updated :: Maybe (String,Builder) =
        do
          let fn = contextFunctionName context
          func <- HashMap.lookup fn (functions pmod)
          let str2 = uniqueBlockName str func
          block <- return $ VBlock fn str2 []
          let oldBlocks = blocks func
          let newBlocks = HashMap.insert str2 block oldBlocks
          func2 <- return $ func{blocks=newBlocks}
          functions2 <- return $ HashMap.insert fn func2 (functions pmod)
          return $ (str2, Builder pmod{functions=functions2} context)
      in case updated of
        Just builder -> builder
        Nothing -> ("",Builder pmod context)


-- assume no function exists with name currently
createFunction :: String -> VType -> [VType] -> Builder -> Builder
createFunction str ty1 argTypes (Builder pmod context) =
  let func = VFunction str ty1 argTypes (HashMap.empty) (HashMap.empty)
      func2 = createBlockF "entry" func
--      instrs = foldl ( \acc (idx, typ) -> HashMap.insert ("$a" ++ (show idx)) (VArgument ("$a" ++ (show idx)) idx typ ) acc) (functionInstructions func) ( zip [0..(length argTypes)] argTypes )
--      func3 = func2{functionInstructions=instrs}
      func3 = func2
      functions2 = HashMap.insert str func3 (functions pmod) in
        Builder pmod{functions=functions2} context

createCallout :: String -> Builder -> Builder
createCallout str (Builder pmod context) =
  let callouts1 = callouts pmod
      callouts2 = HashMap.insert str str callouts1
      in (Builder pmod{callouts=callouts2} context)

createPModule :: PModule
createPModule = PModule (HashMap.empty) (HashMap.empty) (HashMap.empty) 0

createBuilder :: Builder
createBuilder = Builder createPModule (Context "" "")
