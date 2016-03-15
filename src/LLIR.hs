{-# OPTIONS -Wall #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveAnyClass #-}

module LLIR where

-- Imports
import Prelude
import Text.Printf (printf)
import ParseTypes
import qualified Data.Map as HashMap


data VType            = TInt
                      | TBool
                      | TString
                      | TFunction VType [VType]
                      | TCallout
                      | TBlock
                      deriving (Eq, Show);

class Namable a where
  getName :: a -> String

class Locationable a where
  setInsertionPoint :: a -> Builder -> Builder

class Value a where
  getType :: a -> VType


data VConstant = VConstInt Int
               | VConstString String
  deriving(Eq, Show);

instance Value VConstant where
  getType (VConstInt _) = TInt
  getType (VConstString _) = TString

data ValueRef = InstRef String
              | ConstRef VConstant
  deriving(Eq, Show);

data VInstruction = VArgument String {- index -} Int VType
                  | VUnOp {- name -} String {- operand -} String {- argument name -} ValueRef
                  | VBinOp {- name -} String {- operand -} String {- argument name -} ValueRef ValueRef
  deriving (Eq, Show);

instance Namable VInstruction where
  getName (VArgument name _ _ ) = name
  getName (VUnOp name _ _ ) = name
  getName (VBinOp name _ _ _ ) = name

instance Value VInstruction where
  getType (VArgument _ _ typ ) = typ
  getType (VUnOp _ op _ )
    | op == "+"   =  TInt
    | op == "-"   =  TInt
    | op == "~"   =  TInt
    | op == "!"   =  TBool
  getType (VBinOp _ op _ _)
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

data VCallout = VCallout String
  deriving(Eq, Show);

instance Value VCallout where
  getType _ = TCallout

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
  getType (VFunction _ returnType arguments _ _ ) = TFunction returnType arguments

instance Namable VFunction where
  getName func = (functionName func)

data VBlock            = VBlock {
  blockFunctionName :: String,
  blockName     :: String,
  blockInstructions :: [String]
} deriving (Eq, Show);

instance Value VBlock where
  getType _ = TBlock

instance Namable VBlock where
  getName block = (blockName block)

data PModule          = PModule {
  functions    :: HashMap.Map String VFunction,
  lastId       :: Int
} deriving (Eq, Show);

createID :: PModule -> (String, PModule)
createID (PModule funs lid) =
  let name :: String = "%" ++ (show (lid+1)) in
    (name, PModule funs (lid+1))

data Context          = Context {
  contextFunctionName :: String,
  contextBlockName    :: String
  {- instructionIndex :: Int -}
} deriving (Eq, Show);

data Builder          = Builder {
  pmod     :: PModule,
  location :: Context
} deriving (Eq, Show);


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

createUnaryOp :: {-Operand-} String -> ValueRef -> Builder ->(ValueRef,Builder)
createUnaryOp op operand (Builder pmod context) =
  let (name, pmod2) :: (String, PModule) = createID pmod
      builder2 :: Builder = appendInstruction (VUnOp name op operand) (Builder pmod2 context)
      ref :: ValueRef = InstRef name in
      (ref, builder2)

-- TODO createFunction
-- TODO create Other ops

{-
    case fm of
      Just func -> HashMap.lookup (functionName context) pfunctions in
        let bm :: Maybe VBlock = HashMap.lookup (blockName context) (blocks func) in
          case bm of
            Just block ->
              let block2 :: VBlock = appendToBlock instr block
                  func2 :: VUserFunction = VUserFunction (arguments func) (HashMap.insert (blockName context) block2 (blocks func) )
                  functions2 :: HashMap.Map String VUserFunction = HashMap.insert (functionName context) func2 pfunctions in
                    Builder (PModule functions2) context
            Nothing -> Builder (PModule pfunctions) context
      Nothing -> {- should never occur -} Builder (PModule pfunctions) context
-}

  --
  --
  -- let functions2 :: HashMap String VFunction = do
  --   func :: VFunction <- HashMap.lookup context.functionName functions
  --   let block2 :: VBlock = do
  --     block :: VBlock <- HashMap.lookup context.blockName func
  --     return $ appendToBlock instr block
  --   return $ HashMap.insert context.blockName block2 functions in
  -- Builder (PModule functions2) context
