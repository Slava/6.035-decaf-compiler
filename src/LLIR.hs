{-# OPTIONS -Wall #-}
{-# LANGUAGE ScopedTypeVariables #-}

module LLIR where

-- Imports
import Prelude
import Text.Printf (printf)
import ParseTypes
import qualified Data.Map as HashMap


data VType            = VInt
                      | VString
                      | VFunctionDecl VType [VType]

-- Data Types
data Value            = VFunction
                      | VInstruction
                      | VConstant
                      | VArgument String VType

data VFunction        = VCalloutFunction String VType
                      | VUserFunction

data VInstruction     = VFunctionCall VFunction [Value]
                      | VBinOp String Value Value
                      | VUnOp String Value

data VConstant        = VConstInt Int
                      | VConstString String

data VUserFunction    = VUserFunction {
  arguments :: [VArgument],
  blocks    :: HashMap String VBlock
}

data VBlock            = VBlock {
  instructions :: [VInstruction]
}

data PModule          = PModule {
  functions :: HashMap String VUserFunction
}

data Context          = Context {
  functionName :: String,
  blockName    :: String
  {- instructionIndex :: Int -}
}

data Builder          = Builder {
  pmod     :: PModule,
  location :: Context
}

appendToBlock :: VInstruction -> VBlock -> VBlock
appendToBlock instr (VBlock instructions) = VBlock (instructions ++ [instr])

appendInstruction :: VInstruction -> Builder -> Builder
appendInstruction instr (Builder (PModule functions) context) =
  let func = HashMap.lookup context.functionName functions
      block = HashMap.lookup context.blockName func
      block2 = appendToBlock instr block
      functions2 = HashMap.insert context.blockName block2 functions in
    Builder (PModule functions2) context
  --
  --
  -- let functions2 :: HashMap String VFunction = do
  --   func :: VFunction <- HashMap.lookup context.functionName functions
  --   let block2 :: VBlock = do
  --     block :: VBlock <- HashMap.lookup context.blockName func
  --     return $ appendToBlock instr block
  --   return $ HashMap.insert context.blockName block2 functions in
  -- Builder (PModule functions2) context
