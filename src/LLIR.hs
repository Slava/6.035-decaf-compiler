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
data Value            = VFunctionp VFunction
                      | VInstruction
                      | VConstant
                      | VArgumentp VArgument

data VArgument        = VArgument String VType

data VFunction        = VCalloutFunction String VType
                      | VUserFunctionp VUserFunction

data VInstruction     = VFunctionCall VFunction [Value]
                      | VBinOp String Value Value
                      | VUnOp String Value

data VConstant        = VConstInt Int
                      | VConstString String

data VUserFunction    = VUserFunction {
  arguments :: [VArgument],
  blocks    :: HashMap.Map String VBlock
}

data VBlock            = VBlock {
  instructions :: [VInstruction]
}

data PModule          = PModule {
  functions :: HashMap.Map String VUserFunction
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
appendInstruction instr (Builder (PModule pfunctions) context) =
  let updated :: Maybe Builder =
        do
          func <- HashMap.lookup (functionName context) pfunctions
          block <- HashMap.lookup (blockName context) (blocks func)
          block2 <- return $ appendToBlock instr block
          func2 <- return $ VUserFunction (arguments func) (HashMap.insert (blockName context) block2 (blocks func) )
          functions2 <- return $ HashMap.insert (functionName context) func2 pfunctions
          return $ Builder (PModule functions2) context
      in case updated of
        Just builder -> builder
        Nothing -> Builder (PModule pfunctions) context

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
