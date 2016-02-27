{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}

module ParseTypes where

import GHC.Generics

import Data.Aeson

import Scanner (ScannedToken(..), Token(..))

data Program = Program [Declaration] deriving (Eq, Show, Generic)

instance ToJSON Program where

type Block = ([Declaration], [Statement])

type Field = (String, Maybe Int)

data Declaration = Callout String
                 | Fields (Type, [Field])
                 | Method { methodRetType :: Type
                          , methodName :: String
                          , methodArgs :: [Argument]
                          , methodBody :: Block }
                 deriving (Eq, Show, Generic)

instance ToJSON Declaration where

data Type = Type String deriving (Eq, Show, Generic)

instance ToJSON Type where

data Argument = Argument (Type, String) deriving (Eq, Show, Generic)

instance ToJSON Argument where

data Statement = Assignment (Expression, Expression)
               | MethodCallStatement MethodCall
               | BreakStatement
               | ContinueStatement
               | ReturnStatement Expression
               | LoopStatement { loopCondition :: Expression
                               , loopBody :: Block
                               , loopInit :: Maybe (String, Expression)
                               , loopIncr :: Maybe Int }
               | IfStatement { ifCondition :: Expression
                             , ifConsequentBody :: Block
                             , ifAlternativeBody :: Block }
               deriving (Eq, Show, Generic)

instance ToJSON Statement where

data Location = Location (String, Maybe Expression) deriving (Eq, Show, Generic)

instance ToJSON Location where

data Literal = StringLiteral String
             | IntLiteral Int
             | CharLiteral Char
             | BoolLiteral Bool
             deriving (Eq, Show, Generic)

instance ToJSON Literal where

data Expression = BinOpExpression (String, Expression, Expression)
                | NegExpression Expression
                | NotExpression Expression
                | LengthExpression Expression
                | LocationExpression Location
                | LiteralExpression Literal
                | MethodCallExpression MethodCall
                | CondExpression { condCondition :: Expression
                                 , condConsequent :: Expression
                                 , condAlternative :: Expression }
                deriving (Eq, Show, Generic)

instance ToJSON Expression where

data AssignOp = AssignmentOp | AddAssignmentOp | SubtractAssignmentOp deriving (Eq, Show, Generic)

instance ToJSON AssignOp where

type MethodCall = (String, [CalloutArg]);

data CalloutArg = CalloutExpression Expression
                | CalloutStringLit String
                deriving (Eq, Show, Generic)

instance ToJSON CalloutArg where

