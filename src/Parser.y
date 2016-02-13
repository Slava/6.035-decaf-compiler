-- Parser -- Decaf parser                                       -*- haskell -*-
-- Copyright (C) 2013  Benjamin Barenblat <bbaren@mit.edu>
--
-- This file is a part of decafc.
--
-- decafc is free software: you can redistribute it and/or modify it under the
-- terms of the MIT (X11) License as described in the LICENSE file.
--
-- decafc is distributed in the hope that it will be useful, but WITHOUT ANY
-- WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
-- FOR A PARTICULAR PURPOSE.  See the X11 license for more details.
{
module Parser ( parse
              ) where

import Text.Printf (printf)
import Data.List (reverse)

import Scanner (ScannedToken(..), Token(..))

}


--------------------------------- Directives ----------------------------------

%name parse
%error { parseError }
%monad { Either String }

%tokentype { ScannedToken }

%token
  -- keywords --
  class      { ScannedToken _ _ (Keyword "class") }
  boolean    { ScannedToken _ _ (Keyword "boolean") }
  break      { ScannedToken _ _ (Keyword "break") }
  callout    { ScannedToken _ _ (Keyword "callout") }
  continue   { ScannedToken _ _ (Keyword "continue") }
  else       { ScannedToken _ _ (Keyword "else") }
  for        { ScannedToken _ _ (Keyword "for") }
  while      { ScannedToken _ _ (Keyword "while") }
  if         { ScannedToken _ _ (Keyword "if") }
  int        { ScannedToken _ _ (Keyword "int") }
  return     { ScannedToken _ _ (Keyword "return") }
  void       { ScannedToken _ _ (Keyword "void") }

  identifier { ScannedToken _ _ (Identifier $$) }

  charLiteral { ScannedToken _ _ (Scanner.CharLiteral $$) }
  booleanLiteral { ScannedToken _ _ (Scanner.BooleanLiteral $$) }
  intLiteral { ScannedToken _ _ (Scanner.IntLiteral $$) }
  stringLiteral { ScannedToken _ _ (Scanner.StringLiteral $$) }

  -- special symbols --
  '{'        { ScannedToken _ _ LCurly }
  '}'        { ScannedToken _ _ RCurly }
  '('        { ScannedToken _ _ LParen }
  ')'        { ScannedToken _ _ RParen }
  '['        { ScannedToken _ _ LBrack }
  ']'        { ScannedToken _ _ RBrack }
  '+'        { ScannedToken _ _ Plus   }
  '-'        { ScannedToken _ _ Minus  }
  '/'        { ScannedToken _ _ Slash  }
  '*'        { ScannedToken _ _ Asterisk }
  '%'        { ScannedToken _ _ Percent }
  '!'        { ScannedToken _ _ Excl   }
  '>'        { ScannedToken _ _ GreaterThan }
  '<'        { ScannedToken _ _ LessThan }
  '?'        { ScannedToken _ _ QuestM }
  ':'        { ScannedToken _ _ Colon  }
  ';'        { ScannedToken _ _ Semicol }
  ','        { ScannedToken _ _ Comma }
  '@'        { ScannedToken _ _ AtSign }
  '='        { ScannedToken _ _ EqSign }
  ">="       { ScannedToken _ _ GreaterThanEq }
  "<="       { ScannedToken _ _ LessThanEq }
  "=="       { ScannedToken _ _ EqEq   }
  "!="       { ScannedToken _ _ ExclEq }
  "&&"       { ScannedToken _ _ AmpAmp }
  "||"       { ScannedToken _ _ PipePipe }
  "-="       { ScannedToken _ _ MinusEq }
  "+="       { ScannedToken _ _ PlusEq }


%right "+=" "-=" '='
%left '+' '-'
%left '*' '/' '%'
%left NEG
%right '?'
%nonassoc '>' '<' ">=" "<="
%nonassoc "==" "!="
%nonassoc "&&" "||"
%% -------------------------------- Grammar -----------------------------------

Program
      : CalloutDecls FieldDecls MethodDecls { Program ($1 ++ $2 ++ $3) }

CalloutDecls
      : CalloutDecls_ { reverse $1 }

CalloutDecls_
      : {-- empty --}             { [] }
      | CalloutDecls_ CalloutDecl { $2 : $1 }

CalloutDecl
      : callout identifier ';' { Callout $2 }

FieldDecls
      : FieldDecls_ { reverse $1 }

FieldDecls_
      : {-- empty --}         { [] }
      | FieldDecls_ FieldDecl { $2 : $1 }

FieldDecl
      : Type FieldDecl_Fields ';' { Fields ($1, $2) }

FieldDecl_Fields
      : Fields_ { reverse $1 }

Fields_
      : Field_         { [$1] }
      | Fields_ ',' Field_ { $3 : $1 }

Field_
      : identifier { $1 }

MethodDecls
      : MethodDecls_ { reverse $1 }

MethodDecls_
      : {-- empty --}           { [] }
      | MethodDecls_ MethodDecl { $2 : $1 }

MethodDecl
      : MethodRetType identifier '(' Arguments ')' Block {
              Method { retType = $1
                     , name = $2
                     , args = $4
                     , vars = (fst $6)
                     , body = (snd $6) }
        }

MethodRetType
      : Type      { $1 }
      | TypeVoid_ { $1 }

Arguments
      : Arguments_    { reverse $1 }
      | {-- empty --} { [] }

Arguments_
      : Argument                { [$1] }
      | Arguments_ ',' Argument { $3 : $1 }

Argument
      : Type identifier { Argument ($1, $2) }

Block
      : '{' FieldDecls Statements '}' { ($2, $3) }

Statements
      : Statements_ { reverse $1 }

Statements_
      : {-- empty --}         { [] }
      | Statements_ Statement { $2 : $1 }

Statement
      : Location AssignOp Expression ';' { constructAssignmentStatement $1 $2 $3 }
{--
| method_call ;
| if ( expr ) block
else block
| for ( id = expr , expr [, int_literal]) block
| while ( expr ) block
| return expr ;
| break ;
| continue ;
--}

Location
      : Location_ { LocationExpression $1 }

Location_
      : identifier Location_sub { Location ($1, $2) }

Location_sub
      : '[' Expression ']' { Just $2 }
      | {-- empty --}      { Nothing }

AssignOp
      : '='  { AssignmentOp }
      | "+=" { AddAssignmentOp }
      | "-=" { SubtractAssignmentOp }

Expression
      : Location                    { $1 }
      | Literal                     { LiteralExpression $1 }
      | Expression BinOp Expression { BinOpExpression ($2, $1, $3) }
      | '-' Expression %prec NEG    { NegExpression $2 }
      | '!' Expression              { NotExpression $2 }
      | '(' Expression ')'          { $2 }
      | '@' identifier              { LengthExpression (LocationExpression (Location ($2, Nothing))) }
      | MethodCall                  { $1 }
      | Expression '?' Expression ':' Expression
                                    { CondExpression {condition=$1, consequent=$3, alternative=$5} }

BinOp
      : ArithOp { $1 }
      | RelOp   { $1 }
      | EqOp    { $1 }
      | CondOp  { $1 }

ArithOp
      : '+' { "+" }
      | '-' { "-" }
      | '*' { "*" }
      | '/' { "/" }
      | '%' { "%" }

RelOp
      : '>'  { ">" }
      | '<'  { "<" }
      | ">=" { ">=" }
      | "<=" { "<=" }

EqOp
      : "==" { "==" }
      | "!=" { "!=" }

CondOp
      : "&&" { "&&" }
      | "||" { "||" }

MethodCall
      : identifier '(' MethodCall_Expressions ')' { MethodCallExpression ($1, $3) }
      | identifier '(' MethodCall_CalloutArgs ')' { MethodCallExpression ($1, $3) }

MethodCall_Expressions
      : MethodCall_Expressions_ { reverse $1 }
      | {-- empty --}           { [] }
MethodCall_Expressions_
      : Expression                             { [CalloutExpression $1] }
      | MethodCall_Expressions_ ',' Expression { (CalloutExpression $3) : $1 }

MethodCall_CalloutArgs
      : MethodCall_CalloutArgs_ { reverse $1 }
      | {-- empty --}           { [] }
MethodCall_CalloutArgs_
      : MethodCall_CalloutArg                             { [$1] }
      | MethodCall_CalloutArgs_ ',' MethodCall_CalloutArg { $3 : $1 }
MethodCall_CalloutArg
      : Expression     { CalloutExpression $1 }
      | stringLiteral  { CalloutStringLit $1 }

Type
      : int      { Type "int" }
      | boolean  { Type "boolean" }

TypeVoid_
      : void     { Type "void" }

Literal
      : intLiteral     { Parser.IntLiteral (read $1) }
      | charLiteral    { Parser.CharLiteral (head $1) }
      | booleanLiteral {
          Parser.BoolLiteral (if $1 == "true" then True else False)
          }

----------------------------------- Haskell -----------------------------------
{
data Program = Program [Declaration] deriving (Eq)
data Declaration = Callout String
                 | Fields (Type, [String])
                 | Method { retType :: Type
                          , name :: String
                          , args :: [Argument]
                          , vars :: [Declaration]
                          , body :: [Statement]}
                 deriving (Eq)

data Type = Type String deriving (Eq)
data Argument = Argument (Type, String) deriving (Eq)
data Statement = Assignment (Expression, Expression) deriving (Eq)
data Location = Location (String, Maybe Expression) deriving (Eq)
data Literal = StringLiteral String
             | IntLiteral Int
             | CharLiteral Char
             | BoolLiteral Bool
             deriving (Eq)
data Expression = BinOpExpression (String, Expression, Expression)
                | NegExpression Expression
                | NotExpression Expression
                | LengthExpression Expression
                | LocationExpression Location
                | LiteralExpression Literal
                | MethodCallExpression (String, [CalloutArg])
                | CondExpression { condition :: Expression
                                 , consequent :: Expression
                                 , alternative :: Expression }
                deriving (Eq)
data AssignOp = AssignmentOp | AddAssignmentOp | SubtractAssignmentOp deriving (Eq)
data CalloutArg = CalloutExpression Expression
                | CalloutStringLit String
                deriving (Eq)

constructAssignmentStatement lhs op rhs =
  case op of AssignmentOp -> Assignment (lhs, rhs)
             AddAssignmentOp -> Assignment (lhs, BinOpExpression ("+", lhs, rhs))
             SubtractAssignmentOp -> Assignment (lhs, BinOpExpression ("-", lhs, rhs))

parseError :: [ScannedToken] -> Either String a
parseError [] = Left "unexpected EOF"
parseError toks =
  Left $ printf "line %d:%d: unexpected token%s '%s'"
                lineNo
                columnNo
                (if (not $ null $ tail toks) then "s" else "")
                badTokenText
  where firstBadToken = head toks
        lineNo = Scanner.line firstBadToken
        columnNo = Scanner.column firstBadToken
        badTokenText = concatMap (show . extractRawToken) toks
}
