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

import ParseTypes

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
%left NOT
%right '?'
%nonassoc '>' '<' ">=" "<="
%nonassoc "==" "!="
%nonassoc "&&" "||"
%% -------------------------------- Grammar -----------------------------------

Program
      : CalloutDecls { Program $1 }

CalloutDecls
      : CalloutDecl CalloutDecls { $1 : $2 }
      | FieldDecls { $1 }

CalloutDecl
      : callout identifier ';' { Callout $2 }

FieldDecls
      : FieldDecl FieldDecls { $1 : $2 }
      | MethodDecls { $1 }

FieldDecl
      : Type Fields ';' { Fields ($1, $2) }

Fields
      : Field_         { [$1] }
      | Fields ',' Field_ { $3 : $1 }

Field_
      : identifier { ($1, Nothing) }
      | identifier '[' intLiteral ']' { ($1, Just ((read $3) :: Int)) }

MethodDecls
      : MethodDecl MethodDecls { $1 : $2 }
      | {-- empty --}           { [] }

MethodDecl
      : Type identifier '(' Arguments ')' Block {
              Method { methodRetType = $1
                     , methodName = $2
                     , methodArgs = $4
                     , methodBody = $6 }
        }
      | void identifier '(' Arguments ')' Block {
              Method { methodRetType = (Type "void")
                     , methodName = $2
                     , methodArgs = $4
                     , methodBody = $6 }
        }

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
      | MethodCall_ ';'                  { MethodCallStatement $1 }
      | return Expression ';'            { ReturnStatement $2 }
      | continue ';'                     { ContinueStatement }
      | break ';'                        { BreakStatement }
      | while '(' Expression ')' Block   { LoopStatement {loopCondition=$3, loopBody=$5, loopInit=Nothing, loopIncr=Nothing} }
      | for '(' identifier '=' Expression ',' Expression LoopIncr ')' Block
        { LoopStatement {loopCondition=$7, loopBody=$10, loopInit=Just ($3, $5), loopIncr=$8} }
      | if '(' Expression ')' Block OptElse
        { IfStatement {ifCondition=$3, ifConsequentBody=$5, ifAlternativeBody=$6} }

OptElse
      : {-- empty --}    { ([], []) }
      | else Block       { $2 }

LoopIncr
      : {-- empty --}    { Nothing }
      | ',' intLiteral   { Just ((read $2) :: Int) }

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
      | '!' Expression %prec NOT    { NotExpression $2 }
      | '(' Expression ')'          { $2 }
      | '@' identifier              { LengthExpression (LocationExpression (Location ($2, Nothing))) }
      | MethodCall                  { $1 }
      | Expression '?' Expression ':' Expression
                                    { CondExpression {condCondition=$1, condConsequent=$3, condAlternative=$5} }

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
      : MethodCall_ { MethodCallExpression $1 }
MethodCall_
      : identifier '(' MethodCall_CalloutArgs ')' { ($1, $3) }

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

Literal
      : intLiteral     { ParseTypes.IntLiteral (read $1) }
      | charLiteral    { ParseTypes.CharLiteral (head $1) }
      | booleanLiteral {
          ParseTypes.BoolLiteral (if $1 == "true" then True else False)
          }

----------------------------------- Haskell -----------------------------------
{

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
