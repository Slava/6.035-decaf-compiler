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

  charLiteral { ScannedToken _ _ (CharLiteral $$) }
  booleanLiteral { ScannedToken _ _ (BooleanLiteral $$) }
  intLiteral { ScannedToken _ _ (IntLiteral $$) }
  stringLiteral { ScannedToken _ _ (StringLiteral $$) }

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
      : Arguments_ { reverse $1 }

Arguments_
      : {-- empty --}           { [] }
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
      : ';' { Statement }

Type
      : int      { Type "int" }
      | boolean  { Type "boolean" }

TypeVoid_
      : void     { Type "void" }

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
data Statement = Statement deriving (Eq)

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
