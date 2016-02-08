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
      : CalloutDecl* FieldDecl* {--MethodDecl*--} { Declarations $1 ++ $2 {--++ $3--} }

CalloutDecl
      : callout identifier ';' { Callout $2 }

FieldDecl
      : Type _FieldDecl_Fields ';' { ($1, $2) }

_FieldDecl_Fields
      : _fields { reverse $1 }

_fields
      : _field         { [$1] }
      | _fields _field { $2 : $1 }

_field
      : identifier { $1 }

----------------------------------- Haskell -----------------------------------
{
data Program = Program { className :: String
                       } deriving (Eq)

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
