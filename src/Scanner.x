-- Scanner -- Decaf scanner                                     -*- haskell -*-
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
{-# OPTIONS_GHC -w #-}
module Scanner ( ScannedToken(..)
               , Token(..)
               , scan
               , formatTokenOrError
               ) where
}

%wrapper "6.035"


----------------------------------- Tokens ------------------------------------

$digit = [0-9]
$alpha = [a-zA-Z]
@char = (\\[\\nt\'\"]|[\x20-\x7e] # [\'\"\\])
@hex = "0x" [0-9a-fA-F]+
@number = $digit+

tokens :-
  $white+ ;
  "//".*  ;                     -- comment
  boolean | break | callout | continue | else | for | while | if | int | return | void
          { \posn s -> scannedToken posn $ Keyword s }
  true | false
          { \posn s -> scannedToken posn $ BooleanLiteral s }
  @hex | @number
          { \posn s -> scannedToken posn $ IntLiteral s }
  \" @char* \"
          { \posn s -> scannedToken posn $ StringLiteral s }
  \{      { \posn _ -> scannedToken posn LCurly }
  \}      { \posn _ -> scannedToken posn RCurly }
  ($alpha|_)($alpha|_|$digit)*
          { \posn s -> scannedToken posn $ Identifier s }
  \' @char \'
          { \posn s -> scannedToken posn $ CharLiteral (tail (init s)) }


----------------------------- Representing tokens -----------------------------

{
-- | A token with position information.
data ScannedToken = ScannedToken { line :: Int
                                 , column :: Int
                                 , extractRawToken :: Token
                                 } deriving (Eq)

-- | A token.
data Token = Keyword String
           | Identifier String
           | CharLiteral String
           | BooleanLiteral String
           | IntLiteral String
           | StringLiteral String
           | LCurly
           | RCurly
           deriving (Eq)
instance Show Token where
  show (Keyword k) = k
  show (Identifier s) = "IDENTIFIER " ++ s
  show LCurly = "{"
  show RCurly = "}"
  show (CharLiteral c) = "CHARLITERAL '" ++ c ++ "'"
  show (BooleanLiteral b) = "BOOLEANLITERAL " ++ b
  show (IntLiteral i) = "INTLITERAL " ++ i
  show (StringLiteral s) = "STRINGLITERAL " ++ s

{-| Smart constructor to create a 'ScannedToken' by extracting the line and
column numbers from an 'AlexPosn'. -}
scannedToken :: AlexPosn -> Token -> ScannedToken
scannedToken (AlexPn _ lineNo columnNo) tok = ScannedToken lineNo columnNo tok


---------------------------- Scanning entry point -----------------------------

scan :: String -> [Either String ScannedToken]
scan = alexScanTokens

formatTokenOrError :: Either String ScannedToken -> Either String String
formatTokenOrError (Left err) = Left err
formatTokenOrError (Right tok) = Right $ unwords [ show $ line tok
                                                 , show $ extractRawToken tok
                                                 ]
}
