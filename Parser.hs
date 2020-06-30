module Parser where

import Core
import Text.Parsec
import Text.Parsec.Char (anyChar)
import Text.Parsec.Char
import Text.Parsec.String (Parser)
import Text.Parsec.Combinator (many1)

parse' :: Parser a -> String -> Either ParseError a
parse' p s = parse p "" s

spc :: Parser ()
spc = skipMany $ oneOf [' ', '\t', '\n']

spc1 :: Parser ()
spc1 = skipMany1 $ oneOf [' ', '\t', '\n']

sep :: Parser ()
sep = do
  spc
  char ':'
  spc

name :: Parser String
name = many1 alphaNum

bind :: Parser (String, Term)
bind = do
  nam <- name
  sep
  trm <- term
  return (nam, trm)

trycomma :: Parser Bool
trycomma = do
  c <- char ','
  return $ c == ','

binds :: Parser [(String, Term)]
binds = do
  bnd <- bind
  spc
  comma <- option False trycomma
  spc
  if comma
    then do
    bnds <- binds
    return $ bnd : bnds
    else
    return [bnd]

vars :: Parser [String]
vars = do
  var <- name
  spc
  comma <- option False trycomma
  spc
  if comma
    then do
    rest <- vars
    return $ var : rest
    else
    return [var]


def :: Parser (String, Term, Term)
def = do
  nam <- name
  sep
  typ <- term
  spc1
  trm <- term
  return (nam, typ, trm)

-- TODO
term :: Parser Term
term = do
  string "Typ"
  return Typ
