module Parser where

import Core
import Text.Parsec
import Text.Parsec.Char
import Text.Parsec.Combinator (many1)

type Parser u a = Parsec String u a

combine :: Parser u a -> Parser u b -> Parser u (Either a b)
combine p q = (Left <$> p) <|> (Right <$> q)

parse' :: Parser u a -> u -> String -> Either ParseError a
parse' p u s = runParser p u "" s

parseWith :: Parser u a -> u -> String -> Either ParseError (a, String)
parseWith p u s = parse' p' u s
  where p' = do
          a <- p
          str <- getInput
          return (a, str)

tok :: Parser u a -> Parser u a
tok p = do
  a <- p
  spaces
  return a

reserved :: String -> Parser u String
reserved s = tok $ string s

name :: Parser u String
name = tok $ many1 alphaNum

bind :: Parser u (String, Term)
bind = do
  nam <- name
  reserved ":"
  trm <- term
  return (nam, trm)

trycomma :: Parser u Bool
trycomma = do
  c <- reserved ","
  return $ c == ","

binds :: Parser u [(String, Term)]
binds = do
  bnd <- bind
  comma <- option False trycomma
  if comma
    then do
    bnds <- binds
    return $ bnd : bnds
    else
    return [bnd]

vars :: Parser u [String]
vars = do
  var <- name
  comma <- option False trycomma
  if comma
    then do
    rest <- vars
    return $ var : rest
    else
    return [var]

def :: Parser u (String, Term, Term)
def = do
  nam <- name
  reserved ":"
  typ <- term
  trm <- term
  return (nam, typ, trm)

pTyp :: Parser u Term
pTyp = do
  reserved "Typ"
  return Typ

-- TODO
term :: Parser u Term
term = pTyp
