module Parser where

import Core

import Control.Monad
import Data.List
import Text.Parsec
import Text.Parsec.Char
import Text.Parsec.Combinator (many1)

type Ctx = [String]
type Term' = [Term] -> Term

findRef :: Ctx -> String -> Maybe(Int)
findRef ctx nam = findIndex (== nam) ctx

type Parser u a = Parsec String u a

which :: Parser u a -> Parser u b -> Parser u (Either a b)
which p q = (Left <$> p) <|> (Right <$> q)

parse' :: Parser u a -> u -> String -> Either ParseError a
parse' p u s = runParser p u "" s

parseWith :: Parser u a -> u -> String -> Either ParseError (a, String)
parseWith p u s = parse' p' u s
  where p' = do
          a <- p
          str <- getInput
          return (a, str)

tokn :: Parser u a -> Parser u a
tokn p = do
  a <- p
  spaces
  return a

reservedNoSpc :: String -> Parser u String
reservedNoSpc s = try $ string s
reserved s = tokn $ reservedNoSpc s

keywords = ["rec", "let", "def", "Typ"]

nameNoSpc :: Parser u String
nameNoSpc = do
  nam <- many1 alphaNum
  case find (nam ==) keywords of
    Just nam -> fail $ nam ++ " is a keyword."
    Nothing  -> return nam
name = tokn $ nameNoSpc

delimNoSpc :: Parser u a -> String -> String -> Parser u a
delimNoSpc p delim1 delim2 = do
  reserved delim1
  a <- p
  reservedNoSpc delim2
  return a
delim p delim1 delim2 = tokn $ delimNoSpc p delim1 delim2

parensNoSpc p = delimNoSpc p "(" ")"
parensNoSpc' p = delimNoSpc p "<" ">"
parens p = delim p "(" ")"
parens' p = delim p "<" ">"

bind :: Parser Ctx (String, Term')
bind = do
  nam <- name
  reserved ":"
  bnd <- term
  return (nam, bnd)

trycomma :: Parser u Bool
trycomma = do
  c <- reserved ","
  return $ c == ","

binds :: Parser Ctx ([String], [Term'])
binds = do
  (nam, bnd) <- bind
  comma <- option False trycomma
  if comma
    then do
    (nams, bnds) <- binds
    return $ (nam : nams, bnd : bnds)
    else
    return ([nam], [bnd])

vars :: Parser Ctx [String]
vars = do
  var <- name
  comma <- option False trycomma
  if comma
    then do
    rest <- vars
    return $ var : rest
    else
    return [var]

terms :: Parser Ctx [(Term', Bool)]
terms = do
  eras <- option False $ ((== "-") <$> reserved "-")
  trm <- term
  comma <- option False trycomma
  if comma
    then do
    rest <- terms
    return $ (trm, eras) : rest
    else
    return [(trm, eras)]

def :: Parser Ctx (String, Term', Term')
def = do
  nam <- name
  reserved ":"
  typ <- term
  trm <- term
  return (nam, typ, trm)

pTyp :: Parser Ctx Term'
pTyp = do
  reserved "Typ"
  return $ \_ -> Typ

pVar :: Parser Ctx Term'
pVar = do
  nam <- name
  ctx <- getState
  case findRef ctx nam of
    Just idx -> return $ \clos -> clos !! idx
    Nothing -> fail $ "Unbound variable " ++ nam

pLam :: Parser Ctx Term'
pLam = do
  x <- try $ which (parens vars) (parens' vars)
  let (eras, ctx') = case x of
        Left  ctx' -> (False, reverse ctx')
        Right ctx' -> (True, reverse ctx')
  ctx <- getState
  modifyState (ctx' ++)
  bod <- term
  putState ctx
  let traverse bod nam = \ctx -> Lam eras nam $ \x -> bod (x : ctx)
  return $ foldl traverse bod ctx'

pAll :: Parser Ctx Term'
pAll = do
  x <- try $ which (parens binds) (parens' binds)
  reserved "->"
  let (eras, ctx', bnds) = case x of
        Left  (ctx', bnds) -> (False, reverse ctx', reverse bnds)
        Right (ctx', bnds) -> (True, reverse ctx', reverse bnds)
  ctx <- getState
  modifyState (ctx' ++)
  bod <- term
  putState ctx
  let traverse bod (nam, bnd) = \ctx -> All eras nam (bnd ctx) $ \x -> bod (x : ctx)
  return $ foldl traverse bod $ zip ctx' bnds

pFix :: Parser Ctx Term'
pFix = do
  reserved "rec "
  ctx <- getState
  nam <- name
  reserved "."
  modifyState (nam :)
  bod <- term
  putState ctx
  return $ \ctx -> Fix nam $ \x -> bod (x : ctx)

pSec :: Parser Ctx Term'
pSec = do
  reserved "${"
  (nam, bnd) <- bind
  reserved "}"
  ctx <- getState
  modifyState (nam :)
  bod <- term
  putState ctx
  return $ \ctx -> Sec nam (bnd ctx) $ \x -> bod (x : ctx)

pAnn :: Parser Ctx Term'
pAnn = try $ parens $ do
  trm <- term
  reserved "::"
  bnd <- term
  return $ \ctx -> (Ann False (trm ctx) (bnd ctx))

pApp :: Parser Ctx Term'
pApp = do
  let followedByParen p = do
        trm <- p
        reserved "("
        return trm
  func <- (try $ followedByParen pVar) <|> (followedByParen $ parens term)
  args <- terms
  reserved ")"
  let traverse func (arg, eras) = \ctx -> App eras (func ctx) (arg ctx)
  return $ foldl traverse func args

term :: Parser Ctx Term'
term =  do
  trm <- pLam <|> pAll <|> pFix <|> pSec <|> pAnn <|> pTyp <|> pApp <|> pVar 
  return trm

termEnd = do
  spaces
  trm <- term
  eof
  return trm

parseTrm st = case parse' termEnd [] st of
  Right cont -> cont []
  Left cont -> error $ show cont

-- Examples
natTyp :: Term
natTyp =
  let
    zero = Lam True "P" $ \_ -> Lam False "z" $ \z -> Lam False "s" $ \s -> z
    succ typ = Ann False (Lam False "n" $ \n -> Lam True "P" $ \_ -> Lam False "z" $ \z -> Lam False "s" $ \s -> App False s n) (All False "" typ $ \_ -> typ)
  in
    Fix "Nat" $ \natTyp ->
    Sec "self" natTyp $ \self ->
    All True "P" (All False "" natTyp $ \_ -> Typ) $ \pTyp ->
    All False "" (App False pTyp zero) $ \_ ->
    All False "" (All False "pred" natTyp $ \pred -> (App False pTyp $ App False (succ natTyp) pred)) $ \_ ->
    App False pTyp self

succtype = All False "" natTyp $ \_ -> natTyp
succterm = Lam False "n" $ \n -> Lam True "P" $ \_ -> Lam False "z" $ \z -> Lam False "s" $ \s -> App False s n

suc = Ann False succterm succtype
zero = Lam True "P" $ \_ -> Lam False "z" $ \z -> Lam False "s" $ \s -> z
one = App False suc zero
two = App False suc one
