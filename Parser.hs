module Parser where

import Core

import Control.Monad
import Data.List
import qualified Data.Map.Strict as M
import Text.Parsec
import Text.Parsec.Char
import Text.Parsec.Combinator (many1)

type Ctx = [String]
type Ref = M.Map String Term
type PState = (Ctx, Ref)
type Term' = [Term] -> Term

type Parser u a = Parsec String u a

which :: Parser u a -> Parser u b -> Parser u (Either a b)
which p q = (Left <$> p) <|> (Right <$> q)

tokn :: Parser u a -> Parser u a
tokn p = do
  a <- p
  spaces
  return a

reserved :: String -> Parser u String
reserved s = tokn $ try $ string s

keywords = ["rec", "let", "def", "Typ"]

name :: Parser u String
name = tokn $ do
  nam <- many1 alphaNum
  case find (nam ==) keywords of
    Just nam -> fail $ nam ++ " is a keyword."
    Nothing  -> return nam


delim :: Parser u a -> String -> String -> Parser u a
delim p delim1 delim2 = tokn $ do
  reserved delim1
  a <- p
  reserved delim2
  return a

parens p = delim p "(" ")"
parens' p = delim p "<" ">"

bind :: Parser PState (String, Term')
bind = do
  nam <- name
  reserved ":"
  bnd <- term
  return (nam, bnd)

trycomma :: Parser u Bool
trycomma = do
  c <- reserved ","
  return $ c == ","

binds :: Parser PState ([String], [Term'])
binds = do
  (nam, bnd) <- bind
  comma <- option False trycomma
  if comma
    then do
    (nams, bnds) <- binds
    return $ (nam : nams, bnd : bnds)
    else
    return ([nam], [bnd])

vars :: Parser PState [String]
vars = do
  var <- name
  comma <- option False trycomma
  if comma
    then do
    rest <- vars
    return $ var : rest
    else
    return [var]

terms :: Parser PState [Term']
terms = do
  trm <- term
  comma <- option False trycomma
  if comma
    then do
    rest <- terms
    return $ trm : rest
    else
    return [trm]

pTyp :: Parser PState Term'
pTyp = do
  reserved "Typ"
  return $ \_ -> Typ

pVar :: Parser PState Term'
pVar = do
  nam <- name
  (ctx, refs) <- getState
  case (findIndex (== nam) ctx, M.lookup nam refs) of
    (Just idx, _) -> return $ \clos -> clos !! idx
    (_, Just trm) -> return $ \clos -> trm
    (_, _) -> fail $ "Unbound variable " ++ nam

pLam :: Parser PState Term'
pLam = do
  x <- try $ which (parens vars) (parens' vars)
  let (eras, ctx') = case x of
        Left  ctx' -> (False, reverse ctx')
        Right ctx' -> (True, reverse ctx')
  (ctx, trms) <- getState
  modifyState $ \(ctx, trms) -> (ctx' ++ ctx, trms)
  bod <- term
  putState (ctx, trms)
  let traverse bod nam = \ctx -> Lam eras nam $ \x -> bod (x : ctx)
  return $ foldl traverse bod ctx'

pAll :: Parser PState Term'
pAll = do
  x <- try $ which (parens binds) (parens' binds)
  reserved "->"
  let (eras, ctx', bnds) = case x of
        Left  (ctx', bnds) -> (False, reverse ctx', reverse bnds)
        Right (ctx', bnds) -> (True, reverse ctx', reverse bnds)
  (ctx, trms) <- getState
  modifyState $ \(ctx, trms) -> (ctx' ++ ctx, trms)
  bod <- term
  putState (ctx, trms)
  let traverse bod (nam, bnd) = \ctx -> All eras nam (bnd ctx) $ \x -> bod (x : ctx)
  return $ foldl traverse bod $ zip ctx' bnds

pFix :: Parser PState Term'
pFix = do
  reserved "rec "
  nam <- name
  reserved "."
  (ctx, trms) <- getState
  modifyState $ \(ctx, trms) -> (nam : ctx, trms)
  bod <- term
  putState (ctx, trms)
  return $ \ctx -> Fix nam $ \x -> bod (x : ctx)

pSec :: Parser PState Term'
pSec = do
  reserved "${"
  (nam, bnd) <- bind
  reserved "}"
  (ctx, trms) <- getState
  modifyState $ \(ctx, trms) -> (nam : ctx, trms)
  bod <- term
  putState (ctx, trms)
  return $ \ctx -> Sec nam (bnd ctx) $ \x -> bod (x : ctx)

pAnn :: Parser PState Term'
pAnn = try $ parens $ do
  trm <- term
  reserved "::"
  bnd <- term
  return $ \ctx -> (Ann False (trm ctx) (bnd ctx))

pApp :: Parser PState (Term' -> Term')
pApp = do
  x <- try $ which (parens terms) (parens' terms)
  let (eras, args) = case x of
        Left  args -> (False, args)
        Right args -> (True, args)
  let traverse func arg = \ctx -> App eras (func ctx) (arg ctx)
  return $ \func -> foldl traverse func args

term :: Parser PState Term'
term =  do
  let prim = pLam <|> pAll <|> pFix <|> pSec <|> pAnn <|> pTyp
  let app = pVar <|> parens term
  trm <- which prim app
  case trm of
    Left trm -> return trm
    Right func -> do
      conts <- many pApp
      return $ foldl (flip ($)) func conts

def :: Parser PState (String, Term, Term)
def = do
  nam <- name
  reserved ":"
  typ <- term
  modifyState $ \(_, trms) -> ([], trms)
  trm <- term
  let def = Ann False (trm []) (typ [])
  modifyState $ \(_, trms) -> ([], M.insert nam def trms)
  return (nam, trm [], typ [])

runFile :: SourceName -> String -> Either ParseError [(String, Term, Term)]
runFile srcnam src = runParser p ([], M.empty) srcnam src
  where p = do
          spaces
          refs <- many1 def
          eof
          return refs
