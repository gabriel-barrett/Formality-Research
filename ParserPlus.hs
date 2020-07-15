module ParserPlus where

import CorePlus

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

keywords = ["new", "use1", "use2", "rec", "let", "def", "Typ"]

name :: Bool -> Parser u String
name empty = tokn $ do
  nam <- (if empty then many else many1) alphaNum
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
  nam <- name True
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
  var <- name True
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
  reserved "Type"
  return $ \_ -> Typ

pVar :: Parser PState Term'
pVar = do
  nam <- name False
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
  nam <- name False
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

pNew :: Parser PState Term'
pNew = do
  reserved "new("
  trm <- term
  reserved ")"
  return $ \ctx -> New $ trm ctx

pUs1 :: Parser PState Term'
pUs1 = do
  reserved "use1("
  trm <- term
  reserved ")"
  return $ \ctx -> New $ trm ctx

pUs2 :: Parser PState Term'
pUs2 = do
  reserved "use2("
  trm <- term
  reserved ")"
  return $ \ctx -> New $ trm ctx

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

pCom :: Parser PState ()
pCom = do
  reserved "/*"
  manyTill anyChar (reserved "*/")
  return ()

term :: Parser PState Term'
term =  do
  let prim = pAnn <|> pLam <|> pAll <|> pFix <|> pSec <|> pTyp <|> pNew <|> pUs1 <|> pUs2
  let app = pVar <|> parens term
  trm <- which prim app
  case trm of
    Left trm -> return trm
    Right func -> do
      conts <- many pApp
      return $ foldl (flip ($)) func conts

def :: Parser PState (String, Term, Term)
def = do
  nam <- name False
  reserved ":"
  typ <- term
  reserved "="
  modifyState $ \(_, trms) -> ([], trms)
  trm <- term
  let def = Ann False (trm []) (typ [])
  modifyState $ \(_, trms) -> ([], M.insert nam def trms)
  return (nam, trm [], typ [])

defs :: Parser PState [(String, Term, Term)]
defs = do
  pCom <|> return ()
  ref <- def
  refs <- option [] $ try defs
  return $ ref : refs

runFile :: SourceName -> String -> Either ParseError [(String, Term, Term)]
runFile srcnam src = runParser p ([], M.empty) srcnam src
  where p = do
          spaces
          refs <- defs
          pCom <|> return ()
          eof
          return refs

parseTrm src = case runParser term ([], M.empty) "" src of
  Left err -> error $ show err
  Right trm -> trm []
