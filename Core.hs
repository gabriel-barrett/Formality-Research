module Core where

import Control.Monad
import Control.Monad.Writer.Lazy hiding (All)
import Data.Set (Set)
import qualified Data.Set as S
import Data.Map (Map)
import qualified Data.Map.Strict as M

newtype Void = Void Void

type Name = String

data Term
  -- Infinitary lambda calculus
  = Var Name Int                      -- Variable
  | Lam Bool Name (Term -> Term)      -- Lambda
  | App Bool Term Term                -- Application
  | Fix Name (Term -> Term)           -- Fixpoint
  -- Type level
  | Typ                               -- Type type
  | All Bool Name Term (Term -> Term) -- Dependent function
  | Sec Name Term (Term -> Term)      -- Dependent intersection
  | Ann Bool Term Term                -- Type annotation

instance Show Term where
  show t = case t of
    Var name _              ->
      name
    -- Lam name bind body@(Lam _ _ _)     -> concat ["(", n, " : ", go h vs rs, ", ", T.tail $ go b (n : vs) rs]
    -- Lam name bind body                 -> concat ["(", n, " : ", go h vs rs, ") => ", go b (n : vs) rs]
    Lam eras name body      ->
      (if eras then "Λ" else "λ") ++ name ++ ". " ++ show (body (Var name 0))
    App eras func@(App _ _ _) argm      ->
      init (show func) ++ (if eras then " -" else " ") ++ show argm ++ ")"
    App eras func argm      ->
      "(" ++ show func ++ (if eras then " -" else " ") ++ show argm ++ ")"
    Fix name body           ->
      "μ" ++ name ++ ". " ++ show (body (Var name 0))
    Typ                     ->
      "*"
    -- All eras name bind@Typ body -> concat ["∀(", name, "). ", show (body (Var name 0))]
    -- All eras name bind body -> concat ["(", name, " : ", show bind, ") -> ", show (body (Var name 0))]
    All eras name bind body ->
      (if eras then "∀(" else "Π(") ++ name ++ ": " ++ show bind ++ "). " ++ show (body (Var name 0))
    Sec name bind body      ->
      "⋂(" ++ name ++ ": " ++ show bind ++ "). " ++ show (body (Var name 0))
    Ann True term typ       ->
      "{" ++ show term ++ " : " ++ show typ ++ "}"
    Ann False term typ      ->
      "{" ++ show term ++ " ~: " ++ show typ ++ "}"
    -- Ann _ term _             ->
    --   show term

hash t = hash t 0 where
  hash t dep = case t of
    Var _ idx            ->
      if idx < 0 then "^" ++ show (dep + idx) else "#" ++ show idx;
    Lam eras _ body      ->
      (if eras then "Λ" else "λ") ++ hash (body (Var "" (-dep - 1))) (dep + 1)
    App eras func argm   ->
      "@" ++ hash func dep ++ (if eras then "-" else "") ++ hash argm dep
    Fix _ body           ->
      "μ" ++ hash (body (Var "" (-dep - 1))) (dep + 1)
    Typ                  ->
      "*"
    All eras _ bind body ->
      (if eras then "∀" else "Π") ++ hash bind dep ++ hash (body (Var "" (-dep - 1))) (dep + 1)
    Sec _ bind body      ->
      "⋂" ++ hash bind dep ++ hash (body (Var "" (-dep - 1))) (dep + 1)
    Ann _ term _         ->
      hash term dep

instance Eq Term where
  t == s = hash t == hash s

unroll t = case t of
  Fix name body -> body (Fix name body)
  _ -> t

reduce t = case t of
  App eras func argm -> case reduce func of
    Lam _ _ body -> reduce (body argm)
    func         -> App eras func argm
  Fix _ _            -> reduce $ unroll t
  Ann _ term _       -> reduce term
  _                  -> t

equal a b dep seen =
  let a1 = reduce a
      b1 = reduce b
      ah = hash a1
      bh = hash b1
      id = ah ++ bh
  in if ah == bh || S.member id seen then True else
    let seen = S.insert id seen in
      case (a1, b1) of
        (Lam eras1 _ body1, Lam eras2 _ body2)             ->
          (eras1 == eras2)
          && equal (body1 (Var "" dep)) (body2 (Var "" dep)) (dep+1) seen
        (App eras1 func1 argm1, App eras2 func2 argm2)     ->
          (eras1 == eras2)
          && equal func1 func2 dep seen
          && equal argm1 argm2 dep seen
        (All eras1 _ bind1 body1, All eras2 _ bind2 body2) ->
          (eras1 == eras2)
          && equal bind1 bind2 dep seen
          && equal (body1 (Var "" dep)) (body2 (Var "" dep)) (dep+1) seen
        (Sec _ bind1 body1, Sec _ bind2 body2)             ->
          equal bind1 bind2 dep seen
          && equal (body1 (Var "" dep)) (body2 (Var "" dep)) (dep+1) seen
        (_, _)             -> False

-- As of now, only extracts checked type annotations and simplifies intersections
typinfer trm dep seen =
      case trm of
        Ann True trm typ@(Sec _ bind body) ->
          bind : (body trm) : typinfer trm dep seen
        Ann True trm typ ->
          typ : typinfer trm dep seen
        Ann False trm typ ->
          if typcheck trm typ dep seen
          then typinfer (Ann True trm typ) dep seen
          else typinfer trm dep seen
        _ -> []

typcheck trm0 typ0 dep seen0 =
  let
    -- Although we should not reduce terms while typechecking, unrolling a term is ok because
    -- `Fix`is not really part of the lambda calculus (i.e. it is not a constructor) but is
    -- there to indicate that the term is regularly infinite -- neither the typechecker nor the
    -- equality algorithm ever sees `Fix` as a node. To deal with infinities we must keep track
    -- of all pairs that we have already been through. This is entirely analogous to `equal`.
    trm  = unroll trm0
    typ  = reduce typ0
    typh = hash typ0
    trmh = hash trm0
    id   = trmh ++ typh
    seen = S.insert id seen0
  in if S.member id seen0 then True else
    case (trm, typ) of
      -- Cut rule (needs inference)
      (App eras func argm, typ) ->
        let
          check (All eras' name bind body) =
            (eras == eras') && typcheck argm bind dep seen && equal typ (body argm) dep S.empty
          check _ = False
          ftyps = map reduce $ typinfer func dep seen
        in
          foldr (\ftyp res -> res || check ftyp) False ftyps
      -- Annotation
      (Ann True trm' typ', typ) ->
        equal typ' typ dep S.empty || typcheck trm' typ dep seen
      (Ann False trm' typ', typ) ->
        if typcheck trm' typ' dep seen then typcheck (Ann True trm' typ') typ dep seen else False
      -- Type constructors
      (Typ, Typ) ->
        True
      (Sec name bind body, Typ) ->
        typcheck bind Typ dep seen && typcheck (body (Ann True (Var name dep) bind)) typ (dep+1) seen
      (All _ name bind body, Typ) ->
        typcheck bind Typ dep seen && typcheck (body (Ann True (Var name dep) bind)) typ (dep+1) seen
      -- Term rules
      (trm, Sec _ bind body) ->
        let bindh = hash bind
        in typcheck trm bind dep seen && typcheck trm (body trm) dep (S.insert (trmh ++ bindh) seen)
      (Lam eras name body, All eras' name' bind body') ->
        (eras == eras') && typcheck (body (Ann True (Var name dep) bind)) (body' (Var name' dep)) (dep+1) seen
      (_, _) -> False

check trm typ = typcheck trm typ 0 S.empty

-- Debugging
typcheckTrace :: Term -> Term -> Int -> Set String -> Writer [String] Bool
typcheckTrace trm0 typ0 dep seen0 = do
  let trm  = unroll trm0
  let typ  = reduce typ0
  let output = ["Checking " ++ show trm ++ " against " ++ show typ]
  let typh = hash typ
  let trmh = hash trm
  let id   = trmh ++ typh
  let seen = S.insert id seen0
  if S.member id seen0 then return True else
    case (trm, typ) of
      (App eras func argm, typ) -> do
        let fcheck (All eras' name bind body) = do
              check <- typcheckTrace argm bind dep seen
              let res = (eras == eras') && check && equal typ (body argm) dep S.empty
              tell $ ["Checking type: " ++ show check]
              tell $ ["Checking equal: " ++ show (equal typ (body argm) dep S.empty)] ++ output
              return $ res
            fcheck trm = do
              return False
        let ftyps = map reduce $ typinfer func dep seen
        let traverse ftyp mres = do
              res <- mres
              check <- fcheck ftyp
              return $ res || check
        res <- foldr traverse (return False) ftyps
        tell $ ["With result: " ++ show res] ++ output
        tell $ map (\typ -> " - " ++ show typ) ftyps ++ ["FTYPS: "]
        return res
      (Ann True trm' typ', typ) -> do
        let eq = equal typ' typ dep S.empty
        check <- typcheckTrace trm' typ dep seen
        let res = eq || check
        tell $ ["With result: " ++ show res] ++ output
        return $ res
      (Ann False trm' typ', typ) -> do
        check2 <- typcheckTrace (Ann True trm' typ') typ dep seen
        check1 <- typcheckTrace trm' typ' dep seen
        let res = if check1 then check2 else False
        tell $ ["With result: " ++ show res] ++ output
        return $ res
      (Typ, Typ) -> do
        tell $ ["With result: " ++ show True] ++ output
        return True
      (Sec name bind body, Typ) -> do
        check2 <- typcheckTrace (body (Ann True (Var name dep) bind)) typ (dep+1) seen
        check1 <- typcheckTrace bind Typ dep seen
        let res = check1 && check2
        tell $ ["With result: " ++ show res] ++ output
        return $ res
      (All _ name bind body, Typ) -> do
        check2 <- typcheckTrace (body (Ann True (Var name dep) bind)) typ (dep+1) seen
        check1 <- typcheckTrace bind Typ dep seen
        let res = check1 && check2
        tell $ ["With result: " ++ show res] ++ output
        return $ res
      (trm, Sec _ bind body) -> do
        let bindh = hash bind
        check2 <- typcheckTrace trm (body trm) dep (S.insert (trmh ++ bindh) seen)
        check1 <- typcheckTrace trm bind dep seen
        let res = check1 && check2
        tell $ ["With result: " ++ show res] ++ output
        return $ res
      (Lam eras name body, All eras' name' bind body') -> do
        check <- typcheckTrace (body (Ann True (Var name dep) bind)) (body' (Var name' dep)) (dep+1) seen
        let res = (eras == eras') && check
        tell $ ["With result: " ++ show res] ++ output
        return $ res
      (_, _) -> do
        tell $ ["With result: " ++ show False] ++ output
        return False

checkTrace trm typ = do
  let (result, output) = runWriter $ typcheckTrace trm typ 0 S.empty
  forM_ (reverse $ output) putStrLn
  return result

-- As of now, only extracts checked type annotations and simplifies intersections,
-- taking care of infinite intersections.
-- typinfer trm dep seen =
--   aux trm S.empty
--   where
--     aux trm seen' =
--       case trm of
--         Ann True trm typ@(Sec _ bind body) ->
--           let typh = hash typ
--           in if S.member typh seen'
--           then bind : (body trm) : aux trm (S.insert typh seen')
--           else bind : (body trm) : aux trm (S.insert typh seen')
--         Ann True trm typ -> typ : aux trm seen'
--         Ann False trm typ ->
--           if typcheck trm typ dep seen
--           then aux (Ann True trm typ) seen'
--           else aux trm seen'
--         _ -> []
