{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use lambda-case" #-}
-- Module for performing Local Dependency Analysis (LDA)
module Language.Futhark.LDA ( expDependencies, emptyExp, addBindings, DAResult (..) , Lam (..) )
where


import Control.Monad.Reader
import Data.Map qualified as M
import Data.Loc
import Data.List.NonEmpty (toList)
import Language.Futhark qualified as F
import Language.Futhark hiding (Lambda)

newtype DepAnM a =
  DepAnM (Reader (M.Map VName Lam) a)
  deriving (Functor, Applicative, Monad, MonadReader (M.Map VName Lam))
getLam :: VName -> DepAnM (Maybe Lam)
getLam fName = asks (M.lookup fName) -- typechecker should ensure we always hit
runDepAnM :: DepAnM a -> M.Map VName Lam -> a
runDepAnM (DepAnM am) = runReader am


-------------------------
-- DEPENDENCY ANALYSIS --
-------------------------
emptyExp :: Exp
emptyExp = Literal (BoolValue True) $ SrcLoc $ Loc (Pos "" 0 0 0) (Pos "" 0 0 0)

data DAResult
  = Simple [VName]
  | Tuple [DAResult]
  | Lambda Lam
  deriving Show

data Lam = Lam Env [Pat ParamType] Exp
  deriving Show
mergeBranchDA :: DAResult -> DAResult -> DAResult
mergeBranchDA (Simple deps1) (Simple deps2) = Simple (deps1++deps2)
mergeBranchDA (Tuple _) (Tuple _) = error "todo"
mergeBranchDA (Lambda _) _ = error "Lambdas as branch results should be impossible"
mergeBranchDA _ (Lambda _) = error "Lambdas as branch results should be impossible"
mergeBranchDA _ _ = error "Incomparable types should be impossible"

addDepsToDA :: [VName] -> DAResult -> DAResult
addDepsToDA deps (Simple deps2) = Simple (deps++deps2)
addDepsToDA _ (Tuple _) = error "todo"
addDepsToDA _ _ = error "todo"


type Env = M.Map VName DAResult

-- expandDeps :: Env -> DAResult -> DAResult
-- expandDeps env names = Nothing
  -- bindings <- get
  -- fmap concat $ forM names $ \name -> 
  --   case M.lookup name bindings of
  --     Nothing -> pure [name]       -- External variable
  --     Just [] -> pure []           -- Lambda variable
  --     Just deps -> expandDeps deps -- Let definition

-- Find the variable names that expression e depends on
-- expDependenciesRec :: Exp -> (M.Map VName DAResult, DAResult)
-- expDependenciesRec e = runDepM $ expDependenciesRec e

expDependencies :: [Dec] -> Exp -> DAResult
expDependencies decs e =
  let lamMap = mkLamMap decs
  in runDepAnM (expDependenciesRec M.empty e) lamMap
  where
    mkLamMap :: [Dec] -> M.Map VName Lam
    mkLamMap [] = M.empty
    mkLamMap ((ValDec dec):rest) = M.insert (valBindName dec) (lamFromDec dec) $ mkLamMap rest
    mkLamMap (_:rest) = mkLamMap rest
    lamFromDec :: ValBind -> Lam
    lamFromDec dec = Lam M.empty (valBindParams dec) (valBindBody dec)

expDependenciesRec :: Env -> Exp -> DepAnM DAResult
expDependenciesRec env e =
  case e of
    Literal {} -> pure $ Simple []
    IntLit {} -> pure $ Simple []
    FloatLit {} -> pure $ Simple []
    StringLit {} -> pure $ Simple []
    Hole {} -> pure $ Simple []
    Var (QualName _ name) _ _ -> do
      foundLam <- getLam name
      case foundLam of
        Nothing ->
          case M.lookup name env of
            Nothing -> pure $ Simple [name]
            Just eDA -> pure eDA
        Just lam -> pure $ Lambda lam
    Parens e' _ -> expDependenciesRec env e'
    -- QualParens {} ->
    -- TupLit args _ -> concat <$> mapM expDependenciesRec args
    -- RecordLit {} ->
    -- ArrayLit elems _ _ -> concat <$> mapM expDependenciesRec elems
    -- Attr {} ->
    -- Project {} ->
    Negate e' _ -> expDependenciesRec env e'
    Not e' _ -> expDependenciesRec env e'
    -- Assert {} ->
    -- Constr {} ->
    -- Update {} ->
    -- RecordUpdate {} ->
    F.Lambda params body _ _ _ -> pure $ Lambda $ Lam env params body
    -- OpSection {} ->
    -- OpSectionLeft {} ->
    -- OpSectionRight {} ->
    -- ProjectSection {} ->
    -- IndexSection {} ->
    -- Ascript {} ->
    -- Coerce {} ->
    AppExp ae _ ->
      case ae of
        Apply fExp args _ -> do
          lam <- funcDependencies env fExp
          let argsList = map snd $ toList args
          lamDependenciesRec env lam argsList
        -- Range {} ->
        LetPat _ pat e1 e2 _ -> do
          e1DA <- expDependenciesRec env e1
          let env' = addBindings pat e1DA env
          expDependenciesRec env' e2
          
        -- LetFun {} ->
        If eCond eTrue eFalse _ -> do
          eCondDeps <- simpleDependencies env eCond -- guaranteed boolean type
          eTrueDA <- expDependenciesRec env eTrue
          eFalseDA <- expDependenciesRec env eFalse
          pure $ addDepsToDA eCondDeps $ mergeBranchDA eTrueDA eFalseDA
        -- Loop {} ->
        BinOp _ _ (e1, _) (e2, _) _ -> do
          e1Deps <- simpleDependencies env e1
          e2Deps <- simpleDependencies env e2
          pure $ Simple (e1Deps ++ e2Deps)
        -- LetWith {} ->
        -- Index {} ->
        -- Match {} ->
        _ -> pure $ Simple []
    _ -> pure $ Simple []

simpleDependencies :: Env -> Exp -> DepAnM [VName]
simpleDependencies env e = do
  eDA <- expDependenciesRec env e
  case eDA of
    Simple deps -> pure deps
    _ -> error "not a simple value"

funcDependencies :: Env -> Exp -> DepAnM Lam
funcDependencies env fExp = do
  fDA <- expDependenciesRec env fExp
  case fDA of
    Lambda lam -> pure lam
    _ -> error "not a function"

lamDependenciesRec :: Env -> Lam -> [Exp] -> DepAnM DAResult
lamDependenciesRec _ (Lam closure [] body) _ = expDependenciesRec closure body
lamDependenciesRec _ lam [] = pure $ Lambda lam
lamDependenciesRec env (Lam closure (p1:pRest) body) (a1:aRest) = do
  a1DA <- expDependenciesRec env a1
  let closure' = addBindings p1 a1DA closure
  lamDependenciesRec env (Lam closure' pRest body) aRest


addBindings :: Pat a -> DAResult -> Env -> Env
addBindings pat eDA env =
  case (pat, eDA) of
    -- (TuplePat pats _, TupLit args _) -> forM_ (zip pats args) $ uncurry addBindings
    -- (RecordPat pats _, RecordLit fields _) -> 

    -- (TuplePat pats _, e) -> forM_ pats $ \pat' -> addBindings pat' e
    -- (RecordPat fields _, e) -> forM_ fields $ \(_, pat') -> addBindings pat' e
    (PatParens pat' _, _) -> addBindings pat' eDA env
    (Id name _ _, _) ->
      M.insert name eDA env
    (Wildcard _ _, _) -> env
    (PatAscription pat' _ _, _) -> addBindings pat' eDA env
    (PatLit {}, _) -> env
    -- (PatConstr {}, e) ->
    (PatAttr _ pat' _, _) -> addBindings pat' eDA env
    _ -> env
