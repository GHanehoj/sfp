{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use lambda-case" #-}
-- Module for performing Global Dependency Analysis (GDA)
module Language.Futhark.GDA ( expDependencies, emptyExp )
where

import Control.Monad.State

import Data.Map qualified as M
import Data.Loc
import Data.Tuple (swap)
import Data.List.NonEmpty (toList)

import Language.Futhark

-------------------------
-- DEPENDENCY ANALYSIS --
-------------------------
emptyExp :: Exp
emptyExp = Literal (BoolValue True) $ SrcLoc $ Loc (Pos "" 0 0 0) (Pos "" 0 0 0)


type DepM = State (M.Map VName [VName])
addBinding :: VName -> [VName] -> DepM ()
addBinding name deps = modify $ M.insert name deps
expandDeps :: [VName] -> DepM [VName]
expandDeps names = do
  bindings <- get
  fmap concat $ forM names $ \name -> 
    case M.lookup name bindings of
      Nothing -> pure [name]       -- External variable
      Just [] -> pure []           -- Lambda variable
      Just deps -> expandDeps deps -- Let definition
runDepM :: DepM [VName] -> (M.Map VName [VName], [VName])
runDepM m = swap $ runState m M.empty

-- Find the variable names that expression e depends on
expDependencies :: Exp -> (M.Map VName [VName], [VName])
expDependencies e = runDepM $ expDependenciesRec e

expDependenciesRec :: Exp -> DepM [VName]
expDependenciesRec e =
  case e of
    Literal {} -> pure []
    IntLit {} -> pure []
    FloatLit {} -> pure []
    StringLit {} -> pure []
    Hole {} -> pure []
    Var (QualName _ name) _ _ -> pure [name]
    Parens e' _ -> expDependenciesRec e'
    -- QualParens {} ->
    TupLit args _ -> concat <$> mapM expDependenciesRec args
    -- RecordLit {} ->
    ArrayLit elems _ _ -> concat <$> mapM expDependenciesRec elems
    -- Attr {} ->
    -- Project {} ->
    Negate e' _ -> expDependenciesRec e'
    Not e' _ -> expDependenciesRec e'
    -- Assert {} ->
    -- Constr {} ->
    -- Update {} ->
    -- RecordUpdate {} ->
    Lambda params body _ _ _ -> do
        forM_ params $ \param ->
          addBindings param emptyExp
        bodyDeps <- expDependenciesRec body
        expandDeps bodyDeps
    -- OpSection {} ->
    -- OpSectionLeft {} ->
    -- OpSectionRight {} ->
    -- ProjectSection {} ->
    -- IndexSection {} ->
    -- Ascript {} ->
    -- Coerce {} ->
    AppExp ae _ ->
      case ae of
        Apply (Var (QualName _ _) _ _) args _ -> do -- dont depend on function names
          let argExps = map snd $ toList args
          concat <$> mapM expDependenciesRec argExps
        Apply fExp args _ -> do
          fDeps <- expDependenciesRec fExp
          let argExps = map snd $ toList args
          argDeps <- concat <$> mapM expDependenciesRec argExps
          pure $ argDeps ++ fDeps
        -- Range {} ->
        LetPat _ pat e1 e2 _ -> do
          addBindings pat e1
          e2Deps <- expDependenciesRec e2
          expandDeps e2Deps
        -- LetFun {} ->
        If eCond eTrue eFalse _ -> do
          eCondDeps <- expDependenciesRec eCond
          eTrueDeps <- expDependenciesRec eTrue
          eFalseDeps <- expDependenciesRec eFalse
          pure $ eCondDeps ++ eTrueDeps ++ eFalseDeps
        -- Loop {} ->
        BinOp _ _ (e1, _) (e2, _) _ -> do
          e1Deps <- expDependenciesRec e1
          e2Deps <- expDependenciesRec e2
          pure $ e1Deps ++ e2Deps
        -- LetWith {} ->
        -- Index {} ->
        -- Match {} ->
        _ -> pure []
    _ -> pure []


addBindings :: Pat a -> Exp -> DepM ()
addBindings pat e1 =
  case (pat, e1) of
    (TuplePat pats _, TupLit args _) -> forM_ (zip pats args) $ uncurry addBindings
    -- (RecordPat pats _, RecordLit fields _) -> 

    (TuplePat pats _, e) -> forM_ pats $ \pat' -> addBindings pat' e
    (RecordPat fields _, e) -> forM_ fields $ \(_, pat') -> addBindings pat' e
    (PatParens pat' _, e) -> addBindings pat' e
    (Id name _ _, e) -> do
      eDeps <- expDependenciesRec e
      addBinding name eDeps
    (Wildcard _ _, _) -> pure ()
    -- (PatAscription {}, e) ->
    (PatLit {}, _) -> pure ()
    -- (PatConstr {}, e) ->
    -- (PatAttr {}, e) ->
    _ -> pure ()
