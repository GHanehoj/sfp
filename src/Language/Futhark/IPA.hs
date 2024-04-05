{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use lambda-case" #-}
-- Module for performing Irregular Parallelism Analysis (IPA)
module Language.Futhark.IPA
(
  analyseProgram
)
where

import Control.Monad.State
import Control.Monad.Except

import Data.Map qualified as M
import Data.Set qualified as S
import Data.Loc
import Data.Maybe (fromJust)
import Data.List (find)
import Data.List.NonEmpty (toList)
import Data.Bifunctor (bimap)
import Language.Futhark
import Language.Futhark.GDA (expDependencies, emptyExp)


-----------------
-- SETUP & API --
-----------------
analyseProgram :: Prog -> Bool
analyseProgram prog =
  let initS = initState $ progDecs prog in
  let initS' = addIntrinsicInfo initS in
  let main = mainName initS in
  case runAnalysisM (analyseFunc main) initS' of
    Left _ -> False
    Right _ -> True

-- find expression of "main" function
mainName :: M.Map VName FuncData -> VName
mainName s =
  case find (\(VName n _, _) -> n == "main") $ M.toList s of
    Just (name, _) -> name
    Nothing -> error "no main function"

addIntrinsicInfo :: M.Map VName FuncData -> M.Map VName FuncData
addIntrinsicInfo s = foldl addIntrinsic s $ M.toList intrinsics
  where
    addIntrinsic :: M.Map VName FuncData -> (VName, Intrinsic) -> M.Map VName FuncData
    addIntrinsic s' (fName, IntrinsicPolyFun typeParams params rType) =
      let intrinsicData = FuncData {
          sizeParams = extractSizeParams typeParams,
          valueParams = map (VName (nameFromString "") 0,) params,
          body = emptyExp,
          rType = rType,
          analysisInfo = 
            case find (\(name, _) -> name == baseString fName) intrinsicsInfo of
              Just (_, info) -> Just $ mkInfo typeParams params info 
              _ -> Nothing
        } in
      M.insert fName intrinsicData s'
    addIntrinsic s' _ = s'

    intrinsicsInfo :: [(String, ([Bool], [Bool]))]
    intrinsicsInfo = [
        ("map", ([True], [False, False])),
        ("reduce", ([True], [False, False, False]))
      ]
    mkInfo :: [TypeParam] -> [ParamType] -> ([Bool], [Bool]) -> FuncInfo
    mkInfo typeParams params info = 
      let sizeParams = extractSizeParams typeParams in
      let valueParams = map (\_ -> VName (nameFromString "") 0) params in
      bimap (zip sizeParams) (zip valueParams) info

initState :: [DecBase Info VName] -> M.Map VName FuncData
initState [] = M.empty
initState ((ValDec dec):decs) = M.insert (valBindName dec) (funcInfoFromDec dec) $ initState decs
initState (_:decs) = initState decs

funcInfoFromDec :: ValBindBase Info VName -> FuncData
funcInfoFromDec dec = FuncData {
    sizeParams = extractSizeParams $ valBindTypeParams dec,
    valueParams = concatMap patternMap $ valBindParams dec,
    body = valBindBody dec,
    rType = unInfo $ valBindRetType dec,
    analysisInfo = Nothing
  }

extractSizeParams :: [TypeParam] -> [VName]
extractSizeParams [] = []
extractSizeParams ((TypeParamDim name _):rest) = name:extractSizeParams rest
extractSizeParams (_:rest) = extractSizeParams rest


--------------------
-- TYPES & MONADS --
--------------------

data FuncData = FuncData {
  sizeParams :: [VName],
  valueParams :: [(VName, ParamType)], -- for now, only supporting simple parameter patterns
  body :: Exp,
  rType :: ResRetType,
  analysisInfo :: Maybe FuncInfo
}
--                    Sizes            Values
type FuncInfo = ([(VName, Bool)], [(VName, Bool)])

-- Monad used for analysis of full program.
-- Tracks marked sizes and parameters,
-- and throws exception on IP detection
newtype AnalysisM a =
  AnalysisM (ExceptT SrcLoc (State (M.Map VName FuncData)) a)
  deriving (Functor, Applicative, Monad, MonadState (M.Map VName FuncData))
flagIP :: SrcLoc -> AnalysisM a
flagIP loc = AnalysisM $ throwError loc
getFuncData :: VName -> AnalysisM FuncData
getFuncData fName = state (\s -> (fromJust $ M.lookup fName s, s)) -- typechecker should ensure we always hit
addFuncInfo :: VName -> FuncInfo -> AnalysisM ()
addFuncInfo fName info = modify $ M.adjust (\v -> v{analysisInfo=Just info}) fName
runAnalysisM :: AnalysisM a -> M.Map VName FuncData -> Either SrcLoc a -- Get function list and use as initval
runAnalysisM (AnalysisM am) = evalState (runExceptT am)


--------------------
-- IMPLEMENTATION --
--------------------
-- Ensure analysis of function 'fName' is done and return resulting info
-- Non-recusiveness of futhark ensures no infinite loop 
analyseFunc :: VName -> AnalysisM FuncInfo
analyseFunc fName = do
  funcData <- getFuncData fName
  case analysisInfo funcData of
    Just info -> pure info
    Nothing -> do
      let env = fst $ expDependencies $ body funcData
      markedNames <- analyseExp env (body funcData)
      let info = mkFuncInfo markedNames funcData
      addFuncInfo fName info
      pure info

mkFuncInfo :: S.Set VName -> FuncData -> FuncInfo
mkFuncInfo markedNames funcData =
  (markParams $ sizeParams funcData, markParams $ map fst $ valueParams funcData)
  where
    markParams = map (\name -> (name, name `elem` markedNames))

-- Analyse function
analyseExp :: M.Map VName [VName] -> Exp -> AnalysisM (S.Set VName)
analyseExp env = analyse
  where
    analyse e =
      case e of
        Literal {} -> pure S.empty
        IntLit {} -> pure S.empty
        FloatLit {} -> pure S.empty
        StringLit {} -> pure S.empty
        Hole {} -> pure S.empty
        Var {} -> pure S.empty
        Parens e' _ -> analyse e'
        -- QualParens {} ->
        -- TupLit {} ->
        -- RecordLit {} ->
        -- ArrayLit {} ->
        -- Attr {} ->
        -- Project {} ->
        -- Negate {} ->
        -- Not {} ->
        -- Assert {} ->
        -- Constr {} ->
        -- Update {} ->
        -- RecordUpdate {} ->
        Lambda pats body _ _ loc -> do
          let boundNames = S.fromList $ concatMap patNames pats
          bodyMarks <- analyse body
          unless (S.disjoint boundNames bodyMarks) $ flagIP loc
          pure bodyMarks
        -- OpSection {} ->
        -- OpSectionLeft {} ->
        -- OpSectionRight {} ->
        -- ProjectSection {} ->
        -- IndexSection {} ->
        -- Ascript {} ->
        -- Coerce {} ->
        AppExp ae _ ->
          case ae of
            -- Simple function application
            Apply (Var (QualName _ fName) _ _) args loc -> do
              (sizeParamInfo, valueParamInfo) <- analyseFunc fName
              let argList = map snd $ toList args
              -- For each argument, if called function's parameter is marked,
              -- then mark argument dependencies in this function
              let markedValueParams = map fst $ filter snd $ zip argList $ map snd valueParamInfo
              valueMarks <- fmap S.unions $ forM markedValueParams $ \e' -> markDeps env loc (snd $ expDependencies e')

              -- For each argument, if type of the called function's parameter depends on
              -- a marked size, mark corresponding sizes in this function
              let markedSizeParams = map fst $ filter snd sizeParamInfo
              paramTypes <- fmap snd . valueParams <$> getFuncData fName
              let argTypes = map typeOf argList
              sizeMarks <- fmap S.unions $
                forM (zip argTypes paramTypes) $
                  uncurry $ markSizes env loc markedSizeParams

              argMarks <- S.unions <$> mapM analyse argList
              pure $ S.unions [valueMarks, sizeMarks, argMarks]
            Apply f args _ -> do
              let argList = map snd $ toList args
              fMarks <- analyse f
              argMarks <- S.unions <$> mapM analyse argList
              pure $ S.unions [fMarks, argMarks]
            -- Range {} ->
            LetPat _ _ e1 e2 _ -> do -- TODO: support more complex patterns
              e1Marks <- analyse e1
              e2Marks <- analyse e2
              pure $ S.union e1Marks e2Marks
            -- LetFun {} ->
            -- If {} ->
            -- Loop {} ->
            -- BinOp {} ->
            -- LetWith {} ->
            -- Index {} ->
            -- Match {} ->
            _ -> pure S.empty
        _ -> pure S.empty


markDeps :: M.Map VName [VName] -> SrcLoc -> [VName] -> AnalysisM (S.Set VName)
markDeps env loc names =
  fmap S.unions $
    forM names $ \name ->
      case M.lookup name env of
        Nothing -> pure $ S.singleton name -- Function param
        Just [] -> pure $ S.singleton name -- Lambda variable
        Just deps -> markDeps env loc deps -- Let definition


-- Match argument size with parameter size, and mark argument typenames that
-- correspond to marked size parameters 
markSizes :: M.Map VName [VName] -> SrcLoc -> [VName] -> StructType -> ParamType -> AnalysisM (S.Set VName)
markSizes env loc markedSizeParams argType pType = do
  case (argType, pType) of
    (Scalar _, Scalar _) -> pure S.empty -- todo: support more complex patterns
    (Array _ Shape{shapeDims=aDims} _, Array _ Shape{shapeDims=pDims} _) ->
        fmap S.unions $ forM (zip aDims pDims) $ \(aDim, pDim) ->
          if any (`elem` markedSizeParams) $ snd $ expDependencies pDim
            then markDeps env loc (snd $ expDependencies aDim)
            else pure S.empty
    _ -> pure S.empty
