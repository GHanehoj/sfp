-- | @futhark lda@
module Futhark.CLI.LDA (main) where

import Futhark.Compiler
import Futhark.Util.Options
import Language.Futhark
import Language.Futhark.LDA
import Language.Futhark.Semantic
import System.FilePath.Posix qualified as Posix
import Data.List (find)
import Data.Maybe (fromJust, catMaybes)


-- | Run @futhark lda@.
main :: String -> [String] -> IO ()
main = mainWithOptions () [] "program" $ \args () ->
  case args of
    [file] -> do
      Just $ do
        (_, imports, _) <- readProgramOrDie file
        let prog = fileProg $ fromJust $ containingModule imports file
        -- print prog
        let deps = map (decExps $ progDecs prog) $ progDecs prog
        print $ catMaybes deps
    _ -> Nothing

containingModule :: Imports -> String -> Maybe FileModule
containingModule imports file =
  snd <$> find ((== file') . fst) imports
  where
    file' = mkInitialImport $ fst $ Posix.splitExtension file


decExps :: [Dec] -> Dec -> Maybe DAResult
decExps decs dec =
  case dec of
    ValDec d -> Just $ expDependencies decs $ valBindBody d
    _ -> Nothing
