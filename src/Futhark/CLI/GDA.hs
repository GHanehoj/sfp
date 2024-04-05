-- | @futhark gda@
module Futhark.CLI.GDA (main) where

import Futhark.Compiler
import Futhark.Util.Options
import Language.Futhark
import Language.Futhark.GDA
import Language.Futhark.Semantic
import System.FilePath.Posix qualified as Posix
import Data.List (find)
import Data.Maybe (fromJust)
import Data.Map qualified as M


-- | Run @futhark gda@.
main :: String -> [String] -> IO ()
main = mainWithOptions () [] "program" $ \args () ->
  case args of
    [file] -> do
      Just $ do
        (_, imports, _) <- readProgramOrDie file
        let prog = fileProg $ fromJust $ containingModule imports file
        -- print prog
        let deps = map decExps $ progDecs prog
        print $ M.unions deps
    _ -> Nothing

containingModule :: Imports -> String -> Maybe FileModule
containingModule imports file =
  snd <$> find ((== file') . fst) imports
  where
    file' = mkInitialImport $ fst $ Posix.splitExtension file


decExps :: DecBase Info VName -> M.Map VName [VName]
decExps dec =
  case dec of
    ValDec d -> fst $ expDependencies $ valBindBody d
    _ -> M.empty
  