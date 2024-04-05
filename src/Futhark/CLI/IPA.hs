-- | @futhark ipa@
module Futhark.CLI.IPA (main) where

import Futhark.Compiler
import Futhark.Util.Options
import Language.Futhark.IPA
import Language.Futhark.Semantic
import System.FilePath.Posix qualified as Posix
import Data.List (find)
import Data.Maybe (fromJust)


-- | Run @futhark ipa@.
main :: String -> [String] -> IO ()
main = mainWithOptions () [] "program" $ \args () ->
  case args of
    [file] -> do
      Just $ do
        (_, imports, _) <- readProgramOrDie file
        let prog = fileProg $ fromJust $ containingModule imports file
        -- print prog
        print $ analyseProgram prog
    _ -> Nothing

containingModule :: Imports -> String -> Maybe FileModule
containingModule imports file =
  snd <$> find ((== file') . fst) imports
  where
    file' = mkInitialImport $ fst $ Posix.splitExtension file
