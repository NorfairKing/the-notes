module Macro.Graphviz where

import           Prelude
import           Types

import           System.Exit            (ExitCode (..))
import           System.FilePath.Posix  ((<.>), (</>))
import           System.Process         (CreateProcess,
                                         readCreateProcessWithExitCode, shell)

import qualified Crypto.Hash.MD5        as MD5
import qualified Data.ByteString        as SB
import qualified Data.ByteString.Base16 as B16
import qualified Data.ByteString.Char8  as SB8
import qualified Data.Text.Encoding     as T
import qualified Data.Text.IO           as T

dot2tex :: Text -> Note' FilePath
dot2tex text = do
    liftIO $ T.writeFile file_dot text

    (ec, out, err) <- liftIO $ readCreateProcessWithExitCode dotJob ""
    case ec of
        ExitSuccess -> return ()
        ExitFailure c -> do
            liftIO $ putStrLn $ out ++ err
            liftIO $ print c
            error $ "Generating graph" ++ filename -- FIXME send this to a logfile instead

    return file_eps
  where
    filename = SB8.unpack $ SB.take 16 $ B16.encode $ MD5.hash $ T.encodeUtf8 text
    filedir = "/tmp"
    f e = filedir </> filename <.> e
    file_dot = f "dot"
    file_eps = f "eps"

    dotJob :: CreateProcess
    dotJob = shell $ "dot -Teps " ++ file_dot ++ " > " ++ file_eps



