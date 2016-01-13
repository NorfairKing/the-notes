module Macro.Graphviz where

import           Prelude
import           Types

import           Control.Monad          (unless)
import           Control.Monad.Reader   (asks)

import           System.Directory       (doesFileExist)
import           System.Exit            (ExitCode (..))
import           System.FilePath.Posix  ((<.>), (</>))
import           System.Process         (readCreateProcessWithExitCode, shell)


import           Macro.Figure

import           Text.Dot

import qualified Crypto.Hash.MD5        as MD5
import qualified Data.ByteString        as SB
import qualified Data.ByteString.Base16 as B16
import qualified Data.ByteString.Char8  as SB8
import qualified Data.Text.Encoding     as T
import qualified Data.Text.IO           as T


dotFig :: Note -> DotGraph -> Note
dotFig cap g = do
    fp <- dot2tex g
    noindent
    hereFigure $ do
        packageDep_ "graphicx"
        includegraphics [KeepAspectRatio True, IGHeight (Cm 3.0), IGWidth (CustomMeasure $ "0.5" <> textwidth)] fp
        caption cap


dot2tex :: DotGraph -> Note' FilePath
dot2tex graph = do
    filedir <- asks conf_tempDir
    let f e = filedir </> filename <.> e
        file_dot = f "dot"
        file_eps = f "eps"
        dotJob = shell $ "dot -Teps " ++ file_dot ++ " > " ++ file_eps

    doneAlready <- liftIO $ doesFileExist file_eps -- This works because we use hashes for the file name
    unless doneAlready $ do
        registerAction filename $ do
            liftIO $ T.writeFile file_dot text

            (ec, out, err) <- liftIO $ readCreateProcessWithExitCode dotJob ""
            case ec of
                ExitSuccess -> return ()
                ExitFailure c -> do
                    liftIO $ putStrLn $ out ++ err
                    liftIO $ print c
                    error $ "Error while generating graph " ++ filename -- FIXME send this to a logfile instead before we start asyncing this code

    return file_eps
  where
    text = renderGraph graph
    -- A unique filename based on content. In the odd case that the content is the same, it doesn't matter.
    filename = SB8.unpack $ SB.take 16 $ B16.encode $ MD5.hash $ T.encodeUtf8 text



