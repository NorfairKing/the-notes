module Macro.Tikz where

import           Prelude
import           Types

import           Control.Monad         (unless)
import           Control.Monad.Reader  (asks)

import           System.Directory      (doesFileExist)
import           System.Exit           (ExitCode (..))
import           System.FilePath.Posix (dropExtension, (<.>), (</>))
import           System.Process        (readCreateProcessWithExitCode, shell)

import qualified Data.Text             as T
import qualified Data.Text.IO          as T

import           Macro.Figure

import           Utils


tikzFig :: Note -> [Note] -> Note -> Note
tikzFig cap args content = do
    fp <- tikzpicture args content
    noindent
    hereFigure $ do
        packageDep_ "standalone"
        fromLaTeX $ TeXComm "includestandalone" [OptArg "mode=image", FixArg (TeXRaw $ T.pack $ dropExtension fp)]
        caption cap

tikzpicture :: [Note] -> Note -> Note' FilePath
tikzpicture args l = do
    -- packageDep_ "tikz" -- Not even needed?

    lt <- extractΛLaTeX_ $ tikzpicture' args l
    let doc = tikzDoc lt
    let text = render doc
    filedir <- asks conf_tempDir
    let filename = hashContent text
        f e = filedir </> filename <.> e
        file_tex = f "tex"
        file_pdf = f "pdf"
        latexmkjob = shell $ "latexmk -pdf " ++ file_tex
    doneAlready <- liftIO $ doesFileExist file_pdf
    unless doneAlready $ do
        registerAction ("Tikzpicture: " ++ filename) $ do
            liftIO $ T.writeFile file_tex text

            (ec, out, err) <- liftIO $ readCreateProcessWithExitCode latexmkjob ""
            case ec of
                ExitSuccess -> return ()
                ExitFailure c -> do
                    liftIO $ putStrLn $ out ++ err
                    liftIO $ print c
                    error $ "Error while generating tikz picture " ++ filename -- FIXME send this to a logfile instead before we start asyncing this code

    return file_pdf

tikzpicture' :: [Note] -> Note -> Note
tikzpicture' args l = liftListL (\(l:args) -> TeXEnv "tikzpicture" [MOptArg args] l) (l:args)

-- Option for tikz libraries?
tikzDoc :: LaTeX -> LaTeX
tikzDoc content = mconcat
    [
      TeXComm "documentclass" [OptArg "tikz", FixArg "standalone"]
    , TeXComm "usepackage" [FixArg "pgfplots"]
    , TeXEnv "document" [] content
    ]

axis :: [Note] -> Note -> Note
axis args l = do
    packageDep_ "pgfplots"
    liftListL (\(l:args) -> TeXEnv "axis" [MOptArg args] l) (l:args)

addPlot :: [Note] -> Note -> Note
addPlot args l = (<> ";") $ (liftListL $ \(l:args) -> TeXComm "addplot" [MOptArg args, FixArg l]) (l:args)

(=-) :: Note -> Note -> Note
(=-) = liftL2 $ \a b -> a <> "=" <> b




