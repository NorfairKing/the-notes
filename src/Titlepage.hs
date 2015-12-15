module Titlepage (myTitlePage) where

import           Control.Monad        (forM_)
import           Control.Monad.Reader (asks)

import           Prelude              (return)

import qualified Data.Text            as T

import           Notes

titlepageE :: LaTeXC l => l -> l
titlepageE = liftL $ TeXEnv "titlepage" []

myTitlePage :: Note
myTitlePage =
    titlepageE $ do
        raw "\n"
        comm1 "thispagestyle" "empty"
        comm1 "hbox" $ do
            forM_ [1..7] $ \i -> do
                raw "\n"
                comm2 "rule" (raw $ T.pack $ show i ++ "pt") (commS "textheight")
                hspace $ Pt i
            raw "\n"
            comm1 "hspace*" $ raw "0.05" <> commS "textwidth"
            liftL (\a -> TeXComm "parbox" [OptArg (TeXRaw "b"), FixArg (TeXRaw "0.75\\textwidth"), FixArg a]) $ do
                raw "\n"
                noindent
                braces $ do
                    comm2 "fontsize" "80" "90"
                    comm0 "selectfont"
                    textbf "The Notes"
                lnbk
                raw "\n"

                mst <- asks conf_subtitle
                case mst of
                    Nothing -> return ()
                    Just st -> do
                      raw "[1.0\\baselineskip]"
                      huge2 $ textbf $ raw $ T.pack $ st
                      lnbk
                      raw "\n"

                raw "[2.5\\baselineskip]"
                raw "\n"
                huge $ textsc "Tom Sydney Kerckhove"
                lnbk
                raw "\n"
                raw "[4.0\\baselineskip]"

                large $ tabular Nothing [LeftColumn, LeftColumn] $ do
                    "Started" & "September 28, 2015"
                    lnbk
                    "Compiled" & commS "today"
                    lnbk
                    "Commit" & input "commit.tex" -- Make this compile-time.
                    lnbk
                comm1 "vspace" $ raw "0.5\\textheight"













