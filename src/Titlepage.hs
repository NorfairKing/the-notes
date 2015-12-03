module Titlepage (myTitlePage) where

import           Control.Monad (forM_)

import qualified Data.Text     as T

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
            huge $ textbf "The Notes"
            lnbk
            raw "\n"
            raw "[2.5\\baselineskip]"
            raw "\n"
            large $ textsc "Tom Sydney Kerckhove"
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













