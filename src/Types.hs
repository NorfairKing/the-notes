{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances  #-}
module Types (
      module Types

    , module P
    , module Debug.Trace

    , module Text.LaTeX.LambdaTeX

    , module Text.LaTeX
    , module Text.LaTeX.Base.Class
    , module Text.LaTeX.Base.Pretty
    , module Text.LaTeX.Base.Syntax
    , module Text.LaTeX.Packages.AMSFonts
    , module Text.LaTeX.Packages.AMSMath
    , module Text.LaTeX.Packages.AMSThm
    , module Text.LaTeX.Packages.Fancyhdr
    , module Text.LaTeX.Packages.Color
    , module Text.LaTeX.Packages.Graphicx
    ) where

import           Prelude                      (Bool (..))
import           Prelude                      as P (Double, Eq (..), FilePath,
                                                    Fractional (..), IO,
                                                    Maybe (..), Num (..),
                                                    Show (..), mempty, ($),
                                                    (&&), (.))

import           Debug.Trace
import           System.Random

import           Text.LaTeX                   hiding (Label, alph_, article,
                                               chapter, cite, item, label,
                                               pageref, paragraph, ref, ref,
                                               rule, section, subsection,
                                               subsubsection, usepackage)
import           Text.LaTeX.Base.Class
import           Text.LaTeX.Base.Pretty
import           Text.LaTeX.Base.Syntax
import           Text.LaTeX.Packages.AMSFonts
import           Text.LaTeX.Packages.AMSMath  hiding (bullet, div_, equation,
                                               mp, partial, pm, subset, to,
                                               (!:), (^:))
import           Text.LaTeX.Packages.AMSThm   hiding (TheoremStyle (..), proof,
                                               theorem)
import           Text.LaTeX.Packages.Color
import           Text.LaTeX.Packages.Fancyhdr
import           Text.LaTeX.Packages.Graphicx

import           Control.DeepSeq              (NFData (..))
import           Control.Monad.Reader         (ReaderT)
import           Control.Monad.State          (StateT)
import           System.Exit                  (ExitCode (..))

import           Text.LaTeX.LambdaTeX         hiding (label, note, pageref, ref)

type Note  = Note' ()
type Note' = ΛTeXT (StateT State (ReaderT Config IO))

data State = State
    { state_rng :: StdGen
    }

data Args = Args {
      args_selectionString       :: String
    , args_visualDebug           :: Bool
    , args_fast                  :: Bool
    , args_verbose               :: Bool
    , args_ignoreReferenceErrors :: Bool
    , args_todos                 :: Bool
    , args_subtitle              :: String
    , args_texFileName           :: String
    , args_bibFileName           :: String
    , args_pdfFileName           :: String
    , args_tempDir               :: FilePath
    , args_outDir                :: FilePath
    } deriving (Show, Eq)

data Config = Config {
      conf_selection             :: Selection
    , conf_visualDebug           :: Bool
    , conf_fast                  :: Bool
    , conf_verbose               :: Bool
    , conf_ignoreReferenceErrors :: Bool
    , conf_todos                 :: Bool
    , conf_subtitle              :: Maybe String
    , conf_texFileName           :: FilePath
    , conf_bibFileName           :: FilePath
    , conf_pdfFileName           :: FilePath
    , conf_tempDir               :: FilePath
    , conf_outDir                :: FilePath
    } deriving (Show, Eq)

data Label = MkLabel RefKind Text

data RefKind = Definition
             | Theorem
             | Proposition
             | Property
             | Example
             | Figure
             | Note
             | Lemma
    deriving (Show, Eq)



-- TODO: keep Until Deepseq 1.4.2.0
-- |/Since: 1.4.2.0/
instance NFData ExitCode where
    rnf (ExitFailure n) = rnf n
    rnf ExitSuccess     = ()

