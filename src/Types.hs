{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances  #-}
module Types (
    module Types

  , module P

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
                                                    (&&), (++), (.))

import           Text.LaTeX                   hiding (Label, alph_, article,
                                               cite, item, label, pageref, ref,
                                               ref, rule, usepackage)
import           Text.LaTeX.Base.Class
import           Text.LaTeX.Base.Pretty
import           Text.LaTeX.Base.Syntax
import           Text.LaTeX.Packages.AMSFonts
import           Text.LaTeX.Packages.AMSMath  hiding (subset, (!:), (^:))
import           Text.LaTeX.Packages.AMSThm   hiding (TheoremStyle (..), proof,
                                               theorem)
import           Text.LaTeX.Packages.Color
import           Text.LaTeX.Packages.Fancyhdr
import           Text.LaTeX.Packages.Graphicx

import           Control.Monad.Reader         (ReaderT)
import           Control.Monad.State          (StateT)

import           Text.LaTeX.LambdaTeX         hiding (label, note, pageref, ref)

type Note  = Note' ()
type Note' = ΛTeXT (StateT State (ReaderT Config IO))

data State = State

data Args = Args {
      args_selectionString       :: String
    , args_visualDebug           :: Bool
    , args_verbose               :: Bool
    , args_ignoreReferenceErrors :: Bool
    , args_omitTodos             :: Bool
    , args_subtitle              :: String
    , args_texFileName           :: String
    , args_bibFileName           :: String
    , args_pdfFileName           :: String
    } deriving (Show, Eq)

data Config = Config {
      conf_selection             :: Selection
    , conf_visualDebug           :: Bool
    , conf_verbose               :: Bool
    , conf_ignoreReferenceErrors :: Bool
    , conf_omitTodos             :: Bool
    , conf_subtitle              :: Maybe String
    , conf_texFileName           :: FilePath
    , conf_bibFileName           :: FilePath
    , conf_pdfFileName           :: FilePath
    } deriving (Show, Eq)

data Label = Label RefKind Text

data RefKind = Definition
             | Theorem
             | Proposition
             | Property
             | Example
             | Figure
  deriving (Show, Eq)
