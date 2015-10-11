{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances  #-}
module Types (
    module Types

  , module Prelude

  , module Text.LaTeX
  , module Text.LaTeX.Base.Class
  , module Text.LaTeX.Base.Pretty
  , module Text.LaTeX.Base.Syntax
  , module Text.LaTeX.Packages.AMSFonts
  , module Text.LaTeX.Packages.AMSMath
  , module Text.LaTeX.Packages.AMSThm
  , module Text.LaTeX.Packages.Fancyhdr

  , module Control.Monad.Reader
  ) where

import           Prelude                      (Eq (..), Fractional (..), IO,
                                               Num (..), Show (..), mempty, ($),
                                               (++), (.))

import           Text.LaTeX                   hiding (item)
import           Text.LaTeX.Base.Class
import           Text.LaTeX.Base.Pretty
import           Text.LaTeX.Base.Syntax
import           Text.LaTeX.Packages.AMSFonts
import           Text.LaTeX.Packages.AMSMath
import           Text.LaTeX.Packages.AMSThm   hiding (proof)
import           Text.LaTeX.Packages.Fancyhdr

import           Control.Monad.Reader         (MonadReader (..), ReaderT, ask,
                                               asks, runReaderT)


type Note = LaTeXT_ (ReaderT Config IO)

data Config = Config {
    conf_selections :: [Selection]
  } deriving (Show, Eq)

data Selection = All
               | Match String
  deriving (Show, Eq)

data Notes = NotesPart String Note
           | NotesPartList String [Notes]

notes :: String -> [Notes] -> Notes
notes = NotesPartList

notesPart :: String -> Note -> Notes
notesPart = NotesPart

data Part = Part String Note

instance Eq Part where
  (Part n1 _) == (Part n2 _) = n1 == n2

instance MonadReader r m => MonadReader r (LaTeXT m) where
  ask   = lift ask
  local = local
  reader = lift . reader

