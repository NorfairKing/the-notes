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
import           Prelude                      (Eq (..), FilePath,
                                               Fractional (..), IO, Maybe (..),
                                               Num (..), Show (..), mempty, ($),
                                               (&&), (++), (.))

import           Text.LaTeX                   hiding (Label, cite, item, ref)
import           Text.LaTeX.Base.Class
import           Text.LaTeX.Base.Pretty
import           Text.LaTeX.Base.Syntax
import           Text.LaTeX.Packages.AMSFonts
import           Text.LaTeX.Packages.AMSMath
import           Text.LaTeX.Packages.AMSThm   hiding (TheoremStyle (..), proof)
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

data Notes = NotesPart String Note [Reference]
           | NotesPartList String [Notes]

notes :: String -> [Notes] -> Notes
notes = NotesPartList

notesPart :: String -> Note -> Notes
notesPart name body = NotesPart name body []

notesPartRef :: String -> Note -> [Reference] -> Notes
notesPartRef = NotesPart

data Part = Part String Note [Reference]

instance Eq Part where
  (Part n1 _ rfs1) == (Part n2 _ rfs2) = n1 == n2 && rfs1 == rfs2


instance MonadReader r m => MonadReader r (LaTeXT m) where
  ask   = lift ask
  local = local
  reader = lift . reader


data Label = Label RefKind Note
  deriving (Show, Eq)

data RefKind = Definition
             | Theorem
             | Proposition
             | Property
  deriving (Show, Eq)

type ReferenceType = String

data Reference = Reference ReferenceType String [(String, String)] -- Type Label
  deriving (Show, Eq)

