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

  , modify
  ) where
import           Prelude                      (Eq (..), FilePath,
                                               Fractional (..), IO, Maybe (..),
                                               Num (..), Show (..), mempty, ($),
                                               (&&), (++), (.))

import           Text.LaTeX                   hiding (Label, article, cite,
                                               item, ref)
import           Text.LaTeX.Base.Class
import           Text.LaTeX.Base.Pretty
import           Text.LaTeX.Base.Syntax
import           Text.LaTeX.Packages.AMSFonts
import           Text.LaTeX.Packages.AMSMath
import           Text.LaTeX.Packages.AMSThm   hiding (TheoremStyle (..), proof)
import           Text.LaTeX.Packages.Fancyhdr

import           Control.Monad.Reader         (MonadReader (..), ReaderT, ask,
                                               asks, runReaderT)
import           Control.Monad.State          (MonadState (..), StateT, get,
                                               gets, modify, put, runStateT)


type Note = LaTeXT_ (StateT State (ReaderT Config IO))

data State = State {
    state_refs :: [Reference]
  } deriving (Show, Eq)

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

instance MonadState s m => MonadState s (LaTeXT m) where
  get = lift get
  put = lift . put
  state = lift . state


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

