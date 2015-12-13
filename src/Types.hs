{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances  #-}
module Types (
    module Types

  , module P

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

  , ask, asks
  ) where

import           Prelude                      (Bool (..), Ord (..))
import           Prelude                      as P (Double, Eq (..), FilePath,
                                                    Fractional (..), IO,
                                                    Maybe (..), Num (..),
                                                    Show (..), mempty, ($),
                                                    (&&), (++), (.))

import           Data.Set

import           Text.LaTeX                   hiding (Label, alph_, article,
                                               cite, item, ref, rule)
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

import           Control.Monad.Reader         (MonadReader (..), ReaderT, ask,
                                               asks)
import           Control.Monad.State          (MonadState (..), StateT, get,
                                               put)


type Note = LaTeXT_ (StateT State (ReaderT Config IO))
type Note' = LaTeXT (StateT State (ReaderT Config IO))

data State = State {
      state_refs     :: Set Reference
    , state_packages :: Set PackageDep
    } deriving (Show, Eq)

data Args = Args {
      args_selectionStrings      :: [String]
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
      conf_selections            :: [Selection]
    , conf_visualDebug           :: Bool
    , conf_verbose               :: Bool
    , conf_ignoreReferenceErrors :: Bool
    , conf_omitTodos             :: Bool
    , conf_subtitle              :: Maybe String
    , conf_texFileName           :: FilePath
    , conf_bibFileName           :: FilePath
    , conf_pdfFileName           :: FilePath
    } deriving (Show, Eq)

data Selection = All
               | Match String
               | Ignore String
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

data RefKind = Definition
             | Theorem
             | Proposition
             | Property
             | Example
             | Figure
  deriving (Show, Eq)

type ReferenceType = String

data Reference = Reference ReferenceType String [(String, String)] -- Type Label
  deriving (Show, Eq)

instance Ord Reference where
    compare (Reference _ r1 _) (Reference _ r2 _) = compare r1 r2

data PackageDep = PackageDep String [TeXArg]
  deriving (Show, Eq)

instance Ord PackageDep where
    compare (PackageDep n1 _) (PackageDep n2 _) = compare n1 n2
