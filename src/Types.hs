module Types (
    module Types
  , module Text.LaTeX
  , module Text.LaTeX.Base.Class
  , module Text.LaTeX.Base.Pretty
  , module Text.LaTeX.Base.Syntax
  , module Text.LaTeX.Packages.AMSFonts
  , module Text.LaTeX.Packages.AMSMath
  , module Text.LaTeX.Packages.AMSThm
  , module Text.LaTeX.Packages.Fancyhdr
  ) where

import           Text.LaTeX
import           Text.LaTeX.Base.Class
import           Text.LaTeX.Base.Pretty
import           Text.LaTeX.Base.Syntax
import           Text.LaTeX.Packages.AMSFonts
import           Text.LaTeX.Packages.AMSMath
import           Text.LaTeX.Packages.AMSThm   hiding (proof)
import           Text.LaTeX.Packages.Fancyhdr

type Note = LaTeXT_ IO

data Notes = NotesPart String Note
           | NotesPartList String [Notes]

notes :: String -> [Notes] -> Notes
notes = NotesPartList

notesPart :: String -> Note -> Notes
notesPart = NotesPart

data Part = Part String Note
