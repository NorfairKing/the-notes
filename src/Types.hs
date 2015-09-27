module Types (
    module Types
  , module Text.LaTeX
  ) where

import           Text.LaTeX

type Note = LaTeXT_ IO

data Notes = NotesPart Part
           | NotesPartList String [Notes]

data Part = Part {
    part_name     :: String
  , part_preamble :: Note
  , part_body     :: Note
  }
