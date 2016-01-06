module Macro.Section where

import qualified Text.LaTeX as HT (chapter, section, subsection, subsubsection)

import           Types

chapter :: Note -> Note
chapter n = do
    raw "\n"
    HT.chapter n

section :: Note -> Note
section n = do
    raw "\n"
    HT.section n

subsection :: Note -> Note
subsection n = do
    raw "\n"
    HT.subsection n

subsubsection :: Note -> Note
subsubsection n = do
    raw "\n"
    HT.subsubsection n
