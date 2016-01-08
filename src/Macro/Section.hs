module Macro.Section where

import           Prelude
import           Types

import           Macro.Note

import qualified Text.LaTeX as HT (chapter, section, subsection, subsubsection)


chapter :: Text -> Note
chapter n = do
    raw "\n"
    note (escape n) $ HT.chapter $ raw n

section :: Text -> Note
section n = do
    raw "\n"
    note (escape n) $ HT.section $ raw n

subsection :: Text -> Note
subsection n = do
    raw "\n"
    note (escape n) $ HT.subsection $ raw n

subsubsection :: Text -> Note
subsubsection n = do
    raw "\n"
    note (escape n) $ HT.subsubsection $ raw n

escape :: Text -> Text
escape = id
