module Macro.Section where

import           Prelude
import           Types

import           Macro.Note

import qualified Text.LaTeX as HT (chapter, paragraph, section, subsection,
                                   subsubsection)


chapter :: Text -> Note -> Note
chapter n func = do
    raw "\n"
    note n $ do
        HT.chapter (raw n)
        func

section :: Text -> Note -> Note
section n func = do
    raw "\n"
    note n $ do
        HT.section (raw n)
        func

subsection :: Text -> Note -> Note
subsection n func = do
    raw "\n"
    note n $ do
        HT.subsection (raw n)
        func

subsubsection :: Text -> Note -> Note
subsubsection n func = do
    raw "\n"
    note n $ do
        HT.subsubsection (raw n)
        func

paragraph :: Text -> Note -> Note
paragraph n func = do
    raw "\n"
    note n $ do
        HT.paragraph (raw n)
        func

