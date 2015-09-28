module Macro.Section where

import qualified Data.Text as T

import           Types


notesChapter :: Text -> Note
notesChapter title = do
  chapter $ raw title
  label . raw $ T.concat ["ch:", T.toLower title]

notesSection :: Text -> Note
notesSection title = do
  section $ raw title
  label . raw $ T.concat ["sec:", T.toLower title]
