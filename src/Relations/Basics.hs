module Relations.Basics (
    relationBasics

  , relation
  ) where

import           Notes

import           Relations.BasicDefinitions
import           Relations.Composite
import           Relations.Domain

relationBasics :: Notes
relationBasics = notes "basics"
  [
    basicDefinitions
  , domainAndImage
  , compositeRelations
  ]
