module Relations.Main (relations) where

import           Notes

import           Relations.Basics      (basicDefinitions)
import           Relations.Domain      (domainAndImage)
import           Relations.Equivalence (equivalenceRelations)
import           Relations.Orders      (orders)
import           Relations.Preorders   (preorders)


relations :: Note
relations = note "relations" $ do
    chapter "Relations"
    basicDefinitions
    domainAndImage
    preorders
    equivalenceRelations
    orders



