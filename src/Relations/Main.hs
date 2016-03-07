module Relations.Main (relations) where

import           Notes

import           Relations.Basics
import           Relations.Domain
import           Relations.Equivalence
import           Relations.Orders
import           Relations.Preorders


relations :: Note
relations = chapter "Relations" $ do
    basicDefinitions
    domainAndImage
    preorders
    equivalenceRelationS
    orders



