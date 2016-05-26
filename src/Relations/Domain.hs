module Relations.Domain where

import           Notes

import           Logic.FirstOrderLogic.Macro
import           Sets.Basics.Terms

import           Relations.Basics.Macro
import           Relations.Basics.Terms

import           Relations.Domain.Macro
import           Relations.Domain.Terms


domainAndImage :: Note
domainAndImage = subsection "Domain and Image" $ do
    domainDefinition
    imageDefinition

    domainIsInversesImage
    imageIsInversesDomain

domainDefinition :: Note
domainDefinition = de $ do
    lab domainDefinitionLabel
    s [the, domain', "of a", binaryRelation, m rel_, "between", sets, m a, and, m b, "is the following", subset, "of", m a]
    ma $ setcmpr x (te y $ tuple x y ∈ rel_)
  where
    a = "A"
    b = "B"
    x = "x"
    y = "y"


imageDefinition :: Note
imageDefinition = de $ do
    lab imageDefinitionLabel
    lab rangeDefinitionLabel
    s [the, image', or, range', "of a", binaryRelation, m rel_, "between", sets, m a, and, m b, "is the following", subset, "of", m b]
    ma $ setcmpr y (te x $ tuple x y ∈ rel_)
  where
    a = "A"
    b = "B"
    x = "x"
    y = "y"

domainIsInversesImage :: Note
domainIsInversesImage = thm $ do
    s [the, domain, " of a ", relation, " is the image of its inverse"]
    ma $ dom rel_ =: img (inv rel_)

    proof $ align_
        [
          img (inv rel_)
          & "" =: setcmpr y (te x $ tuple x y ∈ inv rel_)
          , "" & "" =: setcmpr y (te x $ tuple x y ∈ setcmpr (tuple y x) (tuple x y ∈ rel_))
          , "" & "" =: setcmpr x (te y $ tuple x y ∈ rel_)
          , "" & "" =: dom rel_
        ]
  where
    x = "x"
    y = "y"

imageIsInversesDomain :: Note
imageIsInversesDomain = thm $ do
    s [the, image, " of a ", relation, " is the ", domain, " of its inverse"]
    ma $ img rel_ =: dom (inv rel_)

    proof $ align_
        [
          dom (inv rel_)
          & "" =: setcmpr x (te y $ tuple x y ∈ inv rel_)
          , "" & "" =: setcmpr x (te y $ tuple x y ∈ setcmpr (tuple y x) (tuple x y ∈ rel_))
          , "" & "" =: setcmpr y (te x $ tuple x y ∈ rel_)
          , "" & "" =: img rel_
        ]
  where
    x = "x"
    y = "y"
