module Relations.Domain (
    domainAndImage

  , domain
  , image
  ) where

import           Notes

import           Relations.BasicDefinitions (relation)

domainAndImage :: Notes
domainAndImage = notesPart "domain-and-image" body

body :: Note
body = do
  section "Domain and Image"

  domainDefinition
  imageDefinition

  domainIsInversesImage
  imageIsInversesDomain

domain :: Note
domain = ix "domain"

domainDefinition :: Note
domainDefinition = de $ do
    s [the, term "domain", " of a binary relation ", m rel, " between sets ", m a, and, m b, " is the following subset of ", m a]
    ma $ setcmpr x (te y $ tuple x y ∈ rel)
  where
    a = "A"
    b = "B"
    x = "x"
    y = "y"

image :: Note
image = ix "image"

imageDefinition :: Note
imageDefinition = de $ do
    s [the, term "image", or, term "range", " of a binary relation ", m rel, " between sets ", m a, and, m b, " is the following subset of ", m b]
    ma $ setcmpr y (te x $ tuple x y ∈ rel)
  where
    a = "A"
    b = "B"
    x = "x"
    y = "y"

domainIsInversesImage :: Note
domainIsInversesImage = thm $ do
  s [the, domain, " of a ", relation, " is the image of its inverse"]
  ma $ reldom rel =: relimg (relinv rel)

  proof $ align_
    [
      relimg (relinv rel)
      & "" =: setcmpr y (te x $ tuple x y ∈ relinv rel)
      , "" & "" =: setcmpr y (te x $ tuple x y ∈ (setcmpr (tuple y x) (tuple x y ∈ rel)))
      , "" & "" =: setcmpr x (te y $ tuple x y ∈ rel)
      , "" & "" =: reldom rel
    ]
  where
    x = "x"
    y = "y"

imageIsInversesDomain :: Note
imageIsInversesDomain = thm $ do
  s [the, image, " of a ", relation, " is the ", domain, " of its inverse"]
  ma $ relimg rel =: reldom (relinv rel)

  proof $ align_
    [
      reldom (relinv rel)
      & "" =: setcmpr x (te y $ tuple x y ∈ relinv rel)
      , "" & "" =: setcmpr x (te y $ tuple x y ∈ (setcmpr (tuple y x) (tuple x y ∈ rel)))
      , "" & "" =: setcmpr y (te x $ tuple x y ∈ rel)
      , "" & "" =: relimg rel
    ]
  where
    x = "x"
    y = "y"


