module UtilsSpec (spec) where

import           Prelude
import           Test.Hspec
import           Test.QuickCheck

import           Utils


spec :: Spec
spec = do
    describe "pluralOf" $ do
        let pluralExamples = sequence_ . map (\(a, b) -> shouldBe (pluralOf a) b)
        it "works for these regular examples" $ pluralExamples
            [
                ("boat"         , "boats")
              , ("house"        , "houses")
              , ("cat"          , "cats")
              , ("river"        , "rivers")
            ]
        it "works for these examples that need \"es\"" $ pluralExamples
            [
                ("bus"          ,     "buses")
              , ("wish"         ,    "wishes")
              , ("pitch"        ,   "pitches")
              , ("box"          ,     "boxes")
            ]
        it "works for these examples that need \"ies\"" $ pluralExamples
            [
                ("penny"        , "pennies")
              , ("spy"          , "spies")
              , ("baby"         , "babies")
              , ("city"         , "cities")
              , ("daisy"        , "daisies")
            ]
        it "works for these examples that need \"ses\"" $ pluralExamples
            [
                ("hypothesis"   , "hypotheses")
              , ("parenthesis"  , "parentheses")
            ]
        it "works for these irregulars" $ pluralExamples
            [
                ("woman"      , "women")
              , ("man"        , "men")
              , ("child"      , "children")
              , ("tooth"      , "teeth")
              , ("foot"       , "feet")
              , ("person"     , "people")
              , ("leaf"       , "leaves")
              , ("mouse"      , "mice")
              , ("goose"      , "geese")
              , ("half"       , "halves")
              , ("knife"      , "knives")
              , ("wife"       , "wives")
              , ("life"       , "lives")
              , ("elf"        , "elves")
              , ("loaf"       , "loaves")
              , ("potato"     , "potatoes")
              , ("tomato"     , "tomatoes")
              , ("cactus"     , "cacti")
              , ("focus"      , "foci")
              , ("fungus"     , "fungi")
              , ("nucleus"    , "nuclei")
              , ("syllabus"   , "syllabi/syllabuses")
              , ("analysis"   , "analyses")
              , ("diagnosis"  , "diagnoses")
              , ("oasis"      , "oases")
              , ("thesis"     , "theses")
              , ("crisis"     , "crises")
              , ("phenomenon" , "phenomena")
              , ("criterion"  , "criteria")
              , ("datum"      , "data")
            ]
        -- it "works for these irregulars that stay the same" $ return ()

