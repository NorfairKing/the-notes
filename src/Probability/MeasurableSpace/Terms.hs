module Probability.MeasurableSpace.Terms where

import           Notes

makeDefs
    [ "measurable space"
    , "measurable"
    , "measurable function"
    , "trivial measurable space"
    ]

abMeasurable :: Note -> Note -> Note
abMeasurable a b = m (tuple a b) <> "-" <> measurable

abMeasurable' :: Note -> Note -> Note
abMeasurable' a b = m (tuple a b) <> "-" <> measurable'
