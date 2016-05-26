module Probability.MeasurableSpace where

import           Notes

import           Functions.Basics.Macro
import           Functions.Basics.Terms
import           Logic.FirstOrderLogic.Macro
import           Sets.Basics.Terms

import           Probability.Intro.Macro
import           Probability.Intro.Terms
import           Probability.SigmaAlgebra.Macro
import           Probability.SigmaAlgebra.Terms

import           Probability.MeasurableSpace.Macro
import           Probability.MeasurableSpace.Terms


measurableSpaceS :: Note
measurableSpaceS = section "Measurable spaces" $ do
    measurableSpaceDefinition
    trivialMeasurableSpaceDefinition
    measurableFunctionDefinition

measurableSpaceDefinition :: Note
measurableSpaceDefinition = de $ do
    s ["Let", m univ_, "be a", universe, "and let", m sa_, "be a", sa, "on", m univ_]
    s [m mspace_, "is called a", measurableSpace']

trivialMeasurableSpaceDefinition :: Note
trivialMeasurableSpaceDefinition = de $ do
    lab trivialMeasurableSpaceDefinitionLabel
    s ["Let ", m univ_, "be a", universe]
    s [m $ mspace univ_ $ setofs [emptyset, univ_], "is called the", trivialMeasurableSpace]

measurableFunctionDefinition :: Note
measurableFunctionDefinition = de $ do
    lab measurableDefinitionLabel
    lab measurableFunctionDefinitionLabel
    let a = "A"
        b = "B"
        aa = mathcal "A"
        bb = mathcal "B"
    s ["Let", m $ mspace a aa, and, m $ mspace b bb, "be two", measurableSpaces]
    let f_ = "f"
    s ["A", measurableFunction', "is a", function, m $ fun f_ a b, "such that the", preimage, "of every", subset, "of", m b, "in", m bb, "is in", m aa]
    let e = "E"
    ma $ fa (e ∈ bb) $ preim f_ e ∈ aa
    s ["If", m aa, and, m bb, "are unclear from context, we sometimes explicitly say that", m f_, is, abMeasurable aa bb]







