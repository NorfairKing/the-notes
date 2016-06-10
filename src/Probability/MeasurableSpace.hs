module Probability.MeasurableSpace where

import           Notes

import           Functions.Basics.Macro
import           Functions.Basics.Terms
import           Logic.FirstOrderLogic.Macro
import           NumberTheory.Macro
import           Sets.Algebra.Intersection.Terms
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
    measureDefinition
    measureSpaceDefinition

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

measureDefinition :: Note
measureDefinition = de $ do
    lab countableAdditivityDefinitionLabel
    s ["Let", m mspace_, "be a", measurableSpace]
    s ["A", measure', "is a", function, m $ fun meas_ univ_ ereals, "with the following three properties"]
    enumerate $ do
        item $ do
            nonNegativity'
            let x = "x"
            ma $ fa (x ∈ univ_) $ meas x >= 0
        item $ do
            nullEmptySet'
            ma $ meas emptyset =: 0
        item $ do
            countableAdditivity'
            newline
            let a = "A"
                n = "n"
                an = a !: n
            s ["Let", m (sequ an n), "be a", sequence, "of", pairwiseDisjunct, sets]
            ma $ meas (setuncmp (nat n) an) =: sumcmp (nat n) (meas an)


measureSpaceDefinition :: Note
measureSpaceDefinition = de $ do
    s ["Let", m mspace_, "be a", measurableSpace, "and let", m meas_, "be a", measure, "then we call", m measp_, "a", measureSpace']




