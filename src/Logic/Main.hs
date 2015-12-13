module Logic.Main (logica) where

import           Notes

import           Logic.AbstractLogic      (abstractLogic)
import           Logic.FirstOrderLogic
import           Logic.HoareLogic         (hoareLogicS)
import           Logic.PropositionalLogic (propositionalLogicS)
import           Logic.SeparationLogic    (separationLogicS)
import           Logic.TemporalLogic      (temporalLogicS)


logica :: Note
logica = note "logic" $ do
    chapter "Logic"
    abstractLogic
    propositionalLogicS
    firstOrderLogic
    hoareLogicS
    separationLogicS
    temporalLogicS

