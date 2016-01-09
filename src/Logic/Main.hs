module Logic.Main where

import           Notes

import           Logic.AbstractLogic
import           Logic.FirstOrderLogic
import           Logic.HoareLogic
import           Logic.PropositionalLogic
import           Logic.SeparationLogic
import           Logic.TemporalLogic


logica :: Note
logica = chapter "Logic" $ do
    abstractLogic
    propositionalLogicS
    firstOrderLogicS
    hoareLogicS
    separationLogicS
    temporalLogicS

