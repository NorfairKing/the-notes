module Macro.MachineLearning.Macro where

import           Types

import           Macro.MetaMacro

mlos :: Note
mlos = mathcal "O"

mldom :: Note
mldom = mathbb "K"

mlmes :: Note
mlmes = "X"

mlal :: Note
mlal = mathcal "A"

-- Machine learning Hypothesis class
mlhc :: Note
mlhc = mathcal "F"

-- Machine Learning Noise Vector
mlnv :: Note
mlnv = epsilon

mlnv_ :: Note -> Note
mlnv_ n = mlnv !: n

-- Machine Learning Data
mldata :: Note
mldata = mathbb "Z"

-- Machine Learning Model
mlm :: Note
mlm = "f"

-- Machine Learning Model Parameters
mlmp :: Note
mlmp = theta

