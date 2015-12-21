module Macro (
    module Macro
  , module X
  ) where

import           Types

import           Macro.Array                 as X
import           Macro.Arrows                as X
import           Macro.Code                  as X
import           Macro.Figure                as X
import           Macro.Framed                as X
import           Macro.Graphviz              as X
import           Macro.Index                 as X
import           Macro.Math                  as X
import           Macro.MetaMacro             as X
import           Macro.Reference             as X
import           Macro.Text                  as X
import           Macro.Theorem               as X
import           Macro.Todo                  as X
import           Macro.Tuple                 as X

import           Macro.Fields.Macro          as X
import           Macro.Groups.Macro          as X
import           Macro.LinearAlgebra.Macro   as X
import           Macro.MachineLearning.Macro as X
import           Macro.Numbers.Macro         as X
import           Macro.Probability.Macro     as X
import           Macro.Sets.Macro            as X
import           Macro.Topology.Macro        as X

-- TODO(kerckhove) Move these to a better place
boxed :: Note -> Note
boxed n = raw "\\text{\\fboxsep=.2em\\fbox{\\m@th$\\displaystyle" <> n <> "$}}"

bla :: Note
bla = boxed leftArrow

bra :: Note
bra = boxed rightArrow

item :: Note -> Note
item n = comm0 "item" <> n

(<=) :: Note -> Note -> Note
(<=) = (<=:)

(>=) :: Note -> Note -> Note
(>=) = (>=:)

(>) :: Note -> Note -> Note
(>) = (>:)

(<) :: Note -> Note -> Note
(<) = (<:)

