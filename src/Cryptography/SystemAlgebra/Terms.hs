module Cryptography.SystemAlgebra.Terms where

import           Notes

makeDefs
    [ "abstract system algebra"
    , "system algebra"
    , "system"
    , "label"
    , "interface label set"
    , "interface"
    , "system merging operation"
    , "interface connection operation"
    , "interface merging"
    , "composition"
    , "parallel composition"
    , "deterministic system"
    , "resource system"
    , "resource"
    , "converter system"
    , "converter"
    , "source"
    , "beacon"
    , "uniform random function"
    , "URF"
    , "synchronous parallel composition"
    , "asynchronous parallel composition"
    , "deterministic environment"
    , "environment"
    , "transcript"
    , "probabillistic system"
    , "probabillistic environment"
    ]

-- | N-system
nS :: Note -> Note
nS n = m n <> "-" <> system

-- | N-systems
nSs :: Note -> Note
nSs n = m n <> "-" <> systems

-- | X,Y-system
xyS :: Note -> Note -> Note
xyS x y = nS $ tuple x y

-- | X,Y-systems
xySs :: Note -> Note -> Note
xySs x y = nSs $ tuple x y

-- | Y-source
yS :: Note -> Note
yS y = m y <> "-" <> source


-- | Deterministic environment for X,Y-system
yxDE :: Note -> Note -> Note
yxDE y x = m (tuple y x) <> "-" <> deterministicEnvironment

yxDEs :: Note -> Note -> Note
yxDEs y x = m (tuple y x) <> "-" <> deterministicEnvironments

-- | Probabillistic environment for X,Y-system
yxPE :: Note -> Note -> Note
yxPE y x = m (tuple y x) <> "-" <> probabillisticEnvironment

yxPEs :: Note -> Note -> Note
yxPEs y x = m (tuple y x) <> "-" <> probabillisticEnvironments

xyDS :: Note -> Note -> Note
xyDS x y = m (tuple x y) <> "-" <> deterministicSystem

xyDSs :: Note -> Note -> Note
xyDSs x y = m (tuple x y) <> "-" <> deterministicSystems

xyPS :: Note -> Note -> Note
xyPS x y = m (tuple x y) <> "-" <> probabillisticSystem

xyPSs :: Note -> Note -> Note
xyPSs x y = m (tuple x y) <> "-" <> probabillisticSystems
