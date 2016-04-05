module Cryptography.SystemAlgebra.DiscreteSystems.Terms where

import           Notes

import           Cryptography.SystemAlgebra.AbstractSystems.Terms

makeDefs
    [ "source"
    , "beacon"
    , "synchronous parallel composition"
    , "asynchronous parallel composition"
    , "deterministic environment"
    , "environment"
    , "transcript"
    , "probabillistic system"
    , "probabillistic environment"
    , "probabillistic transcript"
    , "behaviour"
    , "random function"
    , "random permutation"
    , "uniform random function"
    , "URF"
    , "uniform random permutation"
    , "URP"
    , "cumulative description"
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

-- | Y-beacon
yB :: Note -> Note
yB y = m y <> "-" <> beacon
