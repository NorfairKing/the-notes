module Cryptography.SystemAlgebra.DiscreteSystems.Terms where

import           Notes

import           Cryptography.SystemAlgebra.AbstractSystems.Terms

makeDefs
    [ "source"
    , "beacon"
    , "deterministic discrete system"
    , "synchronous parallel composition"
    , "asynchronous parallel composition"
    , "deterministic environment"
    , "deterministic converter"
    , "probabilistic converter"
    , "environment"
    , "transcript"
    , "probabilistic system"
    , "probabilistic environment"
    , "probabilistic transcript"
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

-- | N-probabilistic system
nPS :: Note -> Note
nPS n = m n <> "-" <> probabilisticSystem

-- | N-probabilistic systems
nPSs :: Note -> Note
nPSs n = m n <> "-" <> probabilisticSystems

-- | N-deterministic system
nDS :: Note -> Note
nDS n = m n <> "-" <> deterministicSystem

-- | N-deterministic systems
nDSs :: Note -> Note
nDSs n = m n <> "-" <> deterministicSystems

-- | X,Y-system
xyS :: Note -> Note -> Note
xyS x y = nS $ tuple x y

-- | X,Y-systems
xySs :: Note -> Note -> Note
xySs x y = nSs $ tuple x y

-- | Y-source
yS :: Note -> Note
yS y = m y <> "-" <> source

-- | Y,X-environment
yxE :: Note -> Note -> Note
yxE y x = m (tuple y x) <> "-" <> environment

-- | Deterministic environment for X,Y-system
yxDE :: Note -> Note -> Note
yxDE y x = m (tuple y x) <> "-" <> deterministicEnvironment

yxDEs :: Note -> Note -> Note
yxDEs y x = m (tuple y x) <> "-" <> deterministicEnvironments

-- | Probabillistic environment for X,Y-system
yxPE :: Note -> Note -> Note
yxPE y x = m (tuple y x) <> "-" <> probabilisticEnvironment

yxPEs :: Note -> Note -> Note
yxPEs y x = m (tuple y x) <> "-" <> probabilisticEnvironments

xyDS :: Note -> Note -> Note
xyDS x y = m (tuple x y) <> "-" <> deterministicSystem

xyDSs :: Note -> Note -> Note
xyDSs x y = m (tuple x y) <> "-" <> deterministicSystems

xyPS :: Note -> Note -> Note
xyPS x y = m (tuple x y) <> "-" <> probabilisticSystem

xyPSs :: Note -> Note -> Note
xyPSs x y = m (tuple x y) <> "-" <> probabilisticSystems

-- | ((U,V), (X, Y)) converter
uvxyC :: Note -> Note -> Note -> Note -> Note
uvxyC u v x y = m (tuple (tuple u v) (tuple x y)) <> "-" <> converter

uvxyC' :: Note -> Note -> Note -> Note -> Note
uvxyC' u v x y = m (tuple (tuple u v) (tuple x y)) <> "-" <> converter'

-- | Y-beacon
yB :: Note -> Note
yB y = m y <> "-" <> beacon
