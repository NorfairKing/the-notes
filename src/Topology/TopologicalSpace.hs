module Topology.TopologicalSpace where

import           Notes

import           Sets.Algebra.Intersection.Terms
import           Sets.Basics.Terms

import           Topology.TopologicalSpace.Terms


topologicalSpaceS :: Note
topologicalSpaceS = section "Topological Space" $ do
    topologyDefinition
    topologicalSpaceDefinition
    closedSetDefinition
    trivialTopologyDefinition
    discreteTopologyDefinition
    topologyExamples
    inducedTopology
    comparableDefinition
    finerCoarserDefinition

topologyDefinition :: Note
topologyDefinition = de $ do
    s ["Let ", m topset, " be a ", set]
    s ["A ",  topology', " ", m toptop, " on ", m topset, " is a collection of ", subsets, " of ", m topset, "with the following properties"]
    enumerate $ do
        item $ m $ emptyset ∈ toptop
        item $ m $ topset ∈ toptop
        item $ do
            s ["Let ", m "A", " be a subset of ", m toptop]
            ma $ setuncmp ("a" ∈ "A") "a" ∈ toptop
            s ["The union of any collection of open sets is an open set"]
        item $ do
            s ["Let ", m "B", " be a finite subset of ", m toptop]
            ma $ setincmp ("b" ∈ "B") "b" ∈ toptop
            s ["The intersection of any finite collection of open sets in an open set"]
    s ["These sets are called the ", term "open", " sets of ", m topset]

topologicalSpaceDefinition :: Note
topologicalSpaceDefinition = do
    de $ do
        s ["Let ", m topset, " be a ", set, and, m toptop, " a ", topology, on, m topset]
        s [m topsp, " is called a ", topologicalSpace]
    nte $ do
        s ["In a sence, the sets in ", m toptop, " describe very abstractly which sets in ", m topset, " are ", quoted "close", " to eachother without describing ", emph "how", " close they are"]

closedSetDefinition :: Note
closedSetDefinition = de $ do
    topspDec
    s ["A subset ", m "x", " of ", m topset, " is called ", term "closed", " if ", m (topset \\ "x"), " is open"]

trivialTopologyDefinition :: Note
trivialTopologyDefinition = de $ do
    s ["The ", term "trivial topology", " on a set ", m topset, " is the set ", m (setofs [emptyset, topset])]
    s ["This topology is also called the ", term "indiscrete topology"]

discreteTopologyDefinition :: Note
discreteTopologyDefinition = de $ do
    s ["The ", term "discrete topology", " on a set ", m topset, " is the powerset ", m (powset topset), " of ", m topset]

topologyExamples :: Note
topologyExamples = do
    ex $ do
      s ["The set ", m (setofs [emptyset, setof a, setof b]), " is not a topology on the set ", m (setofs [a, b]), " because it does not contain the union of the sets ", m (setof a), and, m (setof b)]
    ex $ do
      s ["On the set ", m (setofs [a, b]), " the following sets are all the possible topologies"]
      itemize $ do
        item $ m $ setofs [emptyset, setofs [a, b]]
        item $ m $ setofs [emptyset, setof a, setofs [a, b]]
        item $ m $ setofs [emptyset, setof b, setofs [a, b]]
        item $ m $ setofs [emptyset, setof a, setof b, setofs [a, b]]
  where
    a = "a"
    b = "b"

topspDec :: Note
topspDec = s ["Let ", m topsp, " be a topological space"]

inducedTopology :: Note
inducedTopology = do
    de $ do
      topspDec
      s ["Let ", m y, " be a subset of ", m topset]
      s ["The set ", m ty, " is a topology on ", m y]
      ma $ ty =: setcmpr ("O" ∩ y) ("O" ∈ toptop)
      s [m ty, " is called the ", term "induced topology", on, m y, by, m toptop]

    proof $ do
      noindent
      itemize $ do
        item $ s ["The set ", m (emptyset ∩ y =: emptyset), " is in ", m ty]
        item $ s ["The set ", m (topset ∩ y =: y), " is in ", m ty]
        item $ do
          s ["Let ", m "A", " be a subset of ", m ty]
          s ["Per construction, this means that there exists a subset ", m "B", " as follows "]
          ma $ setuncmp ("a" ∈ "A") "a" =: setuncmp ("b" ∈ "B") ("a" ∩ y)
          s ["Because of the distributivity of the union,", ref distributionLaw2TheoremLabel, " this is equal to the following set"]
          ma $ (pars $ setuncmp ("b" ∈ "B") "a") ∩ y
          s ["Per construction of ", m ty, " this means that ", m (setuncmp ("a" ∈ "A") "a"), " is in ", m ty]
        item $ do
          s ["Let ", m "B", " be a finite subset of ", m ty]
          s ["Per construction, this means that there exists a subset ", m "B", " as follows "]
          ma $ setincmp ("a" ∈ "A") "a" =: setincmp ("a" ∈ "A") ("a" ∩ y)
          s ["Because of the associativity of the intersection,", ref intersectionAssociativityPropertyLabel, " this is equal to the following set"]
          ma $ (pars $ setincmp ("a" ∈ "A") "a") ∩ y
          s ["Per construction of ", m ty, " this means that ", m (setincmp ("a" ∈ "A") "a"), " is in ", m ty]
  where
    ty = toptop !: y
    y = "Y"


comparableDefinition :: Note
comparableDefinition = de $ do
    s ["Two topologies ", m (toptop !: 1), and, m (toptop !: 2), " on a set ", m topset, " are called ", term "comparable", " if either is a subset of the other"]

finerCoarserDefinition :: Note
finerCoarserDefinition = de $ do
    s ["Let ", m (toptop !: 1), and, m (toptop !: 2), " be two comparable topologies on a set ", m topset, " where ", m (toptop !: 1 ⊆ toptop !: 2), " holds"]
    s [m (toptop !: 1), " is called ", term "finer", " than ", m (toptop !: 2), and, m (toptop !: 2), " is called ", term "coarser", " than ", m (toptop !: 1)]
    s ["If ", m (toptop !: 1), " is a proper subset of ", m (toptop !: 2), " then we would call them ", term "strictly finer", and, term "strictly coarser", " respectively"]

