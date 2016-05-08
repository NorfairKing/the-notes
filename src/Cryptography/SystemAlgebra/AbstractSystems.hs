module Cryptography.SystemAlgebra.AbstractSystems where

import           Notes                                            hiding
                                                                   (cyclic)

import           Functions.Basics.Macro
import           Functions.Basics.Terms
import           Functions.BinaryOperation.Terms
import           Logic.FirstOrderLogic.Macro
import           Sets.Basics.Terms

import           Cryptography.SystemAlgebra.AbstractSystems.Macro
import           Cryptography.SystemAlgebra.AbstractSystems.Terms
import           Cryptography.SystemAlgebra.Graph

abstractSystemsSS :: Note
abstractSystemsSS = subsection "Abstract systems" $ do
    abstractSystemAlgebraDefinition
    abstractSystemAlgebraDefinitionNote
    systemAlgebraExamples

    subsubsection "Merging interfaces" $ do
        mergingInterfaces
        mergingInterfacesExamples

    subsubsection "2-systems" $ do
        twoSystemCompositionDefinition
        compositionOfTwoSystemsIsATwoSystem
        twoSystemCompositionAssociative

    subsubsection "Parallel composition" $ do
        parallelCompositionDefinition
        parallelCompositionExamples
        parallelCompositionOfTwoSystemsIsTwoSystem

    subsubsection "Resources and converters" $ do
        resourceDefinition
        converterDefinition
        converterExamples

abstractSystemAlgebraDefinition :: Note
abstractSystemAlgebraDefinition = de $ do
    lab abstractSystemAlgebraDefinitionLabel
    lab systemAlgebraDefinitionLabel
    lab systemDefinitionLabel
    lab labelDefinitionLabel
    lab interfaceLabelSetDefinitionLabel
    lab interfaceDefinitionLabel
    lab systemMergingOperationDefinitionLabel
    lab interfaceConnectionOperationDefinitionLabel
    s ["An", abstractSystemAlgebra', "consists of a", set, m syss_, "of", systems' <> ", a", set, m labs_, "of", labels' <> ", a", total, function, m $ fun laf_ syss_ (powset labs_), "that assigns the associated", interfaceLabelSet', "to each", system, "and two operations as follows"]
    itemize $ do
        item $ do
            s ["A", associative <> ",", commutative, systemMergingOperation', m $ fun2 smo_ syss_ syss_ syss_, "such that.."]
            let a = "A"
                b = "B"
            itemize $ do
                item $ s [m $ a `sm` b, "is only defined if", m $ la a ∩ la b, "is empty"]
                item $ m $ fa (a ∈ syss_) $ fa (b ∈ syss_) $ la (a `sm` b) =: la a ∪ la b
                item $ do
                    s ["Let", m emptysys, "be the", system, "such that", m $ la emptysys =: emptyset, "(if it exists)"]
                    ma $ fa (a ∈ syss_) $ a `sm` emptysys =: a =: emptysys `sm` a
                    todo "prove that this system is in fact unique"
        item $ do
            s ["An", associative, interfaceConnectionOperation', m $ fun3 (ico cdot_ cdot_ cdot_) syss_ labs_ labs_ syss_]
            let a = "A"
                l = "l"
                l1 = l !: 1
                l2 = l !: 2
            s ["Let", m a, "be a", system, "and let", m l1, and, m l2, "be two distinct", labels, "in", m $ la a]
            s [m $ ico a l1 l2, "is the", system, "that is identical to", m a, "except now the interfaces", m l1, and, m l2, "are connected"]
            ma $ la (ico a l1 l2) =: la a \\ setofs [l1, l2]
    s ["The above operations also have to be order invariant"]
    let a = "A"
        b = "B"
        l = "l"
        l1 = l !: 1
        l2 = l !: 2
    ma $ fa (cs [a, b] ∈ syss_) $ fa (cs [l1, l2] ∈ labs_) $ ico a l1 l2 `sm` b =: ico (pars $ a `sm` b) l1 l2

    let l = "L"
    s ["A system", m a, "with", m $ la a =: l, "is called an", m l <> "-" <> system', "or also a", m (setsize l) <> "-" <> system', "if the names of the labels aren't considered"]


abstractSystemAlgebraDefinitionNote :: Note
abstractSystemAlgebraDefinitionNote = nte $ do
    s ["We will generally only consider", abstractSystemAlgebras, "in which the", interfaceConnectionOperation, "is symmetric as follows"]
    let a = "A"
        l = "l"
        l1 = l !: 1
        l2 = l !: 2
    ma $ fa (a ∈ syss_) $ fa (cs [l1, l2] ∈ labs_) $ ico a l1 l2 =: ico a l2 l1



systemAlgebraExamples :: Note
systemAlgebraExamples = do
    let (a, b, c, d) = ("a", "b", "c", "d")
    ex $ do
        let sys = System "S" [a, b]
        systemFig 3 sys $ s ["An abstract", system, m "S", "with two interfaces:", m "a", and, m "b"]
    ex $ do
        let s1 = System "A" [a, b]
            s2 = System "B" [c, d]
            sys = Merge s1 s2
        systemFig 5 sys $ s ["The merger of two abstract", systems]

    ex $ do
        let s1 = System "S" [a, b, c]
            s2 = Connected a b s1
        systemsFig 3 [s1, s2] $ s ["The connection of the interfaces", m "a", and, m "b", "in the abstract", system, m "S"]

    ex $ do
        s ["Electronic components that can be connected to an electronic circuit forms a", systemAlgebra <> ", where the", systemMergingOperation, "means to place components on a board together and the", interfaceConnectionOperation, "means to place a wire between the interfaces"]



mergingInterfaces :: Note
mergingInterfaces = de $ do
    lab interfaceMergingDefinitionLabel
    s ["Given a", systemAlgebra, "we define a composite operation called", interfaceMerging', "as follows"]
    let a = "A"
        l = "L"
        j = "j"
    s ["Denote the interface merging operation on a", system, m a, "of an", interface, set, "with", labels, m l, "into an", interface, "with label", m j, "as" , m $ mio a l j]
    s ["The inverse operation is denoted as", m $ mioi a j l]
    s ["These operations have the following properties"]
    itemize $ do
        item $ m $ fa (a ∈ syss_) $ fa (l ⊆ la a) $ fa (j ∈ labs_ \\ la a) $ la (mio a l j) =: (pars $ la a \\ l) ∪ (setof j)
        item $ m $ fa (a ∈ syss_) $ fa (l ⊆ la a) $ fa (j ∈ labs_ \\ la a) $ la (mioi a j l) =: (pars $ la a \\ setof j) ∪ l
        item $ m $ mioi (pars $ mio a l j) j l =: a

mergingInterfacesExamples :: Note
mergingInterfacesExamples = do
    ex $ do
        let (a, b, c, d, e, l) = ("a", "b", "c", "d", "e", "l")
        let sys = System "A" [a, b, c, d, e]
        systemsFig 5 [sys, MergeLabels [a, b, c] l sys] $ do
            s ["The system on the right represents the merger of the interfaces", m "a" <> ", " <> m "b", and, m "c", "into", m "l", "from the system on the left"]

twoSystemCompositionDefinition :: Note
twoSystemCompositionDefinition = de $ do
    let s1 = "S" !: 1
        s2 = "S" !: 2
        l = "l"
        l1 = l !: 1
        l2 = l !: 2
    s [the, "(serial)", composition', "of two", m 2 <> "-" <> systems, "(with disjoint", interfaceLabelSets <> ")", "on two", labels, m l1, and, m l2, "where", m l1, "is in the", interfaceLabelSet, "of", m s1, and, m l2, "is in the", interfaceLabelSet, "of", m s2, "is defined as the merger of", m s1, and, m s2, "followed by the connection of", m l1, and, m l2, "in the result"]

compositionOfTwoSystemsIsATwoSystem :: Note
compositionOfTwoSystemsIsATwoSystem = do
    thm $ do
        s [the, composition, "of two", m 2 <> "-" <> systems, "is again a", m 2 <> "-" <> system]
        noproof
    ex $ do
        let (a, b, c, d) = ("a", "b", "c", "d")
        let s1 = System "A" [a, b]
            s2 = System "B" [c, d]
            sys = compose b c s1 s2
        systemFig 3 sys $ s ["The composition of two", m 2 <> "-" <> systems]

twoSystemCompositionAssociative :: Note
twoSystemCompositionAssociative = thm $ do
    s [the, composition, "of", m 2 <> "-" <> systems, "is", associative]
    toprove

parallelCompositionDefinition :: Note
parallelCompositionDefinition = de $ do
    lab parallelCompositionDefinitionLabel
    let s_ = "s"
        s1 = s_ !: 1
        s2 = s_ !: 2
        k = "k"
        sk = s_ !: k
        sl = list s1 s2 sk
    s ["Let", m sl, "be", systems, "in a", systemAlgebra, "with the same", interfaceLabelSet]
    let sn = sqbrac sl
    s ["Let", m sn, "be the", system <> ", obtained by relabeling the", interfaces, "of the", systems, m sl, "to be disjoint, then merging the", systems, "and then merging all parralel", interfaces, "into one interface with the same name"]
    s [m sn, "is called the", parallelComposition', "of", m sl]


parallelCompositionExamples :: Note
parallelCompositionExamples = do
    ex $ do
        let (a, b, c) = ("a", "b", "c")
        let s1 = System "A" [a, b, c]
            s2 = System "B" [a, b, c]
            sys = ParComp [s1, s2]
        systemFig 5 sys $ s ["The parallel composition of two abstract", systems]


parallelCompositionOfTwoSystemsIsTwoSystem :: Note
parallelCompositionOfTwoSystemsIsTwoSystem = do
    thm $ do
        s [the, parallelComposition, "of", m 2 <> "-" <> systems, "is a", m 2 <> "-" <> system]
        noproof
    ex $ do
        let (a, b) = ("a", "b")
        let s1 = System "A" [a, b]
            s2 = System "B" [a, b]
            s3 = System "C" [a, b]
            sys = ParComp [s1, s2, s3]
        systemFig 6 sys $ s ["The parallel composition of three 2-", systems]



resourceDefinition :: Note
resourceDefinition = de $ do
    lab resourceSystemDefinitionLabel
    lab resourceDefinitionLabel
    let i = mathcal "I"
    s ["An", m i <> "-" <> resourceSystem', "or simply", m i <> "-" <> resource, "is a", system, "with", interfaceLabelSet, m i]

converterDefinition :: Note
converterDefinition = de $ do
    lab converterSystemDefinitionLabel
    lab converterDefinitionLabel
    s ["A", converterSystem', "or simply", converter', "is a", system, "with two", interfaces <> ", an inside and an outside interface"]
    let a = alpha
        r = "R"
        i = mathcal "I"
    s [the, "inside", interface, "of a", converterSystem, m a, "can be connected to an", interface, "of an", m i <> "-" <> resourceSystem, m r <> ", resulting in a new", resourceSystem, "of the same type as", m r, "where the outside interface of", m a, "serves as the new interface of the combined system"]
    s ["If", m r, "is a", m 1 <> "-" <> system, "then the resulting", m 1 <> "-" <> system, "is denoted as", m $ conv_ a r]
    let i_ = "i"
    s ["Otherwise, if", m a, "is connected to interface", m $ i_ ∈ i, "of", m r, "the resulting", system, "is denoted as", m $ conv a i_ r]

converterExamples :: Note
converterExamples = do
    ex $ do
        let (a, b, c, d, e) = ("a", "b", "c", "in", "out")
        let r = System "R" [a, b, c]
            co = System "c" [d, e]
            sys = compose c d r co
        systemFig 6 sys $ s ["The conversion of a", resourceSystem, m "R", "with a converter", m "c"]

conversionOrderDoesNotMatter :: Note
conversionOrderDoesNotMatter = thm $ do
    s ["When two", converters, "are connected to distinct", interfaces, "of a", resource, "their order of conversion does not matter"]
    let a = alpha
        i = "i"
        b = beta
        j = "j"
        r = "R"
    ma $ conv a i (conv b j r) =: conv b j (conv a i r)
    noproof

