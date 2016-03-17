module Cryptography.SystemAlgebra where

import           Notes

import           Functions.Basics.Macro
import           Functions.Basics.Terms
import           Functions.BinaryOperation.Terms
import           Logic.FirstOrderLogic.Macro
import           Sets.Basics.Terms

import           Cryptography.SystemAlgebra.Macro
import           Cryptography.SystemAlgebra.Terms

systemAlgebraS :: Note
systemAlgebraS = section "System Algebra" $ do
    abstractSystemAlgebraDefinition
    abstractSystemAlgebraDefinitionNote
    systemAlgebraExamples
    mergingInterfaces

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
    s ["A system", m a, "with", m $ la a =: l, "is called an", m l <> "-" <> system']


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
    ex $ do
        s ["Electronic components that can be connected to an electronic circuit forms a", systemAlgebra <> ", where the", systemMergingOperation, "means to place components on a board together and the", interfaceConnectionOperation, "means to place a wire between the interfaces"]



mergingInterfaces :: Note
mergingInterfaces = de $ do
    s ["Given a", systemAlgebra, "we define a composite operation called", dquoted "interface merging", "as follows"]
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












