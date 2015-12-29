module Logic.FirstOrderLogic where

import           Notes

import qualified Prelude                        as P (map)

import           Functions.Application.Macro
import           Logic.AbstractLogic.Macro
import           Logic.AbstractLogic.Terms
import           Logic.PropositionalLogic.Macro
import           Logic.PropositionalLogic.Terms
import           Sets.Basics.Terms

import           Logic.FirstOrderLogic.Macro
import           Logic.FirstOrderLogic.Terms


firstOrderLogicS :: Note
firstOrderLogicS = note "first-order-logic" $ do
    section "First Order Logic"
    firstOrderLogicDefinition
    termDefinition
    atomicSentence
    quantifiers
    modelFOL
    situationalCalculusSS
    inferenceInFOL


firstOrderLogicDefinition :: Note
firstOrderLogicDefinition = de $ do
    lab firstOrderLogicDefinitionLabel
    s ["While propositional logic is about simple facts, first order logic is about complex facts involving objects, relations, functions, etc..."]
    s [firstOrderLogic', " is a ", theory]
    s ["It is an extension of propositional logic with predicates, functions, variables and their quantifiers"]
    s ["Remember that these symbols are just that, symbols"]


termDefinition :: Note
termDefinition = do
    de $ s ["A ", term "term", " in first order logic is either a constant symbol, a variable or a ", m "k", "-ary function symbol applied to terms"]

    ex $ s [cs $ P.map (dquoted . m) [1, 2, 3, x, f x], " are terms in first order logic"]
  where
    x = "x"
    f = fn "f"

atomicSentence :: Note
atomicSentence = do
    de $ do
        lab atomicDefinitionLabel
        s ["A sentence in first order logic is called ", atomic', " if it is a constant symbol or a function of only constant symbols"]

    ex $ s [cs $ P.map (dquoted . m) [1, small 1, smaller 1 2], " are atomic sentences in ", firstOrderLogic]
  where
    small = fn "Small"
    smaller = fn2 "Smaller"


quantifiers :: Note
quantifiers = note "quantifiers" $ do
    subsection "Quantifiers"
    s ["Quantifiers bind free variables"]
    existentialQuantifierDefinition
    universalQuantifierDefinition
    note "composite-sentence" $ do
        compositeSentence
        compositeSentenceExamples

    propertiesOfQuantifiers

x, y, p :: Note
x = "x"
y = "y"
p = "P"

pp :: Note -> Note
pp = fn p

ppp :: Note -> Note -> Note
ppp x y = fn p $ cs [x, y]

existentialQuantifierDefinition :: Note
existentialQuantifierDefinition = de $ do
    s ["The ", existentialQuantifier', " ", m existentialQuantifier, " "]
    s ["A sentence ", m (te x $ pp x), ", in the context of a model ", m "m", " is defined to hold true if there exists a ", m x, " in ", m "m", " such that the predicate ", m p, " holds for ", m x]

universalQuantifierDefinition :: Note
universalQuantifierDefinition = de $ do
    s ["The ", universalQuantifier', " ", m universalQuantifier, " "]
    s ["A sentence ", m (fa x $ pp x), ", in the context of a model ", m "m", " is defined to hold true if the predicate ", m p, " holds for every instantiation of ", m x, " in ", m "m"]

compositeSentence :: Note
compositeSentence = do
    de $ s ["A sentence in first order logic is called ", composite', " if it atomic, contains free variables an quantifiers, or is composed of composite sentences joined by connectives"]
    ex $ s [cs $ P.map (dquoted . m) [1, greater 2 1, great x, fa y (great x ∨ greater x y)], " are composite sentences in first order logic"]
  where
    x = "x"
    great = fn "Great"
    greater = fn2 "Greater"

compositeSentenceExamples :: Note
compositeSentenceExamples = do
    ex $ do
        let (mom, mmoc) = ("ManOnMoon", "MoonMadeOfCheese")
        s ["The following is the transation to ", firstOrderLogic, " of the ", composite, " sentence ", dquoted $ s ["If there is a man on the moon, then the moon is maedo of cheese"]]
        ma $ mom ⇒ mmoc
    ex $ do
        let (x, par, joan, fem) = ("x", fn2 "Parent", "Joan", fn "Female")
        s ["The following is the transation to ", firstOrderLogic, " of the ", composite, " sentence ", dquoted $ s ["Joan has a daughter"]]
        ma $ te x $ par joan x ∧ fem x




propertiesOfQuantifiers :: Note
propertiesOfQuantifiers = note "properties" $ do
    subsubsection "Properties of quantifiers"
    switchExistentials
    switchUniversals
    switchMixed
    dualityOfQuantifiers

switchExistentials :: Note
switchExistentials = thm $ do
    s ["The order of multiple contiguous existential quantifiers does not matter"]
    ma $ (pars $ te x $ te y $ ppp x y) ⇔ (pars $ te y $ te x $ ppp x y)

    toprove

switchUniversals :: Note
switchUniversals = thm $ do
    s ["The order of multiple contiguous universal quantifiers does not matter"]
    ma $ (pars $ fa x $ fa y $ ppp x y) ⇔ (pars $ fa y $ fa x $ ppp x y)

    toprove

switchMixed :: Note
switchMixed = cex $ do
    s ["The order of different quantifiers ", textbf "does", " matter"]
    ma $ not . pars $ (pars $ te x $ fa y $ ppp x y) ⇔ (pars $ fa y $ te x $ ppp x y)

    toprove

dualityOfQuantifiers :: Note
dualityOfQuantifiers = thm $ do
    s ["Each quantifier can be expressed in terms of the other"]
    ma $ (pars $ fa x $ pp x) ⇔ (pars $ not $ te x $ not $ pp x)

    toprove

modelFOL :: Note
modelFOL = de $ do
    s ["A ", model, " in first order logic consists of instantiations of objects, relations and functions and their interpretations in terms of their symbols"]
    s ["Often any constants not in the model is asserted to be false"]


situationalCalculusSS :: Note
situationalCalculusSS = do
    subsection "Situational Calculus"
    s ["The use of ", situationalCalculus', " is to model situations"]
    s ["In situational calculus, facts hold at a certain moment and/or in a certain situation"]
    s ["This is modeled by adding a situational argument to every non-eternal ", predicate]

    s ["Situational calculus can be used to model change, non-change, actions, perceptions, etc..."]

    frameProblem
    planning

frameProblem :: Note
frameProblem = do
    subsubsection "The frame problem"
    s ["Now that we can model situations using frames, there is a need for so called ", effectAxiom', "s that model changes due to actions"]
    s ["In addition to modeling change, one must also model non-change"]
    s ["The frame problem is that the number of frame axioms can be become large and even infinite"]
    s ["This poses problems in automated inference"]
    s ["To solve the problem, we will use so called ", successorStateAxiom', "s that model how each non-eternal predicate is affected or not affected by actions"]
    s ["These successor state axioms model the fact that a predicate is true if and only if an action made it true or it was already true and no action made it false"]

planning :: Note
planning = do
    subsubsection "Planning using first order logic"
    s ["First order logic can be used to plan actions based on a knowledge base of known facts"]
    s ["The idea is to decide what the goal situation is and to model it"]
    s ["Then, automated inference can be used to find out whether the given knowledge base entails the goal situation"]


inferenceInFOL :: Note
inferenceInFOL = do
    subsection "Inference in first order logic"

    s ["Inference in first order logic is more complicated than inference in ", propositionalLogic]
    s ["In general, there are two approaches: Propositionalisation and ", dquoted "lifted", " inference"]

    propositionalisationSS
    liftedInferenceSS

propositionalisationSS :: Note
propositionalisationSS = note "propositionalisation" $ do
    subsubsection "propositionalisation"
    de $ do
        s [propositionalisation', " is an ", inference, " in first order logic"]
        s ["It consists of replacing all quantified variables with so called ", groundingVariable', "s using each possible term"]
        s ["This turns the problem into a propositional logic problem and it can then be solved as discussed before"]
    s ["The problem with proportionalisation is that the solver may need to create a lot of unnecessary symbols"]
    s ["Even worse, the amount of created symbols could be infinite"]

    herbrandTheorem

    s ["Given this theorem, we can propose a naive algorithm to test whether a given sentence ", m lsen, " is entailed by a given first order logic knowledge base"]
    s ["The algorithm consists of enumerating all finite subsets of the propositionalised knowledge base ", m (lkb ∪ not lsen), " and checking whether they are satisfiable one by one using propositional resolution"]
    s ["Note that this algorithm will stop if the given sentence is entailed by the given knowledge base but will never stop otherwise"]
    s ["This is intrinsic to the problem"]
    s ["First order logic is only semi-decidable"]

herbrandReference :: Reference
herbrandReference = Reference article "herbrand-theorem" $
    [
      ("author" , "Jacques Herbrand")
    , ("title"  , "Recherches sur la theorie de la demonstration.")
    , ("year"   , "1930")
    , ("journal", "Travaux de la Societe des Sciences et des Lettres de Varsovie")
    , ("volume" , "3")
    , ("number" , "33")
    ]

herbrandTheorem :: Note
herbrandTheorem = thm $ do
    s [herbrandsTheorem']
    newline
    s ["If a sentence in entailed by a first order logic knowledge base, then there exists a proof using only a finite subset of the propositionalized knowledge base"]
    cite herbrandReference

liftedInferenceSS :: Note
liftedInferenceSS = note "lifted-inferences" $ do
    subsubsection "Lifted inference"
    s [the, liftedInference', "s are a ", set, " of ", inference, "s in first order logic"]
    s ["It consists of trying to infer sentences ", emph "without", " instantiating variables at all using propositional inference by lifting its inferences"]

    de $ do
        s [the, generalizedModusPonens', " is an ", inference, " in first order logic"]
        s ["Let ", m (cs [pp 1, dotsc, pp n]), and, m (cs [p 1, dotsc, p n]), " be sentences in first order logic"]
        s ["Let ", m t, " be a substitution and ", m (subst t q), " its application to ", m q]
        s ["Suppose ", m (subst t (pp i) =: subst t (p i)), " holds"]
        ma $ linf [cs [pp 1, dotsc, pp n], ((p 1) ∧ dotsb ∧ (p n)) ⇒ q] $ subst t q
    thm $ do
        s ["The generalized modus ponens is not ", complete]
        noproof

    s ["There also exists a lifted variant of resolution"]
    todo "Describe this variant"
    s ["It is ", sound, " and refutation-complete but not ", complete]
    todo "define refutation-complete"

  where
    subst_ = "Subst"
    subst = fn2 subst_
    n = "n"
    t = theta
    i = "i"
    q = "q"
    p n = "p" !: n
    pp n = "p'" !: n
