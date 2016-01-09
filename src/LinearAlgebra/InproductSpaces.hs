module LinearAlgebra.InproductSpaces where

import           Notes

import           Functions.Basics.Macro
import           Logic.FirstOrderLogic.Macro
import           Logic.PropositionalLogic.Macro

import           LinearAlgebra.InproductSpaces.Terms

inproductSpaces :: Note
inproductSpaces = section "Inproduct Spaces" $ do
    semiInnerProductDefinition
    innerProductDefinition
    innerProductExamples
    inproductSpaceDefinition
    inproductSpaceExamples

l, u, v, w :: Note
l = lambda
u = "u"
v = "v"
w = "w"

semiInnerProductDefinition :: Note
semiInnerProductDefinition = de $ do
    s ["Let ", m (lavs_ complexes laset laadd lamul), " be a vector space and let ", m (fun lainprod (laset ⨯ laset) complexes), " be a binary operator"]
    s [m lainprod, " is called a ", term "semi-inner product", " if it has the following properties"]
    enumerate $ do
        item $ do
          term "conjugate symmetry"
          ma $ fa (cs [v, w] ∈ laset) $ v <.> w =: conj (w <.> v)

        item $ do
          term "linearity in the first argument"
          ma $ fa (cs [cs [u, v, w] ∈ laset, l ∈ complexes]) $ l <*> v <+> u <.> w =: l * (v <.> w) + u

innerProductDefinition :: Note
innerProductDefinition = de $ do
    s ["Let ", m (lavs_ complexes laset laadd lamul), " be a vector space and let ", m (fun lainprod (laset ⨯ laset) complexes), " be a semi-inproduct"]
    s [m lainprod, " is said to be an ", term "inner product", " if it is also has the ", term "positive-difiniteness", " property"]
    ma $ fa (v ∈ laset) $ (v <.> v >= 0) ∧ (pars $ v <.> v =: 0 ⇔ v =: 0)
  where v = "v"

innerProductExamples :: Note
innerProductExamples = do
    ex $ do
      s ["The following binary operation is an inproduct in ", m (realVectorsSpace p)]
      ma $ func2 realVectorInproduct rp rp reals u v $ sumcmp i $ (u !: i) * (v !: i)
      toprove
      s ["It is called the ", term "vector dotproduct"]

  where
    rp = reals ^: p
    p = "p"
    i = "i"


inproductSpaceDefinition :: Note
inproductSpaceDefinition = de $ do
    lab inproductSpaceDefinitionLabel
    s ["Let ", m lavs, " be a vector space and ", m lainprod, " an inner product on it"]
    s [m laips, " is called an ", term "inner product", " space"]

inproductSpaceExamples :: Note
inproductSpaceExamples = do
    ex $ do
        s ["The field ", m (realVectorsSpace p), ", equipped with the vector dotproduct, is an inner product space"]
        ma $ euclideanInnerProductSpace p
        s ["This is called the ", term "Euclidean inner product space", " of dimension ", m p]
        toprove_ "This is, in fact, an inproduct space"

  where
    p = "p"
