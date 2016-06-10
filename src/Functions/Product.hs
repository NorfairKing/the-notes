module Functions.Product (productFunctionS) where

import           Notes

import           Functions.Application.Macro
import           Functions.Basics.Macro
import           Functions.Basics.Terms

import           Functions.Product.Macro
import           Functions.Product.Terms

productFunctionS :: Note
productFunctionS = section "Product functions" $ do
    directProductFunctionDefinition
    focussedProductFunctionDefinition

directProductFunctionDefinition :: Note
directProductFunctionDefinition = de $ do
    lab directProductDefinitionLabel
    lab directProductFunctionDefinitionLabel
    let i = "i"
        a = ("A" !:)
        ai = a i
        b = ("B" !:)
        bi = b i
        f_ = ("f" !:)
        f i = fn (f_ i)
        fi_ = f_ i
        fl = list (f_ 1) (f_ 2) (f_ i)
    s ["Let", m fl, "be a list of", functions, m $ fun fi_ ai bi]
    let pf = dprodfunlist (f_ 1) (f_ 2) (f_ i)
    s [the, directProduct', or, directProductFunction, m pf, "of the", functions, m fl, "is defined as the following", function]
    let as = tuplelist (a 1) (a 2) (a i)
        bs = tuplelist (b 1) (b 2) (b i)
        aa = ("a" !:)
        aas = tuplelist (aa 1) (aa 2) (aa i)
        bbs = tuplelist (f 1 $ aa 1) (f 2 $ aa 2) (f i $ aa i)
    ma $ func pf as bs aas bbs

focussedProductFunctionDefinition :: Note
focussedProductFunctionDefinition = de $ do
    lab focussedProductDefinitionLabel
    lab focussedProductFunctionDefinitionLabel
    let i = "i"
        a = "A"
        b = ("B" !:)
        bi = b i
        f_ = ("f" !:)
        f i = fn (f_ i)
        fi_ = f_ i
        fl = list (f_ 1) (f_ 2) (f_ i)
    s ["Let", m fl, "be a list of", functions, m $ fun fi_ a bi]
    let pf = fprodfunlist (f_ 1) (f_ 2) (f_ i)
    s [the, focussedProduct', or, focussedProductFunction, m pf, "of the", functions, m fl, "is defined as the following", function]
    let bs = tuplelist (b 1) (b 2) (b i)
        aa = "a"
        bbs = tuplelist (f 1 aa) (f 2 aa) (f i aa)
    ma $ func pf a bs aa bbs









