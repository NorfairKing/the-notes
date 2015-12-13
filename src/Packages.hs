module Packages (
      packages
    , packageDep
    , packageDep_
    , injectPackageDependencies
    ) where

import           Types

import qualified Data.Set            as S
import           Prelude             (map)

import           Control.Monad.State (modify)


packages :: Note
packages = do
  -- For memoir class
  -- usepackage [] "memoir"
  -- For frames
  usepackage [] "mdframed"

  -- For maths
  usepackage [] "amsmath"
  usepackage [] "amsfonts"
  usepackage [] "amssymb"
  usepackage [] "amsthm"

  -- For an even bigger font
  usepackage [] "fix-cm"

  -- For logical inference
  usepackage [] "proof"

  -- For a nice font with math support
  usepackage [] "libertine"
  usepackage ["libertine"] "newtxmath"

  -- To count pages
  usepackage [] "lastpage"
  usepackage [] "afterpage"

  -- To get pages in the right position
  usepackage [] "float"

  -- For frames
  usepackage [] "mdframed"

  -- To adjust marges
  usepackage ["left=2cm", "right=2cm", "top=2cm", "bottom=2cm", "headheight=15pt"] "geometry"

  -- For colros
  usepackage [] "color"

  -- For intervals
  usepackage [] "interval"

  -- For nicer enumerates
  usepackage [] "enumerate"

  -- For nicer verbatim pieces
  usepackage [] "verbatim"

  -- For urls
  usepackage ["hidelinks"] "hyperref"

  usepackage [] "listings"
  usepackage [] "minted"

  -- For nicer inline fractions
  usepackage [] "nicefrac"

  -- For a nicer code font
  usepackage [] "courier"

  -- For indices
  usepackage [] "makeidx"

  -- For colored text
  usepackage [] pcolor

  -- To cancel terms in math
  usepackage [] "cancel"

  -- For bold math
  usepackage [] "bm"

  -- For fancy logic proofs
  usepackage [] "bussproofs"

  -- For sideways figures
  usepackage [] "rotating"

  -- For the nice header
  applyHdrSettings myHdrSettings

  commS "makeindex"

myHdrSettings :: HdrSettings
myHdrSettings =  HdrSettings
    {
      leftHeader    = mempty
    , centerHeader  = large $ textsc "the notes"
    , rightHeader   = mempty
    , leftFooter    = "Tom Sydney Kerckhove"
    , centerFooter  = mempty
    , rightFooter   = thePage
    , headRuleWidth = Pt 0.4
    , footRuleWidth = Pt 0.4
    }


packageDep :: String -> [TeXArg] -> Note
packageDep name args = modify (\s -> s {state_packages = S.insert (PackageDep name args) $ state_packages s})

packageDep_ :: String -> Note
packageDep_ name = packageDep name []

injectPackageDependencies :: [PackageDep] -> LaTeX -> LaTeX
injectPackageDependencies ps = go
    -- We're looking for this: TeXComm "documentclass" [MOptArg $ fmap rendertex opts , FixArg $ fromString cn]
  where
    -- We have to go looking through the LaTeX :(
    go t@(TeXComm "documentclass" _) = TeXSeq t packages
    go (TeXSeq t1 t2) = TeXSeq (go t1) (go t2)
    go c = c

    packages :: LaTeX
    packages = mconcat $ map (\(PackageDep name args) -> TeXComm "usepackage" $ args ++ [FixArg $ fromString name]) ps

