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
  -- For maths
  packageDep_ "amsmath"
  packageDep_ "amsfonts"
  packageDep_ "amssymb"
  packageDep_ "amsthm"

  -- For an even bigger font
  packageDep_ "fix-cm"

  -- For logical inference
  packageDep_ "proof"

  -- For a nice font with math support
  packageDep_ "libertine"
  packageDep  "newtxmath" ["libertine"]

  -- To count pages
  packageDep_ "lastpage"
  packageDep_ "afterpage"

  -- To adjust marges
  packageDep "geometry" ["left=2cm", "right=2cm", "top=2cm", "bottom=2cm", "headheight=15pt"]

  -- For colros
  packageDep_ "color"

  -- For intervals
  packageDep_ "interval"

  -- For nicer enumerates
  packageDep_ "enumerate"

  -- For nicer verbatim pieces
  packageDep_ "verbatim"

  -- For urls
  usepackage ["hidelinks"] "hyperref"

  packageDep_ "listings"
  packageDep_ "minted"

  -- For a nicer code font
  packageDep_ "courier"

  -- For indices
  packageDep_ "makeidx"

  -- For colored text
  packageDep_ pcolor

  -- To cancel terms in math
  packageDep_ "cancel"

  -- For fancy logic proofs
  packageDep_ "bussproofs"

  -- For the nice header
  applyHdrSettings myHdrSettings

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


packageDep :: String -> [LaTeX] -> Note
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
    packages = mconcat $ map (\(PackageDep name args) -> usepackage args name) ps

