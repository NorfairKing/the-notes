module Packages (packages) where

import           Types

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
    packageDep ["mono=false"] "libertine" -- Don't load the monospace font, otherwise verbatim will be messed up.
    packageDep ["libertine"] "newtxmath"

    -- To count pages
    packageDep_ "lastpage"
    packageDep_ "afterpage"

    -- To adjust marges
    packageDep  [
                    "left=2cm"
                  , "right=2cm"
                  , "top=2cm"
                  , "bottom=2cm"
                  , "headheight=15pt"
                ] "geometry"

    -- For colros
    packageDep_ "color"

    -- For intervals
    packageDep_ "interval"

    -- For nicer enumerates
    packageDep_ "enumerate"

    -- For nicer verbatim pieces
    packageDep_ "verbatim"

    -- For urls
    packageDep ["hidelinks"] "hyperref"

    packageDep_ "listings"

    -- For a nicer code font
    packageDep_ "courier"

    -- For indices
    packageDep_ "makeidx"

    -- For colored text
    packageDep_ "color"

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

