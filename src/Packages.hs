module Packages (packages) where

import           Notes

packages :: Note
packages = do
  -- For frames
  usepackage [] "mdframed"

  -- For maths
  usepackage [] "amsmath"
  usepackage [] "amsfonts"
  usepackage [] "amssymb"
  usepackage [] "amsthm"

  -- For logical inference
  usepackage [] "proof"

  -- For todo's
  usepackage ["colorinlistoftodos", "obeyFinal"] "todonotes"

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

