module Macro.Array where

import           Types

import           Control.Monad (sequence_)
import qualified Prelude       as P

import           Macro.Math

linedTable :: [Note] -> [[Note]] -> Note
linedTable header notes = m $ array (Just Center) specs $ do
    hline
    row header
    lnbk
    hline
    hline
    content notes
    hline
  where
    specs :: [TableSpec]
    specs = VerticalLine : P.concat (P.replicate (P.length header) [CenterColumn, VerticalLine])

    row :: [Note] -> Note
    row [] = mempty
    row [n] = n
    row (n:ns) = n & row ns

    content :: [[Note]] -> Note
    content [] = mempty
    content [n] = do
      row n
      lnbk
    content (n:ns) = do
      row n
      lnbk
      hline
      content ns

-- * Math statements below eachother

-- | Math statements below eachother using an array.
belowEachOther :: [TableSpec] -> [Note] -> Note
belowEachOther sp = array Nothing sp . sequence_ . P.map (<> lnbk)

-- | Same as @belowEachOther@ but left outlined.
leftBelowEachOther :: [Note] -> Note
leftBelowEachOther = belowEachOther [LeftColumn]

-- | Same as @belowEachOther@ but centered.
centeredBelowEachOther :: [Note] -> Note
centeredBelowEachOther = belowEachOther [CenterColumn]
