module Macro.Array where

import           Types

import           Control.Monad (sequence_)
import qualified Prelude       as P

import           Macro.Math

-- | The 'tabular' environment can be used to typeset tables with optional horizontal and vertical lines.
array :: LaTeXC l =>
    Maybe Pos       -- ^ This optional parameter can be used to specify the vertical position of the table.
                    --   Defaulted to 'Center'.
    -> [TableSpec]  -- ^ Table specification of columns and vertical lines.
    -> l            -- ^ Table content. See '&', 'lnbk', 'hline' and 'cline'.
    -> l            -- ^ Resulting table syntax.
array Nothing ts  = liftL $ TeXEnv "array" [ FixArg $ TeXRaw $ renderAppend ts ]
array (Just p) ts = liftL $ TeXEnv "array" [ OptArg $ TeXRaw $ render p , FixArg $ TeXRaw $ renderAppend ts ]



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
    specs = VerticalLine : P.concat (P.replicate (P.length notes) [CenterColumn, VerticalLine])

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
