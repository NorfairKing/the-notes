module Logic.PropositionalLogic (propositionalLogic) where

import           Logic.AbstractLogic
import           Notes

import           Data.List           (concat, intersperse, length, replicate)

propositionalLogic :: Notes
propositionalLogic = notesPart "propositional-logic" body

body :: Note
body = do
  propositionalLogicDefinition
  truthTables

propositionalLogicDefinition :: Note
propositionalLogicDefinition = do
  de $ do
    s ["The ", term "propositional logic", " has a ", grammar, " ", m g, " and only two axioms."]
    enumerate $ do
      item $ do
        s [m g, " defines well formed formulas recursively with the following cases."]
        itemize $ do
          item $ s [dquoted "true", " and ", dquoted "false", " are sentences."]
          item $ s ["So-called propositional symbols, boolean variables, are sentences."]
          item $ s ["If ", m ss, " is a sentence, then ", m (neg ss), " is a sentence and it is true only if ", m ss, " is not."]
          item $ s ["If ", m s1, " and ", m s2, " are sentences, then ", m (s1 ∨ s2), " is a sentence and it is true only if one of ", m s1, and, m s2, " are true."]
          item $ s ["If ", m s1, " and ", m s2, " are sentences, then ", m (s1 ∧ s2), " is a sentence and it is true only if both ", m s1, and, m s2, " are true."]
      item $ do
        s ["The sentences ", dquoted "true", " and ", dquoted "false", " are respesctively asserted to be true and false."]
    s ["In propositional logic, a world defines a truth value to every propositional symbol."]

  nte $ do
    "There are some very common notational shorthands in propositional logic: "
    itemize $ do
      item $ s [dquoted (m $ s1 ⇒ s2), " for ", dquoted (m $ neg s1 ∨ s2)]
      item $ s [dquoted (m $ s1 ⇔ s2), " for ", dquoted (m $ (pars $ s1 ⇒ s2) ∧ (pars $ s2 ⇒ s1))]

  where
    ss = "S"
    s1 = ss !: 1
    s2 = ss !: 2
    g = ("G" !: mathbb "I")


		-- | The 'tabular' environment can be used to typeset tables with optional horizontal and vertical lines.
array :: LaTeXC l =>
		Maybe Pos   -- ^ This optional parameter can be used to specify the vertical position of the table.
		--   Defaulted to 'Center'.
		-> [TableSpec] -- ^ Table specification of columns and vertical lines.
		-> l       -- ^ Table content. See '&', 'lnbk', 'hline' and 'cline'.
		-> l       -- ^ Resulting table syntax.
array Nothing ts  = liftL $ TeXEnv "array" [ FixArg $ TeXRaw $ renderAppend ts ]
array (Just p) ts = liftL $ TeXEnv "array" [ OptArg $ TeXRaw $ render p , FixArg $ TeXRaw $ renderAppend ts ]


linedTable :: [Note] -> [[Note]] -> Note
linedTable header notes = ma $ do
  array (Just Center) specs $ do
    hline
    row header
    lnbk
    hline
    hline
    content notes
    hline

  where
    specs :: [TableSpec]
    specs = VerticalLine: (concat $ replicate (length notes) [CenterColumn, VerticalLine])

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


truthTables :: Note
truthTables = do
  truthTableNot
  truthTableOr
  truthTableAnd
  truthTableImplies
  truthTableXor

truthTableNot :: Note
truthTableNot = do
  linedTable
    ["A", not "A"]
    [
      [true , false]
    , [false, true]
    ]

truthTableOr :: Note
truthTableOr = do
  linedTable
    ["A", "B", "A" ∨ "B"]
    [
      [false, false, false]
    , [false, true , true ]
    , [true , false, true ]
    , [true , true , true ]
    ]

truthTableAnd :: Note
truthTableAnd = do
  linedTable
    ["A", "B", "A" ∧ "B"]
    [
      [false, false, false]
    , [false, true , false]
    , [true , false, false]
    , [true , true , true ]
    ]

truthTableImplies :: Note
truthTableImplies = do
  linedTable
    ["A", "B", "A" ⇒ "B"]
    [
      [false, false, true ]
    , [false, true , true ]
    , [true , false, false]
    , [true , true , true ]
    ]

truthTableXor :: Note
truthTableXor = do
  linedTable
    ["A", "B", "A" `xor` "B"]
    [
      [false, false, false]
    , [false, true , true ]
    , [true , false, true ]
    , [true , true , false]
    ]
