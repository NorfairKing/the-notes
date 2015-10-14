module Logic.PropositionalLogic (propositionalLogic) where

import           Logic.AbstractLogic (complete, grammar, inference, sound)
import           Notes

import           Data.List           (concat, intersperse, length, replicate)

propositionalLogic :: Notes
propositionalLogic = notesPartRef "propositional-logic" body [tseitinTransformation]

body :: Note
body = do
  propositionalLogicDefinition
  truthTables
  normalForms
  inferences

propositionalLogicDefinition :: Note
propositionalLogicDefinition = do
  de $ do
    s ["The ", term "propositional logic", " has a ", grammar, " ", m g, " and only two axioms"]
    enumerate $ do
      item $ do
        s [m g, " defines well formed formulas recursively with the following cases"]
        itemize $ do
          item $ s [dquoted "true", " and ", dquoted "false", " are sentences"]
          item $ s ["So-called propositional symbols, boolean variables, are sentences"]
          item $ s ["If ", m ss, " is a sentence, then ", m (neg ss), " is a sentence and it is true only if ", m ss, " is not"]
          item $ s ["If ", m s1, " and ", m s2, " are sentences, then ", m (s1 ∨ s2), " is a sentence and it is true only if one of ", m s1, and, m s2, " are true"]
          item $ s ["If ", m s1, " and ", m s2, " are sentences, then ", m (s1 ∧ s2), " is a sentence and it is true only if both ", m s1, and, m s2, " are true"]
      item $ do
        s ["The sentences ", dquoted "true", " and ", dquoted "false", " are respesctively asserted to be true and false"]
    s ["In propositional logic, a world defines a truth value to every propositional symbol"]

  nte $ do
    "There are some very common notational shorthands in propositional logic."
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
linedTable header notes = m $ do
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

-- | Figure environment.
hereFigure :: LaTeXC l => l -> l
hereFigure = liftL $ (\n -> TeXEnv "figure" [ OptArg $ TeXRaw $ "H" ] (comm0 "centering" <> n))

truthTables :: Note
truthTables = nte $ do
  s ["Truth tables are a very common and naive way of reasoning about sentences propositional logic"]
  s ["The validity of a proposition is checked by enumerating the truth table for the sentence and checking whether all the values in the column for the sentence are true"]

  hereFigure $ do
		truthTableNot
  hereFigure $ do
		truthTableOr
		m quad
		truthTableAnd
  hereFigure $ do
		truthTableImplies
		m quad
		truthTableIff
		m quad
		truthTableXor
		caption "Elementary truth tables"

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


truthTableIff :: Note
truthTableIff = do
  linedTable
    ["A", "B", "A" ⇔ "B"]
    [
      [false, false, true ]
    , [false, true , false]
    , [true , false, false]
    , [true , true , true]
    ]


normalForms :: Note
normalForms = do
  subsection "Normal forms"
  conjunctiveNormalForm

conjunctiveNormalForm :: Note
conjunctiveNormalForm = do
  subsubsection "Conjunctive Normal Form"
  de $ do
    s ["A sentence in propositional logic is said to be in ", term "conjunctive normal form", or, term "clausal normal form", " (", term "CNF", ") if it is a conjunction of clauses where a clause is a disjunction of literals"]
  thm $ do
    s ["Every sentence propositional logic can be converted into an equivalent formula that is in CNF"]
    np
    s ["There is a famous transformation called the ", term "Tseitin transformation", " that does exactly this"]
    cite tseitinTransformation


tseitinTransformation :: Reference
tseitinTransformation = Reference "article" "tseitin68" $
  [
    ("author", "Tseitin, G. S.")
  , ("journal", "Studies in Mathematics and Mathematical Logic")
  , ("pages", "234–259")
  , ("title", "On the complexity of derivations in the propositional calculus")
  , ("volume", "Part II")
  , ("year", "1968")
  ]

inferences :: Note
inferences = do
  subsection "Inference in propositional logic"
  resolution

resolution :: Note
resolution = do
  de $ do
    s ["The ", inference, " ", term "rule of resolution", " is an inference in proposition logic"]
    s ["Let ", m a, and, m b, " be propositional formulae in CNF."]
    ma $ do
      a =: vsep [a !: 1, a !: 2, dotsc, a !: k]
      quad
      b =: vsep [b !: 1, b !: 2, dotsc, b !: l]
    s ["Suppose also that, for some ", m i, and, m j, ", ", m (a !: i =: not (b !: j)), " holds"]
    ma $ do
      linf [vsep [a !: 1, a !: 2, dotsc, a !: k], vsep [b !: 1, b !: 2, dotsc, b !: l]] $
        vsep $
          [a !: 1, a !: 2, dotsc, a !: (i - 1), a !: (i + 1), dotsc, a !: k]
          ++
          [b !: 1, b !: 2, dotsc, b !: (j - 1), b !: (j + 1), dotsc, b !: k]

  thm $ do
    s ["This ", inference, " is ", sound, and, complete, "."]
    toprove

  nte $ do
    s ["Eventhough this ", inference, " is ", sound, and, complete, ", finding proofs can be difficult as search spaces become exponentially large"]
    citneeded

  where
    vsep = separated lorsign
    a = "a"
    b = "b"
    k = "k"
    l = "l"
    i = "i"
    j = "j"
