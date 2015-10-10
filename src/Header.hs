module Header (header) where

import           Notes

header :: Note
header = do
  theoremDefinitions
  mathHeader

  -- \noindent everywhere
  raw "\\setlength\\parindent{0pt}"

theoremDefinitions :: Note
theoremDefinitions = do
  theoremstyle Definition

  raw "\\newtheorem{thm}{Theorem}[chapter]"

  newtheorem' "prop" "Property"
  newtheorem' "pro" "Proposition"
  newtheorem' "nte" "Note"
  newtheorem' "ex" "Example"
  newtheorem' "cex" "Counterexample"
  newtheorem' "con" "Concequence"
  newtheorem' "lem" "Lemma"

  newmdtheoremenv "de" "Definition"
  newmdtheoremenv "alg" "Algorithm"

mathHeader :: Note
mathHeader = do
  renewcommand "arraystretch" 1.25
  renewcommand "qedsymbol" (m $ commS "square")

  renewcommand "leq" (comm0 "leqslant")
  renewcommand "geq" (comm0 "geqslant")


atletteratother :: Note -> Note
atletteratother n = between n (commS "makeatletter") (commS "makeatother")
