module Notes (
    module Types
  , module Notes
  , module Text.LaTeX
  , module Text.LaTeX.Base.Class
  , module Text.LaTeX.Packages.AMSMath
  , module Text.LaTeX.Base.Pretty
  , module Text.LaTeX.Packages.Fancyhdr
  , module Text.LaTeX.Packages.AMSMath
  , module Text.LaTeX.Packages.AMSThm
  , module Text.LaTeX.Packages.AMSFonts
  ) where

import           Text.LaTeX
import           Text.LaTeX.Base.Class
import           Text.LaTeX.Base.Pretty
import           Text.LaTeX.Base.Syntax
import           Text.LaTeX.Packages.AMSFonts
import           Text.LaTeX.Packages.AMSMath
import           Text.LaTeX.Packages.AMSThm   hiding (proof)
import           Text.LaTeX.Packages.Fancyhdr

import qualified Data.Text                    as T

import           Types

notes :: String -> [Notes] -> Notes
notes = NotesPartList

notesPart :: String ->  Note -> Note -> Notes
notesPart name preamble body = NotesPart $ Part name preamble body

renderNotes :: Notes -> LaTeXT_ IO
renderNotes notes = renderParts $ flattenNotes notes

flattenNotes :: Notes -> [Part]
flattenNotes = go ""
  where
    go path (NotesPart pt) = [pt {part_name = path <.> part_name pt} ]
    go path (NotesPartList name ds) = concatMap (go $ path <.> name) ds

    (<.>) :: String -> String -> String
    s1 <.> s2 = s1 ++ "." ++ s2

renderParts :: [Part] -> LaTeXT_ IO
renderParts ps = do
    liftIO $ putStrLn "\nBuilding parts:"
    liftIO $ mapM_ putStrLn $ map part_name ps
    liftIO $ putStrLn ""


    documentclass [] book
    sequence_ $ map part_preamble ps
    document $ sequence_ $ map part_body ps




notesChapter :: Text -> Note
notesChapter title = do
  chapter $ raw title
  label . raw $ T.concat ["ch:", T.toLower title]

notesSection :: Text -> Note
notesSection title = do
  section $ raw title
  label . raw $ T.concat ["sec:", T.toLower title]

de :: Note -> Note
de = theorem "de"

thm :: Note -> Note
thm = theorem "thm"

nte :: Note -> Note
nte = theorem "nte"

index :: Note -> Note
index = comm1 "index"

environment :: String -> (Note -> Note)
environment name = liftL $ TeXEnv name []

ix :: Text -> Note
ix text = do
    index rt
    rt
  where
    rt = raw text

term :: Text -> Note
term text = do
    index rt
    textbf rt
  where
    rt = raw text


newtheorem' :: LaTeXC l => String -> l -> l
newtheorem' name = liftL $ \l -> TeXComm "newtheorem" [ FixArg $ fromString name , OptArg "thm", FixArg l ]

newmdtheoremenv :: LaTeXC l => String -> l -> l
newmdtheoremenv name = liftL $ \l -> TeXComm "newmdtheoremenv" [ FixArg $ fromString name , OptArg "thm", FixArg l ]

comm2 :: LaTeXC l => String -> l -> l -> l
comm2 name = liftL2 $ (\l1 l2 -> TeXComm name [FixArg l1, FixArg l2])

comm3 :: LaTeXC l => String -> l -> l -> l -> l
comm3 name = liftL3 $ (\l1 l2 l3 -> TeXComm name [FixArg l1, FixArg l2, FixArg l3])

renewcommand :: LaTeXC l => l -> l -> l
renewcommand l = comm2 "renewcommand" (raw "\\" <> l)

renewcommand1 :: LaTeXC l => l -> l -> l
renewcommand1 = liftL2 $ (\l1 l2 -> TeXComm "renewcommand" [FixArg $ raw "\\" <> l1, OptArg "1", FixArg l2])

boxed :: Note -> Note
boxed n = raw "\\text{\\fboxsep=.2em\\fbox{\\m@th$\\displaystyle" <> n <> "$}}"

bla :: Note
bla = boxed leftArrow

bra :: Note
bra = boxed rightArrow

leftRightarrow :: Note
leftRightarrow = comm0 "Leftrightarrow"

leftrightarrow :: Note
leftrightarrow = comm0 "leftrightarrow"

leftarrow :: Note
leftarrow = comm0 "leftarrow"

leftArrow :: Note
leftArrow = comm0 "Leftarrow"

rightarrow :: Note
rightarrow = comm0 "rightarrow"

rightArrow :: Note
rightArrow = comm0 "Rightarrow"

m :: Note -> Note
m = math

ma :: Note -> Note
ma = mathDisplay

pars :: Note -> Note
pars = autoParens

brac :: Note -> Note
brac = autoBraces

sqbrac :: Note -> Note
sqbrac = autoSquareBrackets

setof :: Note -> Note
setof = brac

mid :: Note
mid = raw "\\mid "

setcmpr :: Note -> Note -> Note
setcmpr n m = setof $ n <> mid <> m

divSign :: Note
divSign = mid

mdiv :: Note -> Note -> Note
mdiv = binop divSign

defineasSign :: Note
defineasSign = comm0 "quad" <> comm0 "equiv" <> comm0 "quad"

defineas :: Note -> Note -> Note
defineas = binop defineasSign

(===) :: Note -> Note -> Note
(===) = defineas

forallSign :: Note
forallSign = comm0 "forall"

mfa :: Note -> Note -> Note
mfa n m = forallSign <> n <> ":" <> raw "\\ " <> m

setlst :: Note -> Note -> Note
setlst n m = setof $ n <> ", " <> dotsc <> ", " <> m

setlist :: Note -> Note -> Note -> Note
setlist m n o = setof $ m <> ", " <> n <> ", " <> dotsc <> ", " <> o

dotsc :: Note
dotsc = comm0 "dotsc"

fun :: Note -> Note -> Note -> Note
fun m n o = m <> ":" <> raw "\\ " <> n <> rightarrow <> o

func :: Note -> Note -> Note -> Note -> Note -> Note
func m n o p q = fun m n o <> ":" <> raw "\\ " <> p <> comm0 "mapsto" <> q

-- Functions
funinv :: Note -> Note
funinv n = n ^: (-1)

funapp :: Note -> Note -> Note
funapp n m = n <> pars m

-- Intervals
ooint :: LaTeXC l => l -> l -> l
ooint = liftL2 $ (\l1 l2 -> TeXComm "interval" [OptArg "open", FixArg l1, FixArg l2])

ocint :: LaTeXC l => l -> l -> l
ocint = liftL2 $ (\l1 l2 -> TeXComm "interval" [OptArg "open left", FixArg l1, FixArg l2])

coint :: LaTeXC l => l -> l -> l
coint = liftL2 $ (\l1 l2 -> TeXComm "interval" [OptArg "open right", FixArg l1, FixArg l2])

ccint :: LaTeXC l => l -> l -> l
ccint = liftL2 $ (\l1 l2 -> TeXComm "interval" [FixArg l1, FixArg l2])


-- Nicer equality symbol
ge :: Note
ge = comm0 "geqslant"

le :: Note
le = comm0 "leqslant"

seq :: Note -> Note -> Note
seq m n = brac m !: n

overset :: Note -> Note -> Note
overset = comm2 "overset"

underset :: Note -> Note -> Note
underset = comm2 "underset"

seteqsign :: Note
seteqsign = underset "set" "="

(=§=) :: Note -> Note -> Note
(=§=) = binop seteqsign

setneqsign :: Note
setneqsign = underset "set" $ comm0 "neq"

mand :: Note -> Note -> Note
mand = wedge

(&:) :: Note -> Note -> Note
(&:) = mand

mor :: Note -> Note -> Note
mor = vee

(|:) :: Note -> Note -> Note
(|:) = mor

-- C-k (-
(∈) :: Note -> Note -> Note
(∈) = in_

quoted :: Note -> Note
quoted n = "`" <> n <> "'"

iffsign :: Note
iffsign = leftRightarrow

iff :: Note -> Note -> Note
iff m n = m <> iffsign <> n

-- C-k ==
(⇔) :: Note -> Note -> Note
(⇔) = iff

impliessign :: Note
impliessign = rightArrow

mimplies :: Note -> Note -> Note
mimplies m n = m <> impliessign <> n

-- C-k =>
(⇒) :: Note -> Note -> Note
(⇒) = mimplies

proof :: Note -> Note
proof = liftL $ TeXEnv "proof" []

subseteqsign :: Note
subseteqsign = comm0 "subseteq"

subseteq :: Note -> Note -> Note
subseteq m n = m <> subseteqsign <> n

binop :: Note -> Note -> Note -> Note
binop = between

-- C-k (_
(⊆) :: Note -> Note -> Note
(⊆) = subseteq

subsetneqsign :: Note
subsetneqsign = comm0 "subsetneq"

subsetneq :: Note -> Note -> Note
subsetneq = binop subsetneqsign

setneq :: Note -> Note -> Note
setneq = binop setneqsign

setuniverse :: Note
setuniverse = comm0 "Omega"

emptyset :: Note
emptyset = comm0 "emptyset"

-- Shorter than sequence_
s :: [Note] -> Note
s = sequence_
