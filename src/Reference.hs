module Reference where

import           Types

import           Data.List           (intercalate)
import qualified Data.Set            as S
import           Prelude             (map)

import           Control.Monad.State (modify)


unpublished :: ReferenceType
unpublished = "unpublished"

lectureSlides :: ReferenceType
lectureSlides = "unpublished"

online :: ReferenceType
online = "online"

article :: ReferenceType
article = "article"

showReferences :: [Reference] -> String
showReferences rs = (++ "\n\n") . intercalate ",\n\n" $ map showRef rs
  where
    showRef :: Reference -> String
    showRef (Reference rType name fs) =
        "@" ++ rType ++ "{" ++ name ++ ",\n"
        ++ intercalate ",\n" (map showField fs)
        ++ "\n}"

    showField :: (String, String) -> String
    showField (a, b) = "  " ++ a ++ " = {" ++ b ++ "}"


refName :: LaTeXC l => Reference -> l
refName (Reference _ name _) = fromString name

addReference :: Reference -> Note
addReference ref = modify (\s -> s {state_refs = S.insert ref $ state_refs s})

