module Reference where

import           Types

import           Data.List (intercalate)
import           Prelude   (map)


unpublished :: ReferenceType
unpublished = "unpublished"

lectureSlides :: ReferenceType
lectureSlides = "unpublished"

showReferences :: [Reference] -> String
showReferences rs = (++ "\n\n") . intercalate ",\n\n" $ map showRef rs
  where
    showRef :: Reference -> String
    showRef (Reference rType name fs) =
        "@" ++ rType ++ "{" ++ name ++ ",\n"
        ++ intercalate ",\n" (map showField fs)
        ++ "\n}"

    showField :: (String, String) -> String
    showField (a, b) = "  " ++ a ++ " = \"" ++ b ++ "\""


refName :: LaTeXC l => Reference -> l
refName (Reference _ name _) = fromString name
