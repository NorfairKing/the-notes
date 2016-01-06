module License (license) where

import           Notes

url :: Note -> Note
url = comm1 "url"

license :: Note
license = do
    comm1 "section*" "License"
    s ["This work is licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International License"]
    s ["To view a copy of this license, visit ", url "http://creativecommons.org/licenses/by-nc-nd/4.0/"]
    hereFigure $ huge2 $ copyleft

copyleft :: Note
copyleft = do
    packageDep_ "textcomp"
    comm0 "textcopyleft"
