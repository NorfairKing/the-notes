{-# LANGUAGE TemplateHaskell #-}
module TH.Test where

import           Notes

makeDef "domain"

hi :: String
hi = "hi"

