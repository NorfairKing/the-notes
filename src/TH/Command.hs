module TH.Command where

import           Prelude

import           Types
import           Utils

import           Language.Haskell.TH

comm :: Int -> String -> Q [Dec]
comm n c = comm_ n c c

comm_ :: Int -> String -> String -> Q [Dec]
comm_ n c c' = return [sig, fun]
  where
    name = mkName . camelCase . sanitize $ c'
    sig = SigD name (ConT ''Note)
    fun = FunD name
            [ Clause
                []
                (NormalB $ AppE (VarE $ mkName $ "comm" ++ show n) (LitE $ StringL $ c))
                []
            ]
