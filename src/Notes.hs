module Notes (
    module Types
  , module Notes
  , module Macro
  , module TH

  , note
  , module Text.LaTeX.LambdaTeX.Reference
  , module Text.LaTeX.LambdaTeX.Reference.Types
  ) where

import           Types

import           TH

import           Macro
import           Text.LaTeX.LambdaTeX.Reference

import           Prelude

import           Control.Monad.Reader                 (runReaderT)
import           Control.Monad.State                  (runStateT)


import           Text.LaTeX.LambdaTeX                 (execLambdaTeXT, note)
import           Text.LaTeX.LambdaTeX.Reference.Types (Reference (..))
import           Text.LaTeX.LambdaTeX.Selection.Types (Selection)

runNote :: Note -> Config -> Selection -> State -> IO (Either String (LaTeX, [Reference]), State)
runNote note conf λconf state = runReaderT (runStateT (execLambdaTeXT note λconf) state) conf

