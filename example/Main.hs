{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Data.Map (Map)
import Data.Text (Text)
import Reflex.Dom
import Reflex.Dom.SemanticUI

main :: IO ()
main = mainWidget $ do
  el "p" $ text "These are examples of semantic-ui widgets."
  el "p" $ uiButton (huge $ inverted $ blue def) (text "I'm a huge, inverted, blue button!")
