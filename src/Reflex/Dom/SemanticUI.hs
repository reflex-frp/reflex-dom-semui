{-# LANGUAGE TemplateHaskell #-}

module Reflex.Dom.SemanticUI
  ( module Reflex.Dom.SemanticUI.Button
  , module Reflex.Dom.SemanticUI.Checkbox
  , module Reflex.Dom.SemanticUI.Common
  , module Reflex.Dom.SemanticUI.Dropdown
  , module Reflex.Dom.SemanticUI.Icon
  , module Reflex.Dom.SemanticUI.Input
  , module Reflex.Dom.SemanticUI.Modal
  , semanticCSS
  ) where

------------------------------------------------------------------------------
import           Data.FileEmbed
import           Data.Text (Text)
------------------------------------------------------------------------------
import           Reflex.Dom.SemanticUI.Button
import           Reflex.Dom.SemanticUI.Checkbox
import           Reflex.Dom.SemanticUI.Common
import           Reflex.Dom.SemanticUI.Dropdown
import           Reflex.Dom.SemanticUI.Icon
import           Reflex.Dom.SemanticUI.Input
import           Reflex.Dom.SemanticUI.Modal
------------------------------------------------------------------------------


------------------------------------------------------------------------------
-- | The contents of the upstream semantic.min.css stylesheet as a Text value.
semanticCSS :: Text
semanticCSS = $(embedStringFile "lib/semantic.min.css")
