{-# LANGUAGE ConstraintKinds          #-}
{-# LANGUAGE CPP                      #-}
{-# LANGUAGE FlexibleContexts         #-}
{-# LANGUAGE FlexibleInstances        #-}
{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE JavaScriptFFI            #-}
{-# LANGUAGE MultiParamTypeClasses    #-}
{-# LANGUAGE OverloadedStrings        #-}
{-# LANGUAGE RecordWildCards          #-}
{-# LANGUAGE RecursiveDo              #-}
{-# LANGUAGE ScopedTypeVariables      #-}
{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE UndecidableInstances     #-}

module Reflex.Dom.SemanticUI.Container where

------------------------------------------------------------------------------
import           Data.Default
import           Data.Maybe
import           Data.Monoid
import           Data.Text (Text)
import qualified Data.Text as T
import           Reflex.Dom hiding (fromJSString)
------------------------------------------------------------------------------
import           Reflex.Dom.SemanticUI.Common
import           Reflex.Dom.SemanticUI.Icon
------------------------------------------------------------------------------

data UiContainer = UiContainer
    { _uiContainer_size        :: Maybe UiSize
    , _uiContainer_left        :: Maybe UiLeft
    , _uiContainer_fluid       :: Maybe UiFluid
    , _uiContainer_text        :: Maybe UiText
    } deriving (Eq,Show)

instance Default UiContainer where
  def = UiContainer def def def def

instance UiHasSize UiContainer where
  uiSetSize s i = i { _uiContainer_size = Just s }

instance UiHasLeft UiContainer where
  uiLeft i = i { _uiContainer_left = Just UiLeft }

instance UiHasFluid UiContainer where
  fluid i = i { _uiContainer_fluid = Just UiFluid }

instance UiHasText UiContainer where
  text i = i { _uiContainer_text = Just UiText }

uiContainerAttrs :: UiContainer -> Text
uiContainerAttrs UiContainer{..} = T.unwords $ catMaybes
    [ uiText <$> _uiContainer_size
    , uiText <$> _uiContainer_left
    , uiText <$> _uiContainer_fluid
    , uiText <$> _uiContainer_text
    ]

uiContainer
    :: MonadWidget t m
    => Dynamic t UiContainer
    -> m a
    -> m a
uiContainer iDyn children =
    elDynAttr "div" (mkAttrs <$> iDyn) children
  where
    mkAttrs i = "class" =: T.unwords ["ui", uiContainerAttrs i, "container"]
