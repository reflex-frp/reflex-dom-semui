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
import           Data.Text (Text)
import qualified Data.Text as T
import           Reflex.Dom.Core hiding (fromJSString)
------------------------------------------------------------------------------
import           Reflex.Dom.SemanticUI.Common
------------------------------------------------------------------------------


------------------------------------------------------------------------------
-- | This is an attribute that can be applied to components.  Right now it is
-- used by container.
data UiTextContainer = UiTextContainer
  deriving (Eq,Ord,Read,Show,Enum,Bounded)

instance UiClassText UiTextContainer where
  uiText UiTextContainer = "text"

class UiHasTextContainer a where
  textContainer :: a -> a

data UiContainer = UiContainer
    { _uiContainer_size  :: Maybe UiSize
    , _uiContainer_left  :: Maybe UiLeft
    , _uiContainer_fluid :: Maybe UiFluid
    , _uiContainer_text  :: Maybe UiTextContainer
    } deriving (Eq,Show)

instance Default UiContainer where
  def = UiContainer def def def def

instance UiHasSize UiContainer where
  uiSetSize s i = i { _uiContainer_size = Just s }

instance UiHasLeft UiContainer where
  uiLeft i = i { _uiContainer_left = Just UiLeft }

instance UiHasFluid UiContainer where
  fluid i = i { _uiContainer_fluid = Just UiFluid }

instance UiHasTextContainer UiContainer where
  textContainer i = i { _uiContainer_text = Just UiTextContainer }

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
