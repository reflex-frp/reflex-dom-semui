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

module Reflex.Dom.SemanticUI.Input where

------------------------------------------------------------------------------
import           Data.Default
import           Data.Maybe
import           Data.Text (Text)
import qualified Data.Text as T
import           Reflex.Dom hiding (fromJSString)
------------------------------------------------------------------------------
import           Reflex.Dom.SemanticUI.Common
------------------------------------------------------------------------------

data UiInput = UiInput
    { _uiInput_size       :: Maybe UiSize
    , _uiInput_loading    :: Maybe UiLoading
    , _uiInput_error      :: Maybe UiError
    } deriving (Eq,Show)

instance Default UiInput where
  def = UiInput def def def

instance UiHasSize UiInput where
  uiSetSize s b = b { _uiInput_color = Just s }

instance UiHasLoading UiButton where
  loading b = b { _uiButton_loading = Just UiLoading }

instance UiHasError UiInput where
  hasError b = b { _uiInput_error = Just UiError }

uiInputAttrs :: UiInput -> Text
uiInputAttrs UiInput{..} = T.unwords $ catMaybes
    [ uiText <$> _uiInput_size
    , uiText <$> _uiInput_loading
    , uiText <$> _uiInput_error
    ]

uiInput
    :: MonadWidget t m
    => Dynamic t UiInput
    -> TextInputConfig t
    -> m (TextInput t)
uiInput iDyn c =
    elDynAttr' "div" (mkAttrs <$> iDyn) $ textInput c
  where
    mkAttrs b = "class" =: T.unwords ["ui", uiInputAttrs b, "button"]

