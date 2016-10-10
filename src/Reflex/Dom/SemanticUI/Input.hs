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
import           Data.Monoid
import           Data.Text (Text)
import qualified Data.Text as T
import           Reflex.Dom hiding (fromJSString)
------------------------------------------------------------------------------
import           Reflex.Dom.SemanticUI.Common
import           Reflex.Dom.SemanticUI.Icon
------------------------------------------------------------------------------

data UiInput = UiInput
    { _uiInput_size       :: Maybe UiSize
    , _uiInput_left       :: Maybe UiLeft
    , _uiInput_loading    :: Maybe UiLoading
    , _uiInput_error      :: Maybe UiError
    } deriving (Eq,Show)

instance Default UiInput where
  def = UiInput def def def def

instance UiHasSize UiInput where
  uiSetSize s b = b { _uiInput_size = Just s }

instance UiHasLoading UiInput where
  loading b = b { _uiInput_loading = Just UiLoading }

instance UiHasLeft UiInput where
  uiLeft b = b { _uiInput_left = Just UiLeft }

instance UiHasError UiInput where
  hasError b = b { _uiInput_error = Just UiError }

uiInputAttrs :: UiInput -> Text
uiInputAttrs UiInput{..} = T.unwords $ catMaybes
    [ uiText <$> _uiInput_size
    , uiText <$> _uiInput_left
    , (<> " icon") . uiText <$> _uiInput_loading
    , uiText <$> _uiInput_error
    ]

uiInput
    :: MonadWidget t m
    => Dynamic t UiInput
    -> TextInputConfig t
    -> m (TextInput t)
uiInput iDyn c =
    elDynAttr "div" (mkAttrs <$> iDyn) $ do
      res <- textInput c
      _ <- dyn (loadingPart <$> iDyn)
      return res
  where
    mkAttrs i = "class" =: T.unwords ["ui", uiInputAttrs i, "input"]
    loadingPart i = maybe blank (\_ -> uiIcon "search" def >> blank) $ _uiInput_loading i

