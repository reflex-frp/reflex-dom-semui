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

module Reflex.Dom.SemanticUI.Icon where

------------------------------------------------------------------------------
import           Data.Default
import           Data.Maybe
import           Data.Text (Text)
import qualified Data.Text as T
import           Reflex.Dom hiding (fromJSString)
------------------------------------------------------------------------------
import           Reflex.Dom.SemanticUI.Common
------------------------------------------------------------------------------

data UiIcon = UiIcon
    { _uiIcon_size       :: Maybe UiSize
    , _uiIcon_color      :: Maybe UiColor
    , _uiIcon_disabled   :: Maybe UiDisabled
    , _uiIcon_left       :: Maybe UiLeft
    , _uiIcon_loading    :: Maybe UiLoading
    , _uiIcon_fitted     :: Maybe UiFitted
    , _uiIcon_flipped    :: Maybe UiFlipped
    , _uiIcon_rotated    :: Maybe UiRotated
    , _uiIcon_circular   :: Maybe UiCircular
    , _uiIcon_bordered   :: Maybe UiBordered
    , _uiIcon_inverted   :: Maybe UiInverted
    } deriving (Eq,Show)

instance Default UiIcon where
  def = UiIcon def def def def def def def def def def def

instance UiHasSize UiIcon where
  uiSetSize s b = b { _uiIcon_size = Just s }

instance UiHasColor UiIcon where
  uiSetColor c b = b { _uiIcon_color = Just c }

instance UiHasDisabled UiIcon where
  disabled b = b { _uiIcon_disabled = Just UiDisabled }

instance UiHasLeft UiIcon where
  uiLeft b = b { _uiIcon_left = Just UiLeft }

instance UiHasLoading UiIcon where
  loading b = b { _uiIcon_loading = Just UiLoading }

instance UiHasFitted UiIcon where
  fitted b = b { _uiIcon_fitted = Just UiFitted }

instance UiHasFlipped UiIcon where
  uiSetFlipped s b = b { _uiIcon_flipped = Just s }

instance UiHasRotated UiIcon where
  uiSetRotated s b = b { _uiIcon_rotated = Just s }

instance UiHasCircular UiIcon where
  circular b = b { _uiIcon_circular = Just UiCircular }

instance UiHasBordered UiIcon where
  bordered b = b { _uiIcon_bordered = Just UiBordered }

instance UiHasInverted UiIcon where
  inverted b = b { _uiIcon_inverted = Just UiInverted }

uiIconAttrs :: UiIcon -> Text
uiIconAttrs UiIcon{..} = T.unwords $ catMaybes
    [ uiText <$> _uiIcon_size
    , uiText <$> _uiIcon_color
    , uiText <$> _uiIcon_disabled
    , uiText <$> _uiIcon_left
    , uiText <$> _uiIcon_loading
    , uiText <$> _uiIcon_fitted
    , uiText <$> _uiIcon_flipped
    , uiText <$> _uiIcon_rotated
    , uiText <$> _uiIcon_circular
    , uiText <$> _uiIcon_bordered
    , uiText <$> _uiIcon_inverted
    ]

uiIcon
    :: MonadWidget t m
    => Text
    -> Dynamic t UiIcon
    -> m (Event t ())
uiIcon ty iDyn = do
    (e,_) <- elDynAttr' "i" (mkAttrs <$> iDyn) blank
    return $ domEvent Click e
  where
    mkAttrs b = "class" =: T.unwords [ty, uiIconAttrs b, "icon"]

