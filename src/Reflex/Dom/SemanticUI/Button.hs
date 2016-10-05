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

module Reflex.Dom.SemanticUI.Button where

------------------------------------------------------------------------------
import           Control.Monad
import           Control.Monad.Trans
import           Data.Default
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Maybe
import           Data.Monoid
import           Data.Text (Text)
import qualified Data.Text as T
import           GHCJS.DOM.Types hiding (Event, Text)
#ifdef ghcjs_HOST_OS
import           GHCJS.Foreign.Callback
import           GHCJS.Foreign
import           GHCJS.Marshal.Internal
import           GHCJS.Types
#endif
import           Reflex
--import           Reflex.Host.Class
import           Reflex.Dom hiding (fromJSString)
------------------------------------------------------------------------------
import           Reflex.Dom.SemanticUI.Common
------------------------------------------------------------------------------

data UiButton = UiButton
    { _uiButton_emphasis :: Maybe UiEmphasis
    , _uiButton_color    :: Maybe UiColor
    , _uiButton_basic    :: Maybe UiBasic
    , _uiButton_inverted :: Maybe UiInverted
    } deriving (Eq,Show)

instance Default UiButton where
  def = UiButton def def def def

instance UiHasColor UiButton where
  uiSetColor c b = b { _uiButton_color = Just c }

instance UiHasEmphasis UiButton where
  uiSetEmphasis e b = b { _uiButton_emphasis = Just e }

instance UiHasBasic UiButton where
  basic b = b { _uiButton_basic = Just UiBasic }

instance UiHasInverted UiButton where
  inverted b = b { _uiButton_inverted = Just UiInverted }

uiButton :: MonadWidget t m => UiButton -> m a -> m a
uiButton UiButton{..} children = do
    elClass "button" (T.unwords ["ui", attrs, "button"]) children
  where
    attrs = T.unwords $ catMaybes
              [ uiText <$> _uiButton_emphasis
              , uiText <$> _uiButton_color
              , uiText <$> _uiButton_basic
              , uiText <$> _uiButton_inverted
              ]
