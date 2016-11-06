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

#include "foreign-compat.h"

module Reflex.Dom.SemanticUI.Modal where

------------------------------------------------------------------------------
import           Control.Monad.Trans
import           Data.Monoid
import           Data.Text (Text)
import           Reflex.Dom
------------------------------------------------------------------------------
import           GHCJS.Compat
------------------------------------------------------------------------------


-- Not used yet
--data UiModal = UiModal
--    { _uiModal_detachable        :: Bool
--    , _uiModal_autofocus         :: Bool
--    , _uiModal_observeChanges    :: Bool
--    , _uiModal_allowMultiple     :: Bool
--    , _uiModal_keyboardShortcuts :: Bool
--    , _uiModal_offset            :: Int
--    , _uiModal_context           :: Text
--    , _uiModal_closable          :: Bool
--    , _uiModal_transition        :: Text
--    , _uiModal_duration          :: Int
--    , _uiModal_queue             :: Bool
--    }
--
--instance Default UiModal where
--    def = UiModal True True False False True 0 "body" True "scale" 400 False

data ModalBehaviors
    = ShowModal
    | HideModal
    | ToggleModal
    | RefreshModal
    | ShowDimmer
    | HideDimmer
    | HideOthers
    | HideAll
    | CacheSizes
    | SetActive
  deriving (Eq,Ord,Enum)

modalBehaviorString :: ModalBehaviors -> Text
modalBehaviorString beh =
    case beh of
      ShowModal -> "show"
      HideModal -> "hide"
      ToggleModal -> "toggle"
      RefreshModal -> "refresh"
      ShowDimmer -> "show dimmer"
      HideDimmer -> "hide dimmer"
      HideOthers -> "hide others"
      HideAll -> "hide all"
      CacheSizes -> "cache sizes"
      SetActive -> "set active"

------------------------------------------------------------------------------
uiModal :: MonadWidget t m => Text -> Event t ModalBehaviors -> m a -> m a
uiModal elId beh children = do
    res <- elAttr "div" ("id" =: elId <> "class" =: "ui modal") children
    let doBehavior b = liftIO $ js_activateSemUiModal
                         (toJSString ("#"<>elId))
                         (toJSString $ modalBehaviorString b)
    performEvent (doBehavior <$> beh)
    return res

------------------------------------------------------------------------------
uiShowModal :: Text -> ModalBehaviors -> IO ()
uiShowModal sel beh = js_activateSemUiModal (toJSString sel)
                        (toJSString $ modalBehaviorString beh)

FOREIGN_IMPORT(unsafe, js_activateSemUiModal, JSString -> JSString -> IO (), "$($1).modal($2);")

