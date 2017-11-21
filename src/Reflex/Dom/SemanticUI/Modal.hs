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

module Reflex.Dom.SemanticUI.Modal where

------------------------------------------------------------------------------
import           Control.Monad.Trans
import           Data.Text (Text)
import qualified GHCJS.DOM.Types as DOM
#ifndef ghcjs_HOST_OS
import           Control.Monad (void)
import           Control.Lens.Operators ((^.))
import           Language.Javascript.JSaddle.Object (js1, jsg1)
#endif
import           Reflex.Dom.Core
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

data ModalBehavior
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

modalBehaviorString :: ModalBehavior -> Text
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
uiModal :: MonadWidget t m => Event t ModalBehavior -> m a -> m a
uiModal beh children = do
    (e,res) <- elAttr' "div" ("class" =: "ui modal") children
    performEvent (DOM.liftJSM . uiTriggerModalAction (_element_raw e) <$> beh)
    return res

------------------------------------------------------------------------------
uiTriggerModalAction :: DOM.Element -> ModalBehavior -> DOM.JSM ()
uiTriggerModalAction e beh = js_modalAction e
                        (DOM.toJSString $ modalBehaviorString beh)

#ifdef ghcjs_HOST_OS
foreign import javascript unsafe "jQuery($1)['modal']($2);"
    js_modalAction :: DOM.Element -> DOM.JSString -> IO ()
#else
js_modalAction :: DOM.Element -> DOM.JSString -> DOM.JSM ()
js_modalAction e beh =
  void $ jsg1 ("$"::Text) e ^. js1 ("modal"::Text) beh
#endif

