{-# LANGUAGE CPP                      #-}
{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE JavaScriptFFI            #-}
{-# LANGUAGE OverloadedStrings        #-}
{-# LANGUAGE RankNTypes               #-}
{-# LANGUAGE TemplateHaskell          #-}
{-# LANGUAGE TypeFamilies             #-}

module Reflex.Dom.SemanticUI.RadioGroup where

------------------------------------------------------------------------------
import           Control.Monad.Trans
import           Control.Lens (makeLenses)
import           Data.Default
import           Data.Functor (($>))
import qualified Data.List as L
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Maybe (isJust)
import           Data.Monoid ((<>))
import           Data.Text (Text)
import qualified Data.Text as T
import qualified GHCJS.DOM.Element as DOM
#ifdef ghcjs_HOST_OS
import Control.Monad ((<=<))
import GHCJS.DOM.Types (liftJSM, JSVal, pFromJSVal, pToJSVal, toJSVal, JSM)
import GHCJS.Foreign.Callback (Callback, asyncCallback1)
import Text.Read (readMaybe)
#else
import Control.Monad (void)
import GHCJS.DOM.Types (liftJSM, JSM, fromJSValUnchecked)
import Language.Javascript.JSaddle.Object (fun, js0, js1, js2, jsg1)
import Control.Lens.Operators ((^.))
#endif
import           Reflex
import           Reflex.Dom hiding (fromJSString)
------------------------------------------------------------------------------
import           Reflex.Dom.SemanticUI.Checkbox
import           Reflex.Dom.SemanticUI.Common
------------------------------------------------------------------------------


-- | Activate a dropdown element with Semantic UI. No callbacks by semantic ui
-- because they don't notify when a radio is automatically de-selected, so
-- instead we manually put on change listeners to the individual radio items.
activateRadio :: DOM.Element -> JSM ()
#ifdef ghcjs_HOST_OS
activateRadio = js_activateRadio
foreign import javascript unsafe
  "$($1).checkbox();"
  js_activateRadio :: DOM.Element -> JSM ()
#else
activateRadio e =
  void $ jsg1 ("$"::Text) e ^. js0 ("dropdown"::Text)
#endif

-- | Given a list of radio checkboxes, setup onChange callbacks
setRadioCallbacks :: [DOM.Element] -> (Maybe Int -> JSM ()) -> JSM ()
#ifdef ghcjs_HOST_OS
setRadioCallbacks es f = do
  cb <- asyncCallback1 $ f . (\x -> readMaybe =<< pFromJSVal x)
  els <- toJSVal es
  js_setRadioCallbacks els cb
foreign import javascript unsafe
  "$($1).on('change', function() { $2($($1).filter(':checked').val()); });"
  js_setRadioCallbacks :: JSVal -> Callback (JSVal -> JSM ()) -> JSM ()
#else
setRadioCallbacks es onChange = do
  checked <- jsg1 ("$"::Text) es
          ^. js1 ("filter"::Text) (":checked"::Text)
          ^. js0 ("val"::Text)
  let cb = fun $ \_ _ [] -> onChange =<< fromJSValUnchecked checked
  void $ jsg1 ("$"::Text) es ^. js2 ("on"::Text) ("change"::Text) cb
#endif

-- | Set the current value of a radio group.
setRadioGroup :: [DOM.Element] -> Maybe Int -> JSM (Maybe Int)
#ifdef ghcjs_HOST_OS
setRadioGroup es mval = do
  els <- toJSVal es
  case pToJSVal <$> mval of
    Nothing -> js_clearRadioGroup els *> return Nothing
    Just val -> (readMaybe <=< pFromJSVal) <$> js_setRadioGroup els val
foreign import javascript unsafe
  "$($1).prop('checked', false);"
  js_clearRadioGroup :: JSVal -> JSM ()
foreign import javascript unsafe
  "$($1).filter('[value=' + $2 + ']').prop('checked', true);\
   $r = $($1).filter(':checked').val();"
  js_setRadioGroup :: JSVal -> JSVal -> JSM JSVal
#else
setRadioGroup es Nothing =
  Nothing <$ jsg1 ("$"::Text) es ^. js2 ("prop"::Text) ("checked"::Text) False
setRadioGroup es (Just val) = do
  jsg1 ("$"::Text) es
    ^. js1 ("filter"::Text) ("[value=" <> tshow val <> "]"::Text)
    ^. js2 ("prop"::Text) ("checked"::Text) True
  selected <- jsg1 ("$"::Text) es
    ^. js1 ("filter"::Text) (":checked"::Text)
    ^. js0 ("val"::Text)
  fromJSValUnchecked selected
#endif

------------------------------------------------------------------------------

-- | Holds the config of individual radio items
data RadioItemConfig t m = RadioItemConfig
  { _radioItemConfig_label :: Dynamic t (m ()) -- ^ label rendering
  , _radioItemConfig_attributes :: Map Text Text
  , _radioItemConfig_divAttributes :: Map Text Text
  }

$(makeLenses ''RadioItemConfig)

instance HasSetValue (RadioItemConfig t m) where
  type SetValue (RadioItemConfig t m) = Dynamic t (m ())
  setValue = radioItemConfig_label

instance HasAttributes (RadioItemConfig t m) where
  type Attrs (RadioItemConfig t m) = Map Text Text
  attributes = radioItemConfig_attributes

instance MonadWidget t m => Default (RadioItemConfig t m) where
  def = RadioItemConfig
    { _radioItemConfig_label = constDyn blank
    , _radioItemConfig_attributes = mempty
    , _radioItemConfig_divAttributes = mempty
    }

data RadioGroupConfig t m a = RadioGroupConfig
  { _radioGroupConfig_initialValue :: Maybe a
  , _radioGroupConfig_setValue :: Event t (Maybe a)
  , _radioGroupConfig_type :: [CheckboxType]
  , _radioGroupConfig_wrapper :: forall b. m b -> m b
  }

$(makeLenses ''RadioGroupConfig)

instance HasSetValue (RadioGroupConfig t m a) where
  type SetValue (RadioGroupConfig t m a) = Event t (Maybe a)
  setValue = radioGroupConfig_setValue

instance MonadWidget t m => Default (RadioGroupConfig t m a) where
  def = RadioGroupConfig
    { _radioGroupConfig_initialValue = Nothing
    , _radioGroupConfig_setValue = never
    , _radioGroupConfig_type = mempty
    , _radioGroupConfig_wrapper = divClass "field"
    }

-- | Create a group of radio checkboxes from the given list of items. The name
-- is required to link the individual checkboxes together. It must be unique to
-- the field.
radioGroup
  :: (Eq a, MonadWidget t m)
  => Text                       -- ^ Name
  -> [(a, RadioItemConfig t m)] -- ^ Item tuples: (selected type, item config)
  -> RadioGroupConfig t m a     -- ^ Config
  -> m (Dynamic t (Maybe a))
radioGroup name items config = do

  -- Insert all of the items, collecting the raw elements and wrapping them with
  -- the given wrapper function
  inputEls <- traverse wrap . imap (putRadioItem name classes) $ map snd items

  -- Helper to lookup the index of an items type
  let getIndex v = L.findIndex ((==) v . fst) items

  -- Event performed when user fires a set value event. Looks up the value
  -- index, and sets the value in DOM through js.
  onSetEvent <- performEvent $ liftJSM . setRadioGroup inputEls . (>>= getIndex)
                            <$> _radioGroupConfig_setValue config

  -- Set initial value
  pb <- getPostBuild
  setInitialEvent <- performEvent $ pb $> liftJSM
    (setRadioGroup inputEls $ getIndex
      =<< _radioGroupConfig_initialValue config)

  -- On change callbacks
  (onChangeEvent, onChangeCallback) <- newTriggerEvent
  schedulePostBuild $ liftJSM $ setRadioCallbacks inputEls $
    liftIO . onChangeCallback

  index <- holdDyn Nothing $ leftmost [onChangeEvent, onSetEvent, setInitialEvent]
  return $ (\i -> fmap fst $ (items !?) =<< i) <$> index

  where
    wrap = _radioGroupConfig_wrapper config
    cbType = _radioGroupConfig_type config
    hasRadio = if isToggleOrSlider cbType then [] else ["radio"]
    classes = T.unlines $ "ui checkbox" : hasRadio ++ map uiText cbType
    -- Detect clashing classes: toggle and slider take precedence over radio
    isToggleOrSlider types = isJust $
      L.find (\i -> i == CbToggle || i == CbSlider) types

-- | Make an individual radio checkbox item.
putRadioItem
  :: MonadWidget t m
  => Text                 -- ^ HTML name attribute
  -> Text                 -- ^ Classes for the enclosing div element
  -> Int                  -- ^ Value of item
  -> RadioItemConfig t m  -- ^ Item configuration
  -> m DOM.Element
putRadioItem name classes i (RadioItemConfig label attrs' divAttrs') = do
  (cbEl, inputEl) <- elAttr' "div" divAttrs $ do
    (inputEl, _) <- elAttr' "input" attrs blank
    el "label" $ dyn label
    return inputEl
  -- Setup checkbox with semantic ui
  schedulePostBuild $ liftJSM $ activateRadio $ _element_raw cbEl

  return $ _element_raw inputEl

  where
    attrs = "type" =: "radio" <> "value" =: tshow i <> "name" =: name <> attrs'
    divAttrs = M.alter alterClasses "class" divAttrs'
    alterClasses = maybe (Just classes) (\c -> Just $ T.unlines [classes, c])

