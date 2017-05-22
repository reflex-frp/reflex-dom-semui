{-# LANGUAGE CPP                      #-}
{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE JavaScriptFFI            #-}
{-# LANGUAGE OverloadedStrings        #-}
{-# LANGUAGE TemplateHaskell          #-}
{-# LANGUAGE TypeFamilies             #-}

module Reflex.Dom.SemanticUI.Checkbox where

------------------------------------------------------------------------------
import           Control.Monad.Trans
import           Control.Lens (makeLenses)
import           Data.Default
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Text (Text)
import qualified Data.Text as T
import qualified GHCJS.DOM.Element as DOM
#ifdef ghcjs_HOST_OS
import GHCJS.DOM.Types (liftJSM, JSVal, pFromJSVal, JSM)
import GHCJS.Foreign.Callback (Callback, asyncCallback1)
#else
import GHCJS.DOM.Types (liftJSM, JSM, fromJSValUnchecked)
import Language.Javascript.JSaddle.Object (fun, js1, jsg1, jss, obj)
import Control.Lens.Operators ((^.))
import Control.Monad (void)
#endif
import           Reflex
import           Reflex.Dom.Core hiding (fromJSString)
------------------------------------------------------------------------------
import           Reflex.Dom.SemanticUI.Common (UiClassText(..))
------------------------------------------------------------------------------

-- | Given a div element, tell semantic-ui to convert it to a checkbox with the
-- given options. The callback function is called on change with the new state.
activateCheckbox :: DOM.Element -> (Bool -> JSM ()) -> JSM ()
#ifdef ghcjs_HOST_OS
activateCheckbox e onChange = do
  cb <- asyncCallback1 $ onChange . pFromJSVal
  js_activateCheckbox e cb
foreign import javascript unsafe
  "$($1).checkbox({ onChange: function() { \
    $2($($1).checkbox('is checked')); \
  } });"
  js_activateCheckbox :: DOM.Element -> Callback (JSVal -> JSM ()) -> JSM ()
#else
activateCheckbox e onChange = do
  o <- obj
  o ^. jss ("onChange"::Text) (fun $ \_ _ [t, _, _] ->
    onChange =<< fromJSValUnchecked t)
  void $ jsg1 ("$"::Text) e ^. js1 ("checkbox"::Text) o
#endif

-- | Given an initialised checkbox element, set the state to the given value.
-- The act of setting the state calls any callbacks, so the value stays
-- synchronised.
setCheckboxValue :: DOM.Element -> Bool -> JSM ()
setCheckboxValue e True = checkCheckbox e
setCheckboxValue e False = uncheckCheckbox e

#ifdef ghcjs_HOST_OS
foreign import javascript unsafe
  "$($1).checkbox('check');"
  checkCheckbox :: DOM.Element -> JSM ()
foreign import javascript unsafe
  "$($1).checkbox('uncheck');"
  uncheckCheckbox :: DOM.Element -> JSM ()
#else
checkCheckbox, uncheckCheckbox :: DOM.Element -> JSM ()
checkCheckbox e
  = void $ jsg1 ("$"::Text) e ^. js1 ("checkbox"::Text) ("check"::Text)
uncheckCheckbox e
  = void $ jsg1 ("$"::Text) e ^. js1 ("checkbox"::Text) ("uncheck"::Text)
#endif

--------------------------------------------------------------------------------

data CheckboxType =  CbSlider | CbToggle | CbFitted
  deriving Eq

-- | Convert an option to its class representation
instance UiClassText CheckboxType where
  uiText CbSlider = "slider"
  uiText CbToggle = "toggle"
  uiText CbFitted = "fitted"

data CheckboxConf t = CheckboxConf
  { _checkboxConf_initialValue :: Bool
  , _checkboxConf_setValue :: Event t Bool
  , _checkboxConf_attributes :: Map Text Text
  , _checkboxConf_divAttributes :: Map Text Text
  , _checkboxConf_type :: [CheckboxType]
  }

$(makeLenses ''CheckboxConf)

instance Reflex t => Default (CheckboxConf t) where
  def = CheckboxConf
    { _checkboxConf_initialValue = False
    , _checkboxConf_setValue = never
    , _checkboxConf_attributes = mempty
    , _checkboxConf_divAttributes = mempty
    , _checkboxConf_type = mempty
    }

instance HasAttributes (CheckboxConf t) where
  type Attrs (CheckboxConf t) = Map Text Text
  attributes = checkboxConf_attributes

instance HasSetValue (CheckboxConf t) where
  type SetValue (CheckboxConf t) = Event t Bool
  setValue = checkboxConf_setValue

--------------------------------------------------------------------------------

-- | Semantic UI checkbox, returning reflex-dom 'Checkbox' contents
uiCheckbox
  :: MonadWidget t m
  => m ()           -- ^ Label contents
  -> CheckboxConf t -- ^ Checkbox config
  -> m (Checkbox t)
uiCheckbox label config = fmap snd $ uiCheckbox' label config

-- | Semantic UI checkbox, returning element and reflex-dom 'Checkbox' contents
uiCheckbox'
  :: MonadWidget t m
  => m ()           -- ^ Label contents
  -> CheckboxConf t -- ^ Checkbox config
  -> m (El t, Checkbox t)
uiCheckbox' label config = do

  (cbEl, _) <- elAttr' "div" divAttrs $ do
    elAttr "input" attrs blank
    el "label" label

  -- Setup the event and callback function for when the value is changed
  (onChangeEvent, onChangeCallback) <- newTriggerEvent

  -- Activate the dropdown after build
  schedulePostBuild $ liftJSM $
    activateCheckbox (_element_raw cbEl) $ liftIO . onChangeCallback

  -- Allow the value to be set
  let setCbVal = setCheckboxValue (_element_raw cbEl)
  performEvent_ $ liftJSM . setCbVal <$> _checkboxConf_setValue config

  cb <- holdDyn (M.member "checked" attrs) onChangeEvent
  return (cbEl, Checkbox cb onChangeEvent)

  where
    attrs = M.insert "type" "checkbox" $ _checkboxConf_attributes config
    classes = T.unlines $ "ui checkbox" : map uiText (_checkboxConf_type config)
    alterClasses = maybe (Just classes) (\c -> Just $ T.unlines [classes, c])
    divAttrs = M.alter alterClasses "class" $ _checkboxConf_divAttributes config

