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
{-# LANGUAGE TemplateHaskell          #-}

module Reflex.Dom.SemanticUI.Dropdown where

------------------------------------------------------------------------------
import           Control.Monad
import           Control.Monad.Trans
import           Control.Lens (makeLenses)
import           Data.Default
import qualified Data.List as L
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Maybe (catMaybes, maybeToList)
import           Data.Monoid
import           Data.Text (Text)
import qualified Data.Text as T
import qualified GHCJS.DOM.Element as DOM
#ifdef ghcjs_HOST_OS
import GHCJS.DOM.Types
       (liftJSM, JSString, JSVal, toJSString, fromJSString, pFromJSVal,
        pToJSVal, toJSVal, JSM, fromJSValUnchecked)
import GHCJS.Foreign.Callback (Callback, asyncCallback1, asyncCallback3)
#else
import GHCJS.DOM.Types
       (liftJSM, JSString, toJSString, JSM, fromJSValUnchecked)
import Language.Javascript.JSaddle.Object
       (fun, js1, js2, jsg1, jss, obj)
import Control.Lens.Operators ((^.))
#endif
import           Reflex
import           Reflex.Dom hiding (fromJSString)
import           Text.Read (readMaybe)
------------------------------------------------------------------------------
import           Reflex.Dom.SemanticUI.Common (tshow)
------------------------------------------------------------------------------


enumItemMap :: (Show a, Enum a) => a -> a -> [(a, Text)]
enumItemMap from to = map (\a -> (a, T.pack $ show a)) [from..to]

------------------------------------------------------------------------------
activateSemUiDropdown :: Text -> JSM ()
#ifdef ghcjs_HOST_OS
activateSemUiDropdown = js_activateSemUiDropdown . toJSString

foreign import javascript unsafe
  "$($1).dropdown({fullTextSearch: true});"
  js_activateSemUiDropdown :: JSString -> JSM ()
#else
activateSemUiDropdown name = do
  o <- obj
  o ^. jss ("fullTextSearch"::Text) True
  void $ jsg1 ("$"::Text) name ^. js1 ("dropdown"::Text) o
#endif

#ifdef ghcjs_HOST_OS
foreign import javascript unsafe
  "$($1).dropdown({fullTextSearch: true});"
  activateSemUiDropdownEl :: DOM.Element -> JSM ()
#else
activateSemUiDropdownEl :: DOM.Element -> JSM ()
activateSemUiDropdownEl e = do
  o <- obj
  o ^. jss ("fullTextSearch"::Text) True
  void $ jsg1 ("$"::Text) e ^. js1 ("dropdown"::Text) o
#endif

data DropdownMulti t a = DropdownMulti
    { _dm_value :: Dynamic t a
    }

data DropdownMultiConfig a = DropdownMultiConfig
    { _dmc_initialValue :: a
    , _dmc_fullTextSearch :: Bool
    , _dmc_elementId :: Text
    }

------------------------------------------------------------------------------
activateSemUiDropdownMulti
    :: (MonadWidget t m, Read a)
    => DropdownMultiConfig a
    -> m (DropdownMulti t a)
activateSemUiDropdownMulti dmc = do
    pb <- getPostBuild
    let act cb = liftJSM $
          activateSemUiDropdownMulti'
            (toJSString $ _dmc_elementId dmc)
            (liftIO . cb . read)
            (_dmc_fullTextSearch dmc)
    e <- performEventAsync (act <$ pb)
    val <- holdDyn (_dmc_initialValue dmc) e
    return $! DropdownMulti val

#ifdef ghcjs_HOST_OS
activateSemUiDropdownMulti' :: JSString -> (String -> JSM ()) -> Bool -> JSM ()
activateSemUiDropdownMulti' name onChange full = do
  jscb <- asyncCallback3 $ \_ t _ -> liftIO $
    onChange $ fromJSString $ pFromJSVal t
  js_activateSemUiDropdownMulti name jscb full

foreign import javascript unsafe
  "(function(){ $($1).dropdown({onChange: $2, fullTextSearch: $3}); })()"
  js_activateSemUiDropdownMulti
    :: JSString
    -> Callback (JSVal -> JSVal -> JSVal -> JSM ())
    -> Bool
    -> JSM ()
#else
activateSemUiDropdownMulti' :: JSString -> (String -> JSM ()) -> Bool -> JSM ()
activateSemUiDropdownMulti' name onChange full = do
  o <- obj
  o ^. jss ("onChange"::Text) (fun $ \_ _ [_, t, _] -> onChange =<< fromJSValUnchecked t)
  o ^. jss ("fullTextSearch"::Text) full
  void $ jsg1 ("$"::Text) name ^. js1 ("dropdown"::Text) o
#endif

-- Multi-select sem-ui dropdown is not working properly yet.  Not sure how
-- to get the current value.
--
-- $('#dropdownId').dropdown('get value')
-- $('#dropdownId').onChange(value, text, $choice)

-- | Wrapper around the reflex-dom dropdown that calls the sem-ui dropdown
-- function after the element is built.
semUiDropdownMulti
    :: (MonadWidget t m, Show a)
    => Text
       -- ^ Element id.  Ideally this should be randomly generated instead
       -- of passed in as an argument, but for now this approach is easier.
    -> a
       -- ^ Initial value
    -> Dynamic t (Map a Text)
    -> Map Text Text
    -> m (Dynamic t Text)
semUiDropdownMulti elId iv vals attrs = do
    let f vs = semUiDropdownMulti' elId iv vs attrs
    res <- dyn $ fmap f vals
    join <$> holdDyn (constDyn $ tshow iv) res

-- | Wrapper around the reflex-dom dropdown that calls the sem-ui dropdown
-- function after the element is built.
semUiDropdownMulti'
    :: (MonadWidget t m, Show a)
    => Text
       -- ^ Element id.  Ideally this should be randomly generated instead
       -- of passed in as an argument, but for now this approach is easier.
    -> a
       -- ^ Initial value
    -> Map a Text
    -> Map Text Text
    -> m (Dynamic t Text)
semUiDropdownMulti' elId iv vals attrs = do
    d <- dropdown (tshow iv) (constDyn $ M.mapKeys tshow vals) $ def &
      attributes .~ (constDyn $ attrs <> ("id" =: elId))
    pb <- getPostBuild
    performEvent_ (liftJSM (activateSemUiDropdown (T.cons '#' elId)) <$ pb)
    return $ value d

-- | Wrapper around the reflex-dom dropdown that calls the sem-ui dropdown
-- function after the element is built.
semUiDropdown
    :: (MonadWidget t m, Ord a)
    => Text
       -- ^ Element id.  Ideally this should be randomly generated instead
       -- of passed in as an argument, but for now this approach is easier.
    -> a
       -- ^ Initial value
    -> Dynamic t (Map a Text)
    -> Map Text Text
    -> m (Dynamic t a)
semUiDropdown elId iv vals attrs = do
    let f vs = semUiDropdown' elId iv vs attrs
    res <- dyn $ fmap f vals
    join <$> holdDyn (constDyn iv) res

-- | Wrapper around the reflex-dom dropdown that calls the sem-ui dropdown
-- function after the element is built.
semUiDropdown'
    :: (MonadWidget t m, Ord a)
    => Text
       -- ^ Element id.  Ideally this should be randomly generated instead
       -- of passed in as an argument, but for now this approach is easier.
    -> a
       -- ^ Initial value
    -> Map a Text
    -> Map Text Text
    -> m (Dynamic t a)
semUiDropdown' elId iv vals attrs = do
    d <- dropdown iv (constDyn vals) $ def &
      attributes .~ (constDyn $ attrs <> ("id" =: elId))
    pb <- getPostBuild
    performEvent_ (liftJSM (activateSemUiDropdown (T.cons '#' elId)) <$ pb)
    return $ value d


-- | Custom Dropdown item configuration
data DropdownItemConfig m = DropdownItemConfig
  { dropdownItemConfig_dataText :: T.Text
    -- ^ dataText (shown for the selected item)
  , dropdownItemConfig_internal :: m ()
    -- ^ Procedure for drawing the DOM contents of the menu item
    --   (we produce the menu item div for you, so it's enough to
    --    use something simple here, e.g. `text "Friends"`
  }

-- | Dropdowns make have these additional properties
data DropdownOptFlag =
    DOFFluid
     -- ^ More flexible dropdown width, won't line break items
  | DOFSearch
    -- ^ Make menu items are searchable
  | DOFSelection
    -- ^ Dropdown is a selection among alternatives
  deriving (Eq, Enum, Show)

-- Helper function to build class attribute for dropdown
dropdownClass :: [DropdownOptFlag] -> T.Text
dropdownClass opts = T.unwords $ "ui" : (flags ++ ["dropdown"])
  where flags = map (T.toLower . T.drop 3 . tshow) $ L.sortOn fromEnum opts



-- | Dropdown with customizable menu items
semUiDropdownWithItems
  :: forall t m a.(MonadWidget t m, Ord a)
  => Text
     -- ^ Element id.  Ideally this should be randomly generated instead
     -- of passed in as an argument, but for now this approach is easier.
  -> [DropdownOptFlag]  -- TODO: DOFSearch eems broken
  -> a -- ^ Initial value
  -> Dynamic t (Map a (DropdownItemConfig m))
     -- ^ Map of items' values and renderings
  -> Map Text Text
     -- ^ Dropown attributes
  -> m (Dynamic t a)
semUiDropdownWithItems elId opts iv vals attrs = do
  (elDD, elChoice) <- elAttr' "div" ("id" =: elId <>
                            "class" =: dropdownClass opts <> attrs) $ do
    divClass "text" $ dynText (maybe "Menu" dropdownItemConfig_dataText .
                               M.lookup iv <$> vals)
    elAttr "i" ("class" =: "dropdown icon") blank

    divClass "menu" $ do
      sel <- listWithKey vals $ \k ddi -> do
        let (eAttrs :: Dynamic t (Map T.Text T.Text)) =
              ffor ddi $ \(DropdownItemConfig t _) ->
                           ("class" =: "item" <> "data-text" =: t)
            internal = dropdownItemConfig_internal <$> ddi :: Dynamic t (m ())
        e <- elDynAttr' "div" eAttrs $ dyn internal
        return (k <$ domEvent Click (fst e))
      -- return $ (join . fmap fst . M.minView) <$> joinDynThroughMap sel
      return $ switchPromptlyDyn $ leftmost . M.elems <$> sel

  pb <- getPostBuild
  performEvent_ (liftJSM (activateSemUiDropdownEl $ _element_raw elDD) <$ pb)
  holdDyn iv (elChoice)

------------------------------------------------------------------------------
-- New implementation

#ifdef ghcjs_HOST_OS
activateDropdown :: DOM.Element -> (Text -> JSM ()) -> JSM ()
activateDropdown e onChange = do
  cb <- asyncCallback1 $ onChange . pFromJSVal
  js_activateDropdown e cb
foreign import javascript unsafe
  "$($1).dropdown({ forceSelection : false \
                  , onChange: function(value){ $2(value); } \
                  , fullTextSearch: true });"
  js_activateDropdown :: DOM.Element -> Callback (JSVal -> JSM ()) -> JSM ()
#else
activateDropdown :: DOM.Element -> (Text -> JSM ()) -> JSM ()
activateDropdown e onChange = do
  o <- obj
  o ^. jss ("forceSelection"::Text) False
  o ^. jss ("onChange"::Text) (fun $ \_ _ [t, _, _] ->
    onChange =<< fromJSValUnchecked t)
  o ^. jss ("fullTextSearch"::Text) True
  void $ jsg1 ("$"::Text) e ^. js1 ("dropdown"::Text) o
#endif

#ifdef ghcjs_HOST_OS
dropdownSetExactly :: DOM.Element -> [Int] -> JSM ()
dropdownSetExactly e is = do
  jsVal <- toJSVal $ map tshow is
  js_dropdownSetExactly e jsVal

foreign import javascript unsafe
  "$($1).dropdown('set exactly', $2);"
  js_dropdownSetExactly :: DOM.Element -> JSVal -> JSM ()
#else
dropdownSetExactly :: DOM.Element -> [Int] -> JSM ()
dropdownSetExactly e is =
  void $ jsg1 ("$"::Text) e ^. js2 ("dropdown"::Text) ("set exactly"::Text) is
#endif

------------------------------------------------------------------------------

-- | Config for new semantic dropdowns
data DropdownConf t a = DropdownConf
  { _dropdownConf_initialValue :: a
  , _dropdownConf_setValue :: Event t a
  , _dropdownConf_attributes :: Map Text Text
  , _dropdownConf_placeholder :: Text
  }

$(makeLenses ''DropdownConf)

instance (Reflex t) => Default (DropdownConf t (Maybe a)) where
  def = DropdownConf
    { _dropdownConf_initialValue = Nothing
    , _dropdownConf_setValue = never
    , _dropdownConf_attributes = mempty
    , _dropdownConf_placeholder = mempty
    }

instance (Reflex t) => Default (DropdownConf t [a]) where
  def = DropdownConf
    { _dropdownConf_initialValue = mempty
    , _dropdownConf_setValue = never
    , _dropdownConf_attributes = mempty
    , _dropdownConf_placeholder = mempty
    }

instance HasAttributes (DropdownConf t a) where
  type Attrs (DropdownConf t a) = Map Text Text
  attributes = dropdownConf_attributes

instance HasSetValue (DropdownConf t a) where
  type SetValue (DropdownConf t a) = Event t a
  setValue = dropdownConf_setValue

-- | Helper function
indexToItem :: [(a, DropdownItemConfig m)] -> Text -> Maybe a
indexToItem items i' = do
  i <- readMaybe $ T.unpack i'
  fst <$> items !? i

-- | Safe indexing into lists
(!?) :: [a] -> Int -> Maybe a
[] !? _ = Nothing
(x:_) !? 0 = Just x
(_:xs) !? n = xs !? (n - 1)

-- | Semantic-UI dropdown with static items
semUiDropdownNew
  :: (MonadWidget t m, Eq a)
  => [(a, DropdownItemConfig m)] -- ^ Items
  -> [DropdownOptFlag]                -- ^ Options
  -> DropdownConf t (Maybe a)         -- ^ Dropdown config
  -> m (Dynamic t (Maybe a))
semUiDropdownNew items options config = do
  (divEl, evt) <- dropdownInternal items options False
    (_dropdownConf_placeholder config) (_dropdownConf_attributes config)
  let getIndex v = L.findIndex ((==) v . fst) items
      setDropdown = dropdownSetExactly (_element_raw divEl)

  -- setValue events
  performEvent_ $ liftJSM . setDropdown . maybeToList . (>>= getIndex)
               <$> _dropdownConf_setValue config

  -- Set initial value
  pb <- getPostBuild
  performEvent $
    liftJSM (setDropdown $ maybeToList $ getIndex
      =<< _dropdownConf_initialValue config) <$ pb

  holdDyn Nothing $ indexToItem items <$> evt

-- | Semantic-UI dropdown with multiple static items
semUiDropdownMultiNew
  :: (MonadWidget t m, Eq a)
  => [(a, DropdownItemConfig m)] -- ^ Items
  -> [DropdownOptFlag]                -- ^ Options
  -> DropdownConf t [a]               -- ^ Dropdown config
  -> m (Dynamic t [a])
semUiDropdownMultiNew items options config = do
  (divEl, evt) <- dropdownInternal items options True
    (_dropdownConf_placeholder config) (_dropdownConf_attributes config)

  let getIndices vs = L.findIndices ((`elem` vs) . fst) items
      setDropdown = dropdownSetExactly (_element_raw divEl)

  -- setValue events
  performEvent_ $ liftJSM . setDropdown . getIndices
               <$> _dropdownConf_setValue config

  -- Set initial value
  pb <- getPostBuild
  performEvent $
    liftJSM (setDropdown . getIndices $
      _dropdownConf_initialValue config) <$ pb

  holdDyn [] $ catMaybes . map (indexToItem items) . T.splitOn "," <$> evt

-- | Internal function with shared behaviour
dropdownInternal
  :: (MonadWidget t m, Eq a)
  => [(a, DropdownItemConfig m)] -- ^ Items
  -> [DropdownOptFlag]                -- ^ Options
  -> Bool                             -- ^ Is multiple dropdown
  -> Text                             -- ^ Placeholder
  -> Map Text Text                    -- ^ Dropdown div attributes
  -> m (El t, Event t Text)
dropdownInternal items options isMulti placeholder attrs = do

  let classes = dropdownClass options <> if isMulti then " multiple" else ""
  (divEl, _) <- elAttr' "div" ("class" =: classes <> attrs) $ do

    -- This holds the placeholder. Initial value must be set by js function in
    -- wrapper.
    divClass "default text" $ text $ placeholder
    elAttr "i" ("class" =: "dropdown icon") blank

    -- Dropdown menu
    let itemDiv n a = elAttr "div"
          ("class" =: "item" <> "data-value" =: tshow n <> a)
        putItem n (_, conf) = n + 1 <$ case conf of
          DropdownItemConfig "" m -> itemDiv n mempty m
          DropdownItemConfig t m -> itemDiv n ("data-text" =: t) m
    divClass "menu" $ foldM_ putItem (0 :: Int) items

  -- Setup the event and callback function for when the value is changed
  (onChangeEvent, onChangeCallback) <- newTriggerEvent

  -- Activate the dropdown after element is built
  schedulePostBuild $ liftJSM $
    activateDropdown (_element_raw divEl) $ liftIO . onChangeCallback

  return (divEl, onChangeEvent)

