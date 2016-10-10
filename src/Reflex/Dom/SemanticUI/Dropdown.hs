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

module Reflex.Dom.SemanticUI.Dropdown where

------------------------------------------------------------------------------
--import           Control.Lens
import           Control.Monad
import           Control.Monad.Trans
--import           Data.Dependent.Sum (DSum (..))
import qualified Data.List as L
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Monoid
import           Data.Text (Text)
import qualified Data.Text as T
import           GHCJS.DOM.HTMLElement (HTMLElement)
import           Reflex
--import           Reflex.Host.Class
import           Reflex.Dom hiding (fromJSString)
------------------------------------------------------------------------------
import           GHCJS.Compat
import           Reflex.Dom.SemanticUI.Common (tshow)
------------------------------------------------------------------------------


------------------------------------------------------------------------------
activateSemUiDropdown :: Text -> IO ()
activateSemUiDropdown = js_activateSemUiDropdown . toJSString

FOREIGN_IMPORT(unsafe, js_activateSemUiDropdown, JSString -> IO (), "$($1).dropdown({fullTextSearch: true});")

activateSemUiDropdownEl :: HTMLElement -> IO ()
activateSemUiDropdownEl = js_activateSemUiDropdownEl . unHTMLElement

FOREIGN_IMPORT(unsafe, js_activateSemUiDropdownEl, JSVal -> IO (), "$($1).dropdown({fullTextSearch: true});")


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
    let act cb = liftIO $ do
          jscb <- asyncCallback3 $ \_ t _ -> liftIO $
              cb $ read $ fromJSString $ pFromJSVal t
          js_activateSemUiDropdownMulti
            (toJSString $ _dmc_elementId dmc) jscb
            (toJSBool $ _dmc_fullTextSearch dmc)
    e <- performEventAsync (act <$ pb)
    val <- holdDyn (_dmc_initialValue dmc) e
    return $! DropdownMulti val
    -- I think the above is the new reflex implementation of the below, but
    -- haven't tested it yet.

    --postGui <- askPostGui
    --runWithActions <- askRunWithActions
    --e <- newEventWithTrigger $ \et -> do
    --       cb <- asyncCallback3 $ \_ t _ -> liftIO $ do
    --           let v = read $ fromJSString $ pFromJSVal t
    --           postGui $ runWithActions [et :=> Identity v]
    --       js_activateSemUiDropdownMulti
    --         (toJSString $ _dmc_elementId dmc) cb
    --         (toJSBool $ _dmc_fullTextSearch dmc)
    --       return (return ())
    --       -- TODO Probably need some kind of unsubscribe mechanism
    --       --return $ liftIO unsubscribe
    --val <- holdDyn (_dmc_initialValue dmc) e
    --return $! DropdownMulti val

FOREIGN_IMPORT(unsafe, js_activateSemUiDropdownMulti, JSString -> Callback (JSVal -> JSVal -> JSVal -> IO ()) -> JSVal -> IO (), "(function(){ $($1).dropdown({onChange: $2, fullTextSearch: $3}); })()")

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
    performEvent_ (liftIO (activateSemUiDropdown (T.cons '#' elId)) <$ pb)
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
    performEvent_ (liftIO (activateSemUiDropdown (T.cons '#' elId)) <$ pb)
    return $ value d


-- | Custom Dropdown item configuration
data DropdownItemConfig m = DropdownItemConfig
  { dropdownItemConfig_dataText :: T.Text
    -- ^ dataText (shown for the selected item)
  , dropdownItemConfig_internal :: m ()
    -- ^ Procedure for drawing the DOM contents of the menu item
    --   (we produce the menu item div for you, so it' enough to
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
  performEvent_ (liftIO (activateSemUiDropdownEl $ _element_raw elDD) <$ pb)
  holdDyn iv (elChoice)
