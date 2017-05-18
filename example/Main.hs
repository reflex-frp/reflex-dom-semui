{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE RecursiveDo       #-}

module Main (main) where

import Control.Lens
import Control.Monad (void)
import Data.Map (Map, fromList)
import Data.Monoid ((<>))
import Data.Text (Text)
import qualified Data.Text as T
import Reflex.Dom
import Reflex.Dom.SemanticUI
import Reflex.Dom.Internal () -- TODO remove this once we solve orphan instance issue

import StateEnum
import CountryEnum

-- | Contacts
data ContactEnum
  = Jenny | Elliot | Stevie | Christian | Matt | Justen
  deriving (Bounded, Enum, Eq, Ord, Read, Show)

showContact :: ContactEnum -> Text
showContact Jenny = "Jenny Hess"
showContact Elliot = "Elliot Fu"
showContact Stevie = "Stevie Feliciano"
showContact Christian = "Christian"
showContact Matt = "Matt"
showContact Justen = "Justen Kitsune"

renderContact :: MonadWidget t m => ContactEnum -> m ()
renderContact contact = do
  elAttr "img" ("class" =: "ui mini avatar image"
            <> "src" =: ("http://semantic-ui.com/images/avatar/small/"
            <> T.toLower (tshow contact) <> ".jpg")) blank
  text $ showContact contact

-- | Cards
data CardEnum = Visa | Amex | Discover
  deriving (Bounded, Enum, Eq, Ord, Read, Show)

showCard :: CardEnum -> Text
showCard Visa = "Visa"
showCard Amex = "American Express"
showCard Discover = "Discover"

renderCard :: MonadWidget t m => CardEnum -> m ()
renderCard card = do
  elClass "i" (T.toLower (tshow card) <> " icon") blank
  text $ showCard card

checkboxes :: MonadWidget t m => m ()
checkboxes = do

  resetEvent <- divClass "ui top attached segment" $ do
    elClass "h4" "ui header" $ do
      text "Checkboxes"
      uiButton (rightFloated . mini . compact . basic <$> def) $ text "Reset"

  divClass "ui bottom attached segment form" $ do
    divClass "two fields" $ do

      divClass "field" $ do
        el "label" $ text "Checkboxes with labels"
        divClass "ui compact segment" $ do
          c1 <- uiCheckbox (text "Normal checkbox") $
            def & setValue .~ (False <$ resetEvent)
          divClass "ui left pointing label" $ display $ value c1
        divClass "ui compact segment" $ do
          c2 <- uiCheckbox (text "Toggle checkbox") $
            def & checkboxConf_type .~ [CbToggle]
                & setValue .~ (False <$ resetEvent)
          divClass "ui left pointing label" $ display $ value c2
        divClass "ui compact segment" $ do
          c3 <- uiCheckbox (text "Slider checkbox") $
            def & checkboxConf_type .~ [CbSlider]
                & setValue .~ (False <$ resetEvent)
          divClass "ui left pointing label" $ display $ value c3

      void $ divClass "field" $ do
        el "label" $ text "Fitted checkboxes"
        divClass "ui compact segment" $ do
          uiCheckbox blank $
            def & checkboxConf_type .~ [CbFitted]
                & setValue .~ (False <$ resetEvent)
        divClass "ui compact segment" $ do
          uiCheckbox blank $
            def & checkboxConf_type .~ [CbFitted, CbToggle]
                & setValue .~ (False <$ resetEvent)
        divClass "ui compact segment" $ do
          uiCheckbox blank $
            def & checkboxConf_type .~ [CbFitted, CbSlider]
                & setValue .~ (False <$ resetEvent)

dropdowns :: MonadWidget t m => m ()
dropdowns = do

  resetEvent <- divClass "ui top attached segment" $ do
    elClass "h4" "ui header" $ do
      text "Dropdowns"
      uiButton (rightFloated . mini . compact . basic <$> def) $ text "Reset"

  divClass "ui bottom attached segment form" $ do
    let makeContact x = (x, DropdownItemConfig (tshow x) $ renderContact x)
        contacts = map makeContact [minBound..maxBound]
        makeCard x = (x, DropdownItemConfig "" $ renderCard x)
        cards = map makeCard [minBound..maxBound]
        makeState x = (x, DropdownItemConfig "" $ text $ showState x)
        states = map makeState [minBound..maxBound]
        makeCountry x = (x, DropdownItemConfig "" $ renderCountry x)
        countries = map makeCountry [minBound..maxBound]

    divClass "two fields" $ do
      divClass "field" $ do
        rec el "label" $ do
              text "Single value"
              divClass "ui left pointing label" $ display card
            card <- uiDropdown cards [DOFSelection] $
              def & dropdownConf_placeholder .~ "Card Type"
                  & setValue .~ (Just Visa <$ resetEvent)
                  & dropdownConf_initialValue ?~ Visa
        return ()
      divClass "field" $ do
        rec el "label" $ do
              text "Single value, search"
              divClass "ui left pointing label" $ display contact
            contact <- uiDropdown contacts [DOFSearch, DOFSelection] $
              def & dropdownConf_placeholder .~ "Saved Contacts"
                  & setValue .~ (Nothing <$ resetEvent)
        return ()

    divClass "field" $ do
      rec el "label" $ do
            text "Multi value"
            divClass "ui left pointing label" $ display card
          card <- uiDropdownMulti cards [DOFSelection] $
            def & dropdownConf_placeholder .~ "Card Type"
                & setValue .~ (mempty <$ resetEvent)
      return ()

    divClass "field" $ do
      rec el "label" $ do
            text "Multi value, full-text search"
            divClass "ui left pointing label" $ display contact
          contact <- uiDropdownMulti contacts [DOFSearch, DOFSelection] $
            def & dropdownConf_placeholder .~ "Saved Contacts"
                & setValue .~ ([Matt, Elliot] <$ resetEvent)
                & dropdownConf_initialValue .~ [Matt, Elliot]
                & dropdownConf_fullTextSearch .~ True
      return ()

    divClass "two fields" $ do
      divClass "field" $ do
        rec el "label" $ do
              text "Multi value, limited"
              divClass "ui left pointing label" $ display state
            state <- uiDropdownMulti states [DOFSelection] $
              def & dropdownConf_placeholder .~ "States"
                  & setValue .~ (mempty <$ resetEvent)
                  & dropdownConf_maxSelections ?~ 3
        return ()
      divClass "field" $ do
        rec el "label" $ do
              text "Multi value, search, hidden labels"
              divClass "ui left pointing label" $ display country
            country <- uiDropdownMulti countries [DOFSearch, DOFSelection] $
              def & dropdownConf_placeholder .~ "Country"
                  & setValue .~ (mempty <$ resetEvent)
                  & dropdownConf_useLabels .~ False
        return ()

main :: IO ()
main = mainWidget $ divClass "ui container" $ do
  checkboxes
  dropdowns

-- This causes startup time to go to ~5 seconds
--    divClass "field" $ do
--      rec el "label" $ do
--            text "Country old"
--            divClass "ui left pointing label" $ display country
--          country <- semUiDropdownWithItems "country-dropdown"
--            [DOFSelection, DOFSearch] US (constDyn $ fromList countries) mempty
--      return ()



  el "p" $ text "These are examples of semantic-ui widgets."
  el "p" $ uiButton (huge $ inverted $ blue def) (text "I'm a huge, inverted, blue button!")

  divClass "example" $ do
    text "Fluid selection dropdown"
    v <- semUiDropdownWithItems "test-dropdown-1"
         [DOFSelection, DOFFluid] Nothing entries mempty
    el "br" $ blank
    display v

  divClass "example" $ do
    text "Selection dropdown"
    w <- semUiDropdownWithItems "test-dropdown-2"
         [DOFSelection] Nothing entries mempty
    el "br" $ blank
    display w

entries :: MonadWidget t m => Dynamic t (Map (Maybe Int) (DropdownItemConfig m))
entries = constDyn . fromList $ entry <$> (Nothing : (Just <$> [0..4]))
  where -- entry :: Maybe Int -> (Maybe Int,DropdownItemConfig m)
        entry n =
          (n, DropdownItemConfig (spell n) $
              elAttr "div" ("style" =: style) $ do
                elAttr "span" ("style" =: "font-weight: bold;") $ text $ tshow n
                elAttr "span" ("style" =: "font-style: italic;")   $ text $ spell n
          )
        style = "display: flex; justify-content: space-between; "

spell :: Maybe Int -> Text
spell Nothing = "Favorite number"
spell (Just n)
  | n < length spellWords = spellWords !! n
  | otherwise = "Unhandled Option"
  where spellWords = ["Zero","One","Two","Three","Four"]
