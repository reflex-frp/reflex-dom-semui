{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE RecursiveDo       #-}

module Main (main) where

import Control.Lens
import Data.Map (Map, fromList)
import Data.Monoid ((<>))
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Vector as V
import Reflex.Dom
import Reflex.Dom.SemanticUI
import Reflex.Dom.Internal () -- TODO remove this once we solve orphan instance issue
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

main :: IO ()
main = mainWidget $ divClass "ui container" $ do
  (resetDropdowns, _) <- divClass "ui top attached segment" $ do
    elClass "h4" "ui header" $ do
      text "Dropdowns"
      elAttr' "a" ("class" =: "ui horizontal blue label") $ text "Reset"

  let resetEvent = domEvent Click resetDropdowns
  divClass "ui bottom attached segment form" $ do
    let makeContact x = (x, DropdownItemConfig (tshow x) $ renderContact x)
        contacts = V.fromList $ map makeContact [minBound..maxBound]
        makeCard x = (x, DropdownItemConfig "" $ renderCard x)
        cards = V.fromList $ map makeCard [minBound..maxBound]

    divClass "two fields" $ do
      divClass "field" $ do
        rec el "label" $ do
              text "Single value"
              divClass "ui left pointing label" $ display card
            initial <- holdDyn (Just Visa) $ (Just Visa) <$ resetEvent
            card <- semUiDropdownNew cards [DOFSelection] $
              def & dropdownConf_placeholder .~ "Card Type"
                  & setValue .~ initial
        return ()
      divClass "field" $ do
        rec el "label" $ do
              text "Searchable single value"
              divClass "ui left pointing label" $ display contact
            initial <- holdDyn Nothing $ Nothing <$ resetEvent
            contact <- semUiDropdownNew contacts [DOFSearch, DOFSelection] $
              def & dropdownConf_placeholder .~ "Saved Contacts"
                  & setValue .~ initial
        return ()

    divClass "two fields" $ do
      divClass "field" $ do
        rec el "label" $ do
              text "Multi value"
              divClass "ui left pointing label" $ display card
            initial <- holdDyn [] $ [] <$ resetEvent
            card <- semUiDropdownMultiNew cards [DOFSelection] $
              def & dropdownConf_placeholder .~ "Card Type"
                  & setValue .~ initial
        return ()
      divClass "field" $ do
        rec el "label" $ do
              text "Searchable multi value"
              divClass "ui left pointing label" $ display contact
            initial <- holdDyn [Matt, Elliot] $ [Matt, Elliot] <$ resetEvent
            contact <- semUiDropdownMultiNew contacts [DOFSearch, DOFSelection] $
              def & dropdownConf_placeholder .~ "Saved Contacts"
                  & setValue .~ initial
        return ()

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
