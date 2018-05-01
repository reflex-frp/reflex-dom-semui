{-# LANGUAGE CPP                      #-}
{-# LANGUAGE ConstraintKinds          #-}
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
import           Data.Default
import           Data.Maybe
import           Data.Monoid
import           Data.Text       (Text)
import qualified Data.Text       as T
import           Reflex.Dom.Core hiding (fromJSString)
------------------------------------------------------------------------------
import Reflex.Dom.SemanticUI.Common
import Reflex.Dom.SemanticUI.Icon
------------------------------------------------------------------------------

------------------------------------------------------------------------------
-- | Data structure describing options available for buttons.  The typical way
-- of using this data structure is to use the default instance and modify it
-- using the various UiHasXYZ type classes.  For instance:
--
-- @huge $ inverted $ blue def@
data UiButton = UiButton
    { _uiButton_emphasis   :: Maybe UiEmphasis
    , _uiButton_color      :: Maybe UiColor
    , _uiButton_basic      :: Maybe UiBasic
    , _uiButton_inverted   :: Maybe UiInverted
    , _uiButton_activation :: Maybe (Either UiActive UiDisabled)
    -- ^ active and disabled should be mutually exclusive so we use an Either
    , _uiButton_size       :: Maybe UiSize
    , _uiButton_loading    :: Maybe UiLoading
    , _uiButton_compact    :: Maybe UiCompact
    , _uiButton_toggle     :: Maybe UiToggle
    , _uiButton_fluid      :: Maybe UiFluid
    , _uiButton_circular   :: Maybe UiCircular
    , _uiButton_floated    :: Maybe UiFloated
    , _uiButton_custom     :: Maybe Text
    } deriving (Eq,Show)

instance Default UiButton where
  def = UiButton def def def def def def def def def def def def def

instance UiHasColor UiButton where
  uiSetColor c b = b { _uiButton_color = Just c }

instance UiHasEmphasis UiButton where
  uiSetEmphasis e b = b { _uiButton_emphasis = Just e }

instance UiHasBasic UiButton where
  basic b = b { _uiButton_basic = Just UiBasic }

instance UiHasInverted UiButton where
  inverted b = b { _uiButton_inverted = Just UiInverted }

instance UiHasActive UiButton where
  active b = b { _uiButton_activation = Just $ Left UiActive }

instance UiHasDisabled UiButton where
  disabled b = b { _uiButton_activation = Just $ Right UiDisabled }

instance UiHasSize UiButton where
  uiSetSize c b = b { _uiButton_size = Just c }

instance UiHasLoading UiButton where
  loading b = b { _uiButton_loading = Just UiLoading }

instance UiHasCompact UiButton where
  compact b = b { _uiButton_compact = Just UiCompact }

instance UiHasToggle UiButton where
  uiToggle b = b { _uiButton_toggle = Just UiToggle }

instance UiHasFluid UiButton where
  fluid b = b { _uiButton_fluid = Just UiFluid }

instance UiHasCircular UiButton where
  circular b = b { _uiButton_circular = Just UiCircular }

instance UiHasFloated UiButton where
  uiSetFloated f b = b { _uiButton_floated = Just f }

instance UiHasCustom UiButton where
  custom s i = i { _uiButton_custom = addCustom s (_uiButton_custom i) }


data UiButtonType = UiSimpleButton | UiSubmitButton | UiResetButton
                  deriving (Eq,Ord,Read,Show,Enum,Bounded)

instance Default UiButtonType where def = UiSimpleButton

buttonTypeAttrValue :: UiButtonType -> Text
buttonTypeAttrValue x = case x of
  UiSimpleButton -> "button"
  UiSubmitButton -> "submit"
  UiResetButton  -> "reset"

------------------------------------------------------------------------------
-- | Helper function mostly intended for internal use.  Exported for
-- completeness.
uiButtonAttrs :: UiButton -> Text
uiButtonAttrs UiButton{..} = T.unwords $ catMaybes
    [ uiText <$> _uiButton_emphasis
    , uiText <$> _uiButton_color
    , uiText <$> _uiButton_basic
    , uiText <$> _uiButton_inverted
    , uiText <$> _uiButton_activation
    , uiText <$> _uiButton_size
    , uiText <$> _uiButton_loading
    , uiText <$> _uiButton_compact
    , uiText <$> _uiButton_toggle
    , uiText <$> _uiButton_fluid
    , uiText <$> _uiButton_circular
    , uiText <$> _uiButton_floated
    , _uiButton_custom
    ]

------------------------------------------------------------------------------
-- | The primary function for creating Semantic UI buttons.  Much of Semantic
-- UI's button functionality is available from this function:
--
-- @uiButton (huge $ inverted $ blue def) (text "Click Me")@
--
-- Some of the Semantic UI button functionality requires a certain class and
-- additional structure from the child nodes.  This kind of functionality is
-- provided by other functions such as 'uiButtonAnimated'.
uiButton
    :: MonadWidget t m
    => UiButtonType
    -> Dynamic t UiButton
    -> m ()
    -> m (Event t ())
uiButton bType bDyn children = do
    (e,_) <- elDynAttr' "button" (mkAttrs <$> bDyn) children
    return $ domEvent Click e
  where
    mkAttrs b = "class" =: T.unwords ["ui", uiButtonAttrs b, "button"]
             <> "type"  =: buttonTypeAttrValue bType

data UiButtonAnimationType
  = HorizontalAnimation
  | VerticalAnimation
  | FadeAnimation
  deriving (Eq,Ord,Read,Show,Enum,Bounded)

instance UiClassText UiButtonAnimationType where
   uiText HorizontalAnimation = "animated"
   uiText VerticalAnimation   = "vertical animated"
   uiText FadeAnimation       = "animated fade"

------------------------------------------------------------------------------
-- | Implements animated buttons that change when you hover over them.
uiButtonAnimated
    :: MonadWidget t m
    => UiButtonType
    -> UiButtonAnimationType
    -- ^ Controls the type of the animation
    -> Dynamic t UiButton
    -> m ()
    -- ^ The visible section
    -> m ()
    -- ^ The hidden section
    -> m (Event t ())
uiButtonAnimated bType anim bDyn visible hidden = do
    (e,_) <- elDynAttr' "button" (mkAttrs <$> bDyn) $ do
      divClass "visible content" visible
      divClass "hidden content" hidden
    return $ domEvent Click e
  where
    mkAttrs b = "class" =: T.unwords ["ui", uiButtonAttrs b, uiText anim, "button"]
             <> "type"  =: buttonTypeAttrValue bType

------------------------------------------------------------------------------
-- | Implements a labeled icon button.  The icon can be on the left or the
-- right and this widget uses the Either type to indicate that.
uiLabeledIconButton
    :: MonadWidget t m
    => UiButtonType
    -> Either Text Text
    -> Dynamic t UiButton
    -> Dynamic t UiIcon
    -> m ()
    -> m (Event t ())
uiLabeledIconButton bType iconType bDyn iDyn children =
    uiButton bType (custom (eText $ setE "labeled" iconType) <$> bDyn) $ do
      uiIcon (eText iconType) iDyn
      children
  where
    eText (Left t)  = t
    eText (Right t) = T.unwords ["right", t]
    setE a (Left _)  = Left a
    setE a (Right _) = Right a
