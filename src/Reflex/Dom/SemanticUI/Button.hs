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
import           Data.Default
import           Data.Maybe
import           Data.Text (Text)
import qualified Data.Text as T
import           Reflex.Dom hiding (fromJSString)
------------------------------------------------------------------------------
import           Reflex.Dom.SemanticUI.Common
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
    } deriving (Eq,Show)

instance Default UiButton where
  def = UiButton def def def def def def def def def def def

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
  toggle b = b { _uiButton_toggle = Just UiToggle }

instance UiHasFluid UiButton where
  fluid b = b { _uiButton_fluid = Just UiFluid }

instance UiHasCircular UiButton where
  circular b = b { _uiButton_circular = Just UiCircular }

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
    => Dynamic t UiButton
    -> m ()
    -> m (Event t ())
uiButton bDyn children = do
    (e,_) <- elDynAttr' "button" (mkAttrs <$> bDyn) children
    return $ domEvent Click e
  where
    mkAttrs b = "class" =: T.unwords ["ui", uiButtonAttrs b, "button"]

data UiButtonAnimationType
  = HorizontalAnimation
  | VerticalAnimation
  | FadeAnimation
  deriving (Eq,Ord,Read,Show,Enum,Bounded)

instance UiClassText UiButtonAnimationType where
   uiText HorizontalAnimation = "animated"
   uiText VerticalAnimation = "vertical animated"
   uiText FadeAnimation = "animated fade"

------------------------------------------------------------------------------
-- | Implements animated buttons that change when you hover over them.
uiButtonAnimated
    :: MonadWidget t m
    => UiButtonAnimationType
    -- ^ Controls the type of the animation
    -> Dynamic t UiButton
    -> m ()
    -- ^ The visible section
    -> m ()
    -- ^ The hidden section
    -> m (Event t ())
uiButtonAnimated anim bDyn visible hidden = do
    (e,_) <- elDynAttr' "button" (mkAttrs <$> bDyn) $ do
      divClass "visible content" visible
      divClass "hidden content" hidden
    return $ domEvent Click e
  where
    mkAttrs b = "class" =: T.unwords ["ui", uiButtonAttrs b, uiText anim, "button"]

