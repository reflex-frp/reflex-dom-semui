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

module Reflex.Dom.SemanticUI.Common where

------------------------------------------------------------------------------
import           Data.Default
import           Data.Text (Text)
import qualified Data.Text as T
import           Reflex.Dom
------------------------------------------------------------------------------

------------------------------------------------------------------------------
-- | Temporary...will be moved out of here eventually.
tshow :: Show a => a -> Text
tshow = T.pack . show

instance (Default a, Reflex t) => Default (Dynamic t a) where
  def = constDyn def

------------------------------------------------------------------------------
-- | A type class for converting data types into appropriate  Semantic UI
-- class text.
class UiClassText a where
  uiText :: a -> Text

------------------------------------------------------------------------------
data UiColor
  = UiRed
  | UiOrange
  | UiYellow
  | UiOlive
  | UiGreen
  | UiTeal
  | UiBlue
  | UiViolet
  | UiPurple
  | UiPink
  | UiBrown
  | UiGrey
  | UiBlack
  deriving (Eq,Ord,Read,Show,Enum,Bounded)

instance UiClassText UiColor where
  uiText UiRed = "red"
  uiText UiOrange = "orange"
  uiText UiYellow = "yellow"
  uiText UiOlive = "olive"
  uiText UiGreen = "green"
  uiText UiTeal = "teal"
  uiText UiBlue = "blue"
  uiText UiViolet = "violet"
  uiText UiPurple = "purple"
  uiText UiPink = "pink"
  uiText UiBrown = "brown"
  uiText UiGrey = "grey"
  uiText UiBlack = "black"

class UiHasColor a where
  uiSetColor :: UiColor -> a -> a

instance (Reflex t, UiHasColor a) => UiHasColor (Dynamic t a) where
  uiSetColor c = fmap (uiSetColor c)

red, orange, yellow, olive, green, teal, blue, violet, purple, pink, brown, grey, black
  :: UiHasColor a => a -> a
red = uiSetColor UiRed
orange = uiSetColor UiOrange
yellow = uiSetColor UiYellow
olive = uiSetColor UiOlive
green = uiSetColor UiGreen
teal = uiSetColor UiTeal
blue = uiSetColor UiBlue
violet = uiSetColor UiViolet
purple = uiSetColor UiPurple
pink = uiSetColor UiPink
brown = uiSetColor UiBrown
grey = uiSetColor UiGrey
black = uiSetColor UiBlack

------------------------------------------------------------------------------
data UiEmphasis
  = UiPrimary
  | UiSecondary
  | UiPositive
  | UiNegative
  deriving (Eq,Ord,Read,Show,Enum,Bounded)

instance UiClassText UiEmphasis where
  uiText UiPrimary = "primary"
  uiText UiSecondary = "secondary"
  uiText UiPositive = "positive"
  uiText UiNegative = "negative"

class UiHasEmphasis a where
  uiSetEmphasis :: UiEmphasis -> a -> a

primary, secondary, positive, negative :: UiHasEmphasis a => a -> a
primary = uiSetEmphasis UiPrimary
secondary = uiSetEmphasis UiSecondary
positive = uiSetEmphasis UiPositive
negative = uiSetEmphasis UiNegative

------------------------------------------------------------------------------
data UiBasic = UiBasic
  deriving (Eq,Ord,Read,Show,Enum,Bounded)

instance UiClassText UiBasic where
  uiText UiBasic = "basic"

class UiHasBasic a where
  basic :: a -> a

------------------------------------------------------------------------------
data UiInverted = UiInverted
  deriving (Eq,Ord,Read,Show,Enum,Bounded)

instance UiClassText UiInverted where
  uiText UiInverted = "inverted"

class UiHasInverted a where
  inverted :: a -> a

instance (Reflex t, UiHasInverted a) => UiHasInverted (Dynamic t a) where
  inverted = fmap inverted

------------------------------------------------------------------------------
data UiActivation
  = UiActive
  | UiDisabled
  deriving (Eq,Ord,Read,Show,Enum,Bounded)

instance UiClassText UiActivation where
  uiText UiActive = "active"
  uiText UiDisabled = "disabled"

class UiHasActivation a where
  uiSetActivation :: UiActivation -> a -> a

active, disabled :: UiHasActivation a => a -> a
active = uiSetActivation UiActive
disabled = uiSetActivation UiDisabled

------------------------------------------------------------------------------
data UiSize
  = UiMini
  | UiTiny
  | UiSmall
  | UiMedium
  | UiLarge
  | UiBig
  | UiHuge
  | UiMassive
  deriving (Eq,Ord,Read,Show,Enum,Bounded)

instance UiClassText UiSize where
  uiText UiMini = "mini"
  uiText UiTiny = "tiny"
  uiText UiSmall = "small"
  uiText UiMedium = "medium"
  uiText UiLarge = "large"
  uiText UiBig = "big"
  uiText UiHuge = "huge"
  uiText UiMassive = "massive"

class UiHasSize a where
  uiSetSize :: UiSize -> a -> a

instance (Reflex t, UiHasSize a) => UiHasSize (Dynamic t a) where
  uiSetSize c = fmap (uiSetSize c)

mini, tiny, small, medium, large, big, huge, massive :: UiHasSize a => a -> a
mini = uiSetSize UiMini
tiny = uiSetSize UiTiny
small = uiSetSize UiSmall
medium = uiSetSize UiMedium
large = uiSetSize UiLarge
big = uiSetSize UiBig
huge = uiSetSize UiHuge
massive = uiSetSize UiMassive

------------------------------------------------------------------------------
data UiLoading = UiLoading
  deriving (Eq,Ord,Read,Show,Enum,Bounded)

instance UiClassText UiLoading where
  uiText UiLoading = "loading"

class UiHasLoading a where
  loading :: a -> a

------------------------------------------------------------------------------
data UiCompact = UiCompact
  deriving (Eq,Ord,Read,Show,Enum,Bounded)

instance UiClassText UiCompact where
  uiText UiCompact = "compact"

class UiHasCompact a where
  compact :: a -> a

------------------------------------------------------------------------------
data UiToggle = UiToggle
  deriving (Eq,Ord,Read,Show,Enum,Bounded)

instance UiClassText UiToggle where
  uiText UiToggle = "toggle"

class UiHasToggle a where
  toggle :: a -> a

------------------------------------------------------------------------------
data UiFluid = UiFluid
  deriving (Eq,Ord,Read,Show,Enum,Bounded)

instance UiClassText UiFluid where
  uiText UiFluid = "fluid"

class UiHasFluid a where
  fluid :: a -> a


------------------------------------------------------------------------------
data UiCircular = UiCircular
  deriving (Eq,Ord,Read,Show,Enum,Bounded)

instance UiClassText UiCircular where
  uiText UiCircular = "circular"

class UiHasCircular a where
  circular :: a -> a
