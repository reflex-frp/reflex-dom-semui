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
-- | Passthrough instance for Either
instance (UiClassText a, UiClassText b) => UiClassText (Either a b) where
  uiText (Left a) = uiText a
  uiText (Right b) = uiText b

class UiHasCustom a where
  -- | IMPORTANT: Implementations of this function should use the accompanying
  -- 'addCustom' function to make sure that new values are added on and don't
  -- overwrite anything that was already there.
  custom :: Text -> a -> a

------------------------------------------------------------------------------
-- | Helper function for adding a class item to a custom class field.
addCustom :: Text -> Maybe Text -> Maybe Text
addCustom cls Nothing = Just cls
addCustom cls (Just c) = Just (T.unwords [cls, c])

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
data UiActive = UiActive
  deriving (Eq,Ord,Read,Show,Enum,Bounded)

instance UiClassText UiActive where
  uiText UiActive = "active"

class UiHasActive a where
  active :: a -> a

------------------------------------------------------------------------------
data UiDisabled = UiDisabled
  deriving (Eq,Ord,Read,Show,Enum,Bounded)

instance UiClassText UiDisabled where
  uiText UiDisabled = "disabled"

class UiHasDisabled a where
  disabled :: a -> a

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
data UiFlipped
  = UiFlipHoriz
  | UiFlipVert
  deriving (Eq,Ord,Read,Show,Enum,Bounded)

instance UiClassText UiFlipped where
  uiText UiFlipHoriz = "horizontally flipped"
  uiText UiFlipVert = "vertically flipped"

class UiHasFlipped a where
  uiSetFlipped :: UiFlipped -> a -> a

flipHoriz, flipVert :: UiHasFlipped a => a -> a
flipHoriz = uiSetFlipped UiFlipHoriz
flipVert = uiSetFlipped UiFlipVert


------------------------------------------------------------------------------
data UiRotated
  = UiRotateCounterclockwise
  | UiRotateClockwise
  deriving (Eq,Ord,Read,Show,Enum,Bounded)

instance UiClassText UiRotated where
  uiText UiRotateCounterclockwise = "counterclockwise rotated"
  uiText UiRotateClockwise = "clockwise rotated"

class UiHasRotated a where
  uiSetRotated :: UiRotated -> a -> a

counterclockwise, clockwise :: UiHasRotated a => a -> a
counterclockwise = uiSetRotated UiRotateCounterclockwise
clockwise = uiSetRotated UiRotateClockwise


------------------------------------------------------------------------------
data UiAlignment
  = UiLeftAligned
  | UiCenterAligned
  | UiRightAligned
  | UiJustified
  deriving (Eq,Ord,Read,Show,Enum,Bounded)

instance UiClassText UiAlignment where
  uiText UiLeftAligned = "left aligned"
  uiText UiCenterAligned = "center aligned"
  uiText UiRightAligned = "right aligned"
  uiText UiJustified = "justified"

class UiHasAlignment a where
  uiSetAlignment :: UiAlignment -> a -> a

leftAligned, centerAligned, rightAligned, justified :: UiHasAlignment a => a -> a
leftAligned = uiSetAlignment UiLeftAligned
centerAligned = uiSetAlignment UiCenterAligned
rightAligned = uiSetAlignment UiRightAligned
justified = uiSetAlignment UiJustified


------------------------------------------------------------------------------
data UiFitted = UiFitted
  deriving (Eq,Ord,Read,Show,Enum,Bounded)

instance UiClassText UiFitted where
  uiText UiFitted = "fitted"

class UiHasFitted a where
  fitted :: a -> a


------------------------------------------------------------------------------
data UiLeft = UiLeft
  deriving (Eq,Ord,Read,Show,Enum,Bounded)

instance UiClassText UiLeft where
  uiText UiLeft = "left"

class UiHasLeft a where
  uiLeft :: a -> a
  -- Use the ui prefix to not clash with the left function from errors


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
  uiToggle :: a -> a


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


------------------------------------------------------------------------------
data UiError = UiError
  deriving (Eq,Ord,Read,Show,Enum,Bounded)

instance UiClassText UiError where
  uiText UiError = "error"

class UiHasError a where
  hasError :: a -> a


------------------------------------------------------------------------------
data UiBordered = UiBordered
  deriving (Eq,Ord,Read,Show,Enum,Bounded)

instance UiClassText UiBordered where
  uiText UiBordered = "bordered"

class UiHasBordered a where
  bordered :: a -> a


------------------------------------------------------------------------------
data UiTransparent = UiTransparent
  deriving (Eq,Ord,Read,Show,Enum,Bounded)

instance UiClassText UiTransparent where
  uiText UiTransparent = "transparent"

class UiHasTransparent a where
  transparent :: a -> a


