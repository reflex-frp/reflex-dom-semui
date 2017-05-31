{-# LANGUAGE OverloadedStrings #-}

module StateEnum where

import Prelude hiding (GT, LT)

import Data.Text (Text)
import qualified Data.Text as T
import Reflex.Dom.Core

data StateEnum
  = AL | AK | AZ | AR | CA | CO | CT | DE | DC | FL | GA | HI | ID | IL | IN
  | IA | KS | KY | LA | ME | MD | MA | MI | MN | MS | MO | MT | NE | NV | NH
  | NJ | NM | NY | NC | ND | OH | OK | OR | PA | RI | SC | SD | TN | TX | UT
  | VT | VA | WA | WV | WI | WY
  deriving (Bounded, Enum, Eq, Ord, Read, Show)

showState :: StateEnum -> Text
showState AL = "Alabama"
showState AK = "Alaska"
showState AZ = "Arizona"
showState AR = "Arkansas"
showState CA = "California"
showState CO = "Colorado"
showState CT = "Connecticut"
showState DE = "Delaware"
showState DC = "District Of Columbia"
showState FL = "Florida"
showState GA = "Georgia"
showState HI = "Hawaii"
showState ID = "Idaho"
showState IL = "Illinois"
showState IN = "Indiana"
showState IA = "Iowa"
showState KS = "Kansas"
showState KY = "Kentucky"
showState LA = "Louisiana"
showState ME = "Maine"
showState MD = "Maryland"
showState MA = "Massachusetts"
showState MI = "Michigan"
showState MN = "Minnesota"
showState MS = "Mississippi"
showState MO = "Missouri"
showState MT = "Montana"
showState NE = "Nebraska"
showState NV = "Nevada"
showState NH = "New Hampshire"
showState NJ = "New Jersey"
showState NM = "New Mexico"
showState NY = "New York"
showState NC = "North Carolina"
showState ND = "North Dakota"
showState OH = "Ohio"
showState OK = "Oklahoma"
showState OR = "Oregon"
showState PA = "Pennsylvania"
showState RI = "Rhode Island"
showState SC = "South Carolina"
showState SD = "South Dakota"
showState TN = "Tennessee"
showState TX = "Texas"
showState UT = "Utah"
showState VT = "Vermont"
showState VA = "Virginia"
showState WA = "Washington"
showState WV = "West Virginia"
showState WI = "Wisconsin"
showState WY = "Wyoming"
