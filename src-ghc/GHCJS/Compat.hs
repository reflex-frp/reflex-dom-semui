{-# OPTIONS_GHC -fno-warn-missing-methods #-}

{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}

module GHCJS.Compat where

import Data.String (IsString)
import Data.Text (Text)

data JSVal

pFromJSVal :: JSVal -> JSString
pFromJSVal = undefined

pToJSVal :: a -> JSVal
pToJSVal = undefined

data JSString
instance IsString JSString

class ToJSString a
instance ToJSString [Char]
instance ToJSString Text

toJSString :: ToJSString a => a -> JSString
toJSString = undefined

class FromJSString a
instance FromJSString [Char]
instance FromJSString Text

fromJSString :: FromJSString a => JSString -> a
fromJSString = undefined

toJSBool :: Bool -> JSVal
toJSBool = undefined

data Callback a

data OnBlocked
  = ContinueAsync
  | ThrowWouldBlock

syncCallback :: OnBlocked -> IO () -> IO (Callback (IO ()))
syncCallback = undefined

syncCallback1 :: OnBlocked -> (JSVal -> IO ()) -> IO (Callback (JSVal -> IO ()))
syncCallback1 = undefined

asyncCallback1 :: (JSVal -> IO ()) -> IO (Callback (JSVal -> IO ()))
asyncCallback1 = undefined

asyncCallback2 :: (JSVal -> JSVal -> IO ()) -> IO (Callback (JSVal -> JSVal -> IO ()))
asyncCallback2 = undefined

asyncCallback3 :: (JSVal -> JSVal -> JSVal -> IO ()) -> IO (Callback (JSVal -> JSVal -> JSVal -> IO ()))
asyncCallback3 = undefined

releaseCallback :: Callback a -> IO ()
releaseCallback = undefined
