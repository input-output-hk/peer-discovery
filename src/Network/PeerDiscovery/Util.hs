module Network.PeerDiscovery.Util
  ( -- * CBOR
    serialise'
  , deserialiseOrFail'
  , encodePortNumber
  , decodePortNumber
  , matchSize
  -- * MVar
  , withMVarP
  , modifyMVarP
  , modifyMVarP_
  -- * Misc
  , randomPartition
  , mkInteger
  , (<&>)
  ) where

import Codec.CBOR.Decoding
import Codec.CBOR.Encoding
import Codec.Serialise
import Control.Concurrent
import Control.Monad
import Data.Bits
import Data.Word
import Network.Socket
import System.Random.Shuffle
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BSL
import qualified Data.Map.Strict as M

-- | Strict version of 'serialise'.
serialise' :: Serialise a => a -> BS.ByteString
serialise' = BSL.toStrict . serialise

-- | Strict version of 'deserialiseOrFail'.
deserialiseOrFail' :: Serialise a => BS.ByteString -> Either DeserialiseFailure a
deserialiseOrFail' = deserialiseOrFail . BSL.fromStrict

-- | Encoder for PortNumber.
encodePortNumber :: (Functor f, Serialise (f Word16)) => f PortNumber -> Encoding
encodePortNumber = encode . fmap (fromIntegral :: PortNumber -> Word16)

-- | Decoder for PortNumber.
decodePortNumber :: (Functor f, Serialise (f Word16)) => Decoder s (f PortNumber)
decodePortNumber = fmap (fromIntegral :: Word16 -> PortNumber) <$> decode

matchSize
  :: Int    -- ^ requested
  -> String -- ^ label for error message
  -> Int    -- ^ actual
  -> Decoder s ()
matchSize requested label actual = when (actual /= requested) $ do
  fail $ label ++ ": failed size check, expected " ++ show requested
      ++ ", found " ++ show actual

----------------------------------------

withMVarP :: MVar a -> (a -> r) -> IO r
withMVarP mv f = withMVar mv $ return . f

-- | Strictly apply a pure function to contents of MVar and return a result.
modifyMVarP :: MVar a -> (a -> (a, r)) -> IO r
modifyMVarP mv f = modifyMVar mv $ \v -> do
  let ret@(v', _) = f v
  v' `seq` return ret

-- | Strictly apply a pure function to contents of MVar.
modifyMVarP_ :: MVar a -> (a -> a) -> IO ()
modifyMVarP_ mv f = modifyMVar_ mv $ \v -> return $! f v

----------------------------------------

-- | Randomly partition a list into N sublists of similar size.
randomPartition :: Int -> [a] -> IO [[a]]
randomPartition n xs = shuffleM (take (length xs) $ cycle [1..n])
  <&> M.elems . M.fromListWith (++) . (`zip` map pure xs)

-- | Convert an Integer into a ByteString by interpreting it as its big endian
-- representation.
mkInteger :: BS.ByteString -> Integer
mkInteger = BS.foldl' (\acc w -> acc `shiftL` 8 + fromIntegral w) 0

(<&>) :: Functor f => f a -> (a -> b) -> f b
(<&>) = flip fmap
infixl 1 <&>
