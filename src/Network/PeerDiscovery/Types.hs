module Network.PeerDiscovery.Types
  ( -- * Config
    Config(..)
  , defaultConfig
    -- * Peer
  , Peer(..)
  , mkPeer
    -- * PeerId
  , PeerId
  , mkPeerId
  , peerIdBitSize
  , randomPeerId
  , testPeerIdBit
  , distance
    -- * RpcId
  , RpcId
  , rpcIdBitSize
  , randomRpcId
    -- * Nonce
  , Nonce
  , randomNonce
    -- * Node
  , Node(..)
    -- * RoutingTable
  , NodeInfo(..)
  , RoutingTable(..)
  , RoutingTree(..)
    -- * ResponseHandler
  , ResponseHandler(..)
  , ResponseHandlers
    -- * PeerDiscovery
  , PeerDiscovery(..)
  ) where

import Codec.CBOR.Decoding
import Codec.CBOR.Encoding
import Codec.Serialise
import Control.Concurrent
import Data.Bits
import Data.Functor.Identity
import Data.List
import Data.Monoid
import Data.Typeable
import Network.Socket
import System.Random
import qualified Crypto.Hash as H
import qualified Crypto.PubKey.Ed25519 as C
import qualified Crypto.Random as C
import qualified Data.ByteArray as BA
import qualified Data.ByteString as BS
import qualified Data.Map.Strict as M
import qualified Data.Sequence as S

import Network.PeerDiscovery.Util

data Config = Config
  { configAlpha             :: !Int -- ^ Concurrency parameter.
  , configK                 :: !Int -- ^ Bucket size.
  , configB                 :: !Int -- ^ Maximum depth of the routing tree.
  , configMaxTimeouts       :: !Int -- ^ Number of acceptable timeouts before
                                    --   eviction from the routing tree.
  , configResponseTimeout   :: !Int -- ^ Response timeout in microseconds.
  , configSignalQueueSize   :: !Int -- ^ Size of the signal queue.
  }

defaultConfig :: Config
defaultConfig = Config
  { configAlpha             = 3
  , configK                 = 10
  , configB                 = 5
  , configMaxTimeouts       = 3
  , configResponseTimeout   = 500000
  , configSignalQueueSize   = 10000
  }

----------------------------------------

-- | IPv4 Peer.
data Peer = Peer
  { peerAddress :: !HostAddress
  , peerPort    :: !PortNumber
  } deriving (Eq, Ord)

instance Show Peer where
  showsPrec p Peer{..} = showsPrec p b1 . ("." ++)
                       . showsPrec p b2 . ("." ++)
                       . showsPrec p b3 . ("." ++)
                       . showsPrec p b4 . (":" ++)
                       . showsPrec p peerPort
    where
      (b1, b2, b3, b4) = hostAddressToTuple peerAddress

mkPeer :: SockAddr -> Maybe Peer
mkPeer (SockAddrInet port host) = Just (Peer host port)
mkPeer _                        = Nothing

----------------------------------------

-- Size of PeerId in bits.
peerIdBitSize :: Int
peerIdBitSize = 224

-- | PeerId is the peer identifier derivable from Peer, i.e. SHA224 of its data.
newtype PeerId = PeerId Integer
  deriving (Eq, Ord, Serialise)

instance Show PeerId where
  show = (++ "...") . toBinary
    where
      -- Show 16 most significant bits of an identifier.
      toBinary :: PeerId -> String
      toBinary (PeerId x) =
        foldr (\i acc -> (if testBit x i then "1" else "0") ++ acc) ""
          $ enumFromThenTo (peerIdBitSize - 1) (peerIdBitSize - 2) (peerIdBitSize - 16)

-- | Construct 'PeerId' from 'Peer'.
mkPeerId :: C.PublicKey -> PeerId
mkPeerId = PeerId . mkInteger . H.hashWith H.SHA224
  where
    mkInteger :: H.Digest H.SHA224 -> Integer
    mkInteger = foldl' (\acc w -> acc `shiftL` 8 + fromIntegral w) 0 . BA.unpack

-- | Generate random 'PeerId' using global 'StdGen'.
randomPeerId :: IO PeerId
randomPeerId = PeerId <$> randomRIO (0, 2^peerIdBitSize - 1)

-- | Test whether a specific bit of 'PeerId' is set.
testPeerIdBit :: PeerId -> Int -> Bool
testPeerIdBit (PeerId n) k = testBit n (peerIdBitSize - k - 1)

-- | Calculate distance between two peers using xor metric.
distance :: PeerId -> PeerId -> Integer
distance (PeerId a) (PeerId b) = a `xor` b

----------------------------------------

-- | Size of RpcId in bits.
rpcIdBitSize :: Int
rpcIdBitSize = 160

-- | Identifier of any RPC call for prevention of address forgery attacks and
-- linking requests with appropriate response handlers.
newtype RpcId = RpcId Integer
  deriving (Eq, Ord, Show, Serialise)

-- | Generate random 'RpcId' using global 'StdGen'
randomRpcId :: IO RpcId
randomRpcId = RpcId <$> randomRIO (0, 2^rpcIdBitSize - 1)

----------------------------------------

-- | Nonce used in authorization requests.
newtype Nonce = Nonce BS.ByteString
  deriving (Eq, Show, BA.ByteArrayAccess, Serialise)

randomNonce :: IO Nonce
randomNonce = Nonce <$> C.getRandomBytes 8

----------------------------------------

-- | 'Peer' along with its id.
data Node = Node
  { nodeId           :: !PeerId
  , nodePeer         :: !Peer
  } deriving (Eq, Show)

instance Serialise Node where
  encode Node{..} = encodeListLen 3
                 <> encode nodeId
                 <> encode (htonl peerAddress)
                 <> encodePortNumber (Identity peerPort)
    where
      Peer{..} = nodePeer

  decode = do
    matchSize 3 "decode(Node)" =<< decodeListLen
    nodeId   <- decode
    nodePeer <- Peer <$> (ntohl <$> decode)
                     <*> (runIdentity <$> decodePortNumber)
    pure Node{..}

----------------------------------------

-- | 'Node' along with additional info for 'RoutingTable'.
data NodeInfo = NodeInfo
  { niNode         :: !Node
  , niTimeoutCount :: !Int
  } deriving (Eq, Show)

-- | Routing table.
data RoutingTable = RoutingTable
  { rtId     :: !PeerId
  , rtTree   :: !RoutingTree
  } deriving (Eq, Show)

data RoutingTree = Bucket !(S.Seq NodeInfo)
                 | Split {- 1 -} !RoutingTree {- 0 -} !RoutingTree
  deriving (Eq, Show)

----------------------------------------

-- | Handler of a specific Request.
data ResponseHandler = forall r. Typeable r => ResponseHandler
  { rhRecipient        :: !Peer
  , rhTimeoutHandlerId :: !ThreadId
  , rhOnFailure        :: !(IO ())
  , rhHandler          :: !(r -> IO ())
  }

-- | Map of response handlers.
type ResponseHandlers = MVar (M.Map RpcId ResponseHandler)

-- | Primary object of interest.
data PeerDiscovery = PeerDiscovery
  { pdBindAddr         :: !Peer
  , pdPublicPort       :: !(Maybe PortNumber)
  , pdPublicKey        :: !C.PublicKey
  , pdSecretKey        :: !C.SecretKey
  , pdSocket           :: !Socket
  , pdRoutingTable     :: !(MVar RoutingTable)
  , pdResponseHandlers :: !ResponseHandlers
  , pdConfig           :: !Config
  }