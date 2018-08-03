{-# language RankNTypes, RecursiveDo #-}
module Main where

import Control.Concurrent
import Control.Monad
import Network.Socket
import Prelude
import System.Random
import Text.Pretty.Simple
import qualified Crypto.Error as C
import qualified Crypto.PubKey.Ed25519 as C
import qualified Data.ByteString as BS

import Network.PeerDiscovery
import Network.PeerDiscovery.Communication.Method
import Network.PeerDiscovery.Operations
import Network.PeerDiscovery.Types
import Data.Foldable (traverse_)

-- | Notes
--
-- TODO:
--
-- - Thread for periodically refreshing routing table (calling peer lookup)
--
-- - Replacement cache in the routing table.
--
-- - Abstract the network layer away to be able to use mockup routing for
--   large-scale testing.
--
-- NOT CLEAR:
--
-- - Exclude peers with non-zero amount of timeouts from being returned by
--   findClosest (most likely makes sense).
--
-- - Additional thread for periodically pinging peers with non-zero amount of
--   timeouts to speed up their eviction (possibly necessary if we do the
--   above).
--
-- ----------------------------------------
--
-- 1. IPv6 support - requires two instances, one for IPv4 and one for IPv6 - we
-- can't mix these two. Relatively easy to add. Alternative below.
--
-- IPv6 - we bind to IPv6 socket, disable IPv6Only flag (doesn't work on Windows
-- < 7, OpenBSD?) and accept connections from both IPv4 and IPv6 peers (we
-- translate IPv4 address of a peer embedded as IPv6 address to its original
-- form). We store both IPv4 and IPv6 addresses in our routing table (each leaf
-- has two buckets, one for IPv6 and one for IPv4). When IPv4 peer sends us
-- FindNode request, we only return IPv4 peers. When IPv6 peer sends us FindNode
-- request, it also sends whether he wants to receive IPv4 addresses. If that's
-- the case, we return both for a certain bucket, prioritizing IPv6 peers over
-- IPv4 ones.
--
-- IPv4 - we bind to IPv4 socket and store only IPv4 addresses in the routing
-- table (we keep empty buckets of IPv6 addresses for compatibility with IPv6
-- mode). A flag sent along with incoming FindNode requests about returning only
-- IPv6 hosts is ignored.
--
-- 2. We should support persistent key pairs. This way, for "central" instances
-- new nodes will boostrap their instances with, we can publish their key
-- fingerprints along with ip addresses / domain names, so that when we
-- bootstrap, we can use them to verify the authenticity of hosts we connect to.
--
-- 4. No need to worry about splitting data into multiple packets - for bucket
-- size of 10 ReturnNodes message takes less than 500 bytes. If we want to use
-- larger bucket size (which most likely is not needed as bucket size represents
-- redundancy and 10 is fine) it's fine up to 35 (~1430 bytes, Ethernet MTU is
-- 1500, 1472 for IPv4 and 1452 for IPv6 without appropriate headers).

-- | Start a bunch of threads, perform an action, and then
-- kill all the threads.
withThreads
  :: [IO ()]
  -> IO r
  -> IO r
withThreads tas m = do
  tids <- traverse forkIO tas
  r <- m
  traverse_ killThread tids
  pure r

withPeers
  :: Config
  -> CommunicationMethod cm
  -> [PortNumber]  -- Well-known peers
  -> [(Bool, PortNumber)] -- Other peers
  -> (PeerDiscovery cm -> [Node] -> IO ())
      -- Given a list of well-known peers, what should each peer do?
  -> IO r -- What should we do after starting up the network?
  -> IO r
withPeers conf router wkConnInfos connInfos them us = mdo
  putStrLn "Starting relays"
  wps :: [(ThreadId, Node)] <- traverse (go (fmap snd wps) True) wkConnInfos
  threadDelay (5*10^(6::Int))
  putStrLn "Starting other peers"
  ops <- traverse (\(joinp, port) -> go (fmap snd wps) joinp port) connInfos
  res <- us
  -- Take some time for the peers to do something.
  threadDelay (10^(7::Int))
  putStrLn "Killing everything"
  traverse_ (killThread . fst) $ wps ++ ops
  pure res
  where
    go :: [Node] -> Bool -> PortNumber -> IO (ThreadId, Node)
    go wps joinNetwork port = do
        let C.CryptoPassed skey = C.secretKey . BS.pack . take C.secretKeySize
                                . randoms . mkStdGen $ fromIntegral port
        tid <- forkIO $ withPeerDiscovery conf joinNetwork (Just skey) router port $ \pd ->
          them pd wps
        return (tid, Node (mkPeerId $ C.toPublic skey) (Peer 0 port))

-- | Start multiple peer discovery instances.
withPeerDiscoveries
  :: Config
  -> CommunicationMethod cm
  -> [(Bool, PortNumber)]
  -> ([PeerDiscovery cm] -> IO r)
  -> IO r
withPeerDiscoveries conf router connInfos k = go [] connInfos
  where
    go acc = \case
      []                                -> k (reverse acc)
      ((joinNetwork, port):rest) -> do
        let C.CryptoPassed skey = C.secretKey . BS.pack . take C.secretKeySize
                                . randoms . mkStdGen $ fromIntegral port
        withPeerDiscovery conf joinNetwork (Just skey) router port $ \pd ->
          go (pd : acc) rest

testWithComms :: forall cm. CommunicationMethod cm -> IO ()
testWithComms cm =
  withPeers defaultConfig cm (map snd wkConnInfos) otherConnInfos them $ do
    threadDelay (4*10^(6::Int))
    
  where
    wkConnInfos = map (True, ) [2900..3000]
    otherConnInfos = map (True, ) [3002,3004..6500] ++ map (False,) [3001,3003..4000]
    connInfos = wkConnInfos ++ otherConnInfos
    them :: PeerDiscovery cm -> [Node] -> IO ()
    them pd wks = do
      gen <- newStdGen
      let (boot_peer', gen') = randomR (0,99) gen
      putStrLn "bootstrapping peer"
      bootstrap pd (wks !! boot_peer') >>= print

      -- Wait for some others to bootstrap too.
      threadDelay (10^(6::Int))

      targetId <- randomPeerId
      putStrLn $ show targetId
      --pPrint =<< readMVar (pdRoutingTable pd)

      pPrint . map (\x -> let d = distance targetId (mkPeerId (pdPublicKey pd)) in (length (show d), d, x))
        =<< peerLookup pd targetId

      threadDelay (10^(7::Int)) -- Keep our PD instance alive for a while
      
{-
  withPeerDiscoveries defaultConfig cm connInfos $ \pds -> do

    let nodes = let xs = map (\pd -> Node { nodeId = mkPeerId $ pdPublicKey pd
                                          , nodePeer = pdBindAddr pd
                                          }) pds
                in last xs : init xs
    extra_done <- newEmptyMVar
    _ <- forkIO $ withPeerDiscovery defaultConfig True Nothing cm 3251 $ \pd -> do
      putStrLn "Extra joining"
      _ <- bootstrap pd (nodes !! 2)
      let target_id = nodeId $ nodes !! 100
      threadDelay 7000000
      close_peers <- peerLookup pd target_id
      putMVar extra_done $ map (\x -> distance target_id (nodeId x)) close_peers

    zipWithM_ (\pd node -> do
                  putStrLn $ "Bootstrapping " ++ show (pdBindAddr pd)
                  True <- bootstrap pd node
                  return ()
              ) pds nodes

    --forM_ pds $ \pd -> void $ peerLookup pd =<< randomPeerId
    --forM_ pds $ \pd -> void $ peerLookup pd =<< randomPeerId

    let pd1 = head pds
        pd2 = pds !! 250

    let targetId = mkPeerId $ pdPublicKey pd2
    putStrLn $ show targetId
    pPrint =<< readMVar (pdRoutingTable pd2)

    pPrint . map (\x -> let d = distance targetId (nodeId x) in (length (show d), d, x))
      =<< peerLookup pd1 targetId

    dn <- readMVar extra_done
    putStrLn $ "extra done: " ++ show dn

    void getLine
-}


main :: IO ()
main = withStmRouter $ \router -> testWithComms (stmRouter router)
