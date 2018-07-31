module Network.PeerDiscovery.Operations
  ( bootstrap
  , peerLookup
  , handleRequest
  , performRoutingTableMaintenance
  ) where

import Control.Arrow ((&&&))
import Control.Concurrent.Async
import Control.Concurrent.MVar
import Control.Concurrent.STM
import Control.Exception
import Control.Monad
import Data.Function
import Data.Maybe
import Prelude
import qualified Crypto.PubKey.Ed25519 as C
import qualified Data.Foldable as F
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.Sequence as Seq
import qualified Data.Traversable as F

import Network.PeerDiscovery.Communication
import Network.PeerDiscovery.Routing
import Network.PeerDiscovery.Types
import Network.PeerDiscovery.Util

-- | Bootstrap the instance with initial peer. Returns 'True'
-- if bootstrapping was successful.
bootstrap
  :: PeerDiscovery cm
  -> Node -- ^ Initial peer
  -> IO Bool
bootstrap pd node = do
  -- Why do we have this transaction and then one in bootstrapUnlessDone?
  -- We have two requirements:
  --
  -- 1. If bootstrapping was previously done and we're now re-bootstrapping,
  -- we actually want to bootstrap.
  --
  -- 2. However, if bootstrapping is currently *in progress*, we just want
  -- to wait for it to succeed.
  --
  -- We originally used just one transaction:
  --
  -- atomically $ readTVar (pdBootstrapState pd) >>= \case
  --   BootstrapInProgress -> retry
  --   bs -> do
  --      writeTVar (pdBootstrapState pd) BootstrapInProgress
  --      return ...
  --
  -- This accomplishes (1), but not (2). If bootstrapping is already in
  -- progress, the single transaction would indeed wait for it to complete,
  -- but then repeat it whether it succeeded or not.
  atomically $ readTVar (pdBootstrapState pd) >>= \case
    BootstrapDone -> writeTVar (pdBootstrapState pd) BootstrapNeeded
    _ -> pure ()
  bootstrapUnlessDone pd node

-- | Bootstrap the instance with initial peer, unless we are already
-- bootstrapped. Returns 'True' if bootstrapping was successful or we
-- were already bootstrapped.
bootstrapUnlessDone
  :: PeerDiscovery cm
  -> Node -- ^ Initial peer
  -> IO Bool
bootstrapUnlessDone pd node = do
  -- Save the requested public port. If something goes wrong
  -- (we can't ping the initial peer at all or we receive an exception)
  -- we restore this.
  requestedPublicPort <- readMVar (pdPublicPort pd)
  -- If we receive an exception after setting BootstrapInProgress, we need
  -- to be sure to set it back to BootstrapNeeded to unblock any other threads
  -- that are attempting to bootstrap.
  let
    resetBootstrap = do
      modifyMVarP_ (pdPublicPort pd) (const requestedPublicPort)
      atomically $ writeTVar (pdBootstrapState pd) BootstrapNeeded
  (`onException` resetBootstrap) $ do
    bootstrap_still_needed <- atomically $ readTVar (pdBootstrapState pd) >>= \case
      -- If bootstrapping is already in progress, let it proceed.
      BootstrapInProgress -> retry
      -- We are already bootstrapped, so we don't need to do anything.
      BootstrapDone -> pure False
      -- The job is ours: bootstrap.
      BootstrapNeeded -> True <$ writeTVar (pdBootstrapState pd) BootstrapInProgress
    if not bootstrap_still_needed
    then return True
    else do
      -- Filled with True if the initial ping succeeds; filled with
      -- False otherwise.
      initialPingMV <- newEmptyMVar
  
      -- We do this asynchronously: there's no need to wait for a response
      -- to the initial ping before sending the one that checks for global
      -- reachability.
      sendRequest pd (Ping Nothing) node
        -- Failed to ping the initial peer. Reset the
        -- bootstrap state and report failure.
        (putMVar initialPingMV False) $
        -- Successfully pinged the initial peer.
        \Pong -> do
        -- We successfully contacted (and thus authenticated) the initial peer, so
        -- it's safe to insert him into the routing table.
        modifyMVarP_ (pdRoutingTable pd) $ unsafeInsertPeer (pdConfig pd) node
        myId <- withMVarP (pdRoutingTable pd) rtId
        -- Populate our neighbourhood.
        void $ peerLookup pd myId
        fix $ \loop -> do
          targetId <- randomPeerId
          -- Populate part of the routing table holding nodes far from us.
          if testPeerIdBit myId 0 /= testPeerIdBit targetId 0
            then do
                   _ <- peerLookup pd targetId
                   return ()
            else loop
        putMVar initialPingMV True
  
      case requestedPublicPort of
          Nothing   -> return ()
          Just port -> do
            -- Check if we're globally reachable on the specified port.
            reachable <- sendRequestSync pd (Ping $ Just port) node
              (return False)
              (\Pong -> return True)
            -- If we're not, erase the port so we don't pretend in future
            -- communication that we are.
            when (not reachable) $ do
              putStrLn $ "bootstrap: we are not globally reachable on " ++ show port
              modifyMVarP_ (pdPublicPort pd) (const Nothing)
  
      -- In principle, I believe we could cancel the initial ping if the
      -- global reachability test succeeds. But we don't currently have
      -- the ability to cancel requests, and I don't know if it's worth the
      -- trouble.
      initial_ping_succeeded <- readMVar initialPingMV
      if not initial_ping_succeeded
      then resetBootstrap >> return False
      else do
        atomically $ writeTVar (pdBootstrapState pd) BootstrapDone
        return True

----------------------------------------

-- | Post-processed response of a 'FindNode' request.
data Reply = Success !Node !ReturnNodes
           | Failure !Distance !Node

-- | Perform Kademlia peer lookup operation and return up to k live peers
-- closest to a target id.
peerLookup :: PeerDiscovery cm -> PeerId -> IO [Node]
peerLookup pd@PeerDiscovery{..} targetId = do
  -- We start by taking k peers closest to the target from our routing table.
  closest <- withMVarP pdRoutingTable $ map (distance targetId . nodeId &&& id)
                                      . findClosest (configK pdConfig) targetId
  -- Put ourselves in the initial set of failed peers to avoid contacting
  -- ourselves during lookup as there is no point, we already picked the best
  -- peers we had in the routing table.
  failed <- withMVarP pdRoutingTable (S.singleton . rtId)

  -- We partition k initial peers into (at most) d buckets of similar size to
  -- perform d independent lookups with disjoin routing paths to make it hard
  -- for an adversary to reroute us into the part of network he controls.
  buckets <- randomPartition (configD pdConfig) closest
  let !bucketsLen = length buckets
  -- We share the list of nodes we query to make routing paths disjoint.
  queried <- newMVar M.empty
  -- Perform up to d lookups in parallel.
  results <- forConcurrently buckets $ \bucket -> do
    queue <- newTQueueIO
    outerLoop queue (M.fromList bucket) queried failed

  return . map fst . take (configK pdConfig)
         -- Consider only nodes that were returned by the majority of lookups.
         . filter ((> bucketsLen `quot` 2) . snd)
         -- Count the number of lookups that returned a specific node.
         . M.toList . M.fromListWith (+) . map (, 1::Int)
         $ concat results
  where
    outerLoop
      :: TQueue Reply
      -> M.Map Distance Node
      -> MVar (M.Map Distance Node)
      -> S.Set PeerId
      -> IO [Node]
    outerLoop queue closest queried failed = do
      -- We select alpha peers from the k closest ones we didn't yet query.
      chosen <- peersToQuery queried (configAlpha pdConfig) closest
      if null chosen
        -- If there isn't anyone left to query, the lookup is done.
        then return . M.elems $ M.take (configK pdConfig) closest
        else do
          sendFindNodeRequests queue chosen
          -- Process responses from chosen peers and update the list of closest
          -- and queried peers accordingly.
          (newClosest, newFailed) <-
            processResponses queue queried (length chosen) closest failed

          -- We returned from processResponses which indicates that the closest
          -- peer didn't change (as if it did, we would send more FindNode
          -- requests), so now we send FindNode requests to all of the k closest
          -- peers we didn't yet query.
          rest <- peersToQuery queried (configK pdConfig) newClosest
          sendFindNodeRequests queue rest
          (newerClosest, newerFailed) <-
            processResponses queue queried (length rest) newClosest newFailed

          outerLoop queue newerClosest queried newerFailed

    -- Select a number of chosen peers from the k closest ones we didn't yet
    -- query to send them FindNode requests and mark them as queried so parallel
    -- lookups will not select them as we want routing paths to be disjoint.
    peersToQuery
      :: MVar (M.Map Distance Node)
      -> Int
      -> M.Map Distance Node
      -> IO ([(Distance, Node)])
    peersToQuery mvQueried n closest = modifyMVarP mvQueried $ \queried ->
      let chosen = M.take n $ (M.take (configK pdConfig) closest) M.\\ queried
      in (queried `M.union` chosen, M.toList chosen)

    -- Asynchronously send FindNode requests to multiple peers and put the
    -- responses in a queue so we can synchronously process them as they come.
    sendFindNodeRequests
      :: TQueue Reply
      -> [(Distance, Node)]
      -> IO ()
    sendFindNodeRequests queue peers = do
      publicPort <- readMVar pdPublicPort
      myId <- withMVarP pdRoutingTable rtId
      let findNode = FindNode { fnPeerId = myId
                              , fnPublicPort = publicPort
                              , fnTargetId = targetId
                              }
      forM_ peers $ \(targetDist, peer) -> sendRequest pd findNode peer
        (atomically . writeTQueue queue $ Failure targetDist peer)
        (atomically . writeTQueue queue . Success peer)

    processResponses
      :: TQueue Reply
      -> MVar (M.Map Distance Node)
      -> Int
      -> M.Map Distance Node
      -> S.Set PeerId
      -> IO (M.Map Distance Node, S.Set PeerId)
    processResponses queue queried = innerLoop
      where
        innerLoop
          :: Int
          -> M.Map Distance Node
          -> S.Set PeerId
          -> IO (M.Map Distance Node, S.Set PeerId)
        innerLoop pending closest failed = case pending of
          -- If there are no more pending replies, we completed the round.
          0 -> return (closest, failed)
          _ -> do
            reply <- atomically (readTQueue queue)
            case reply of
              -- We got the list of peers from the recipient. Put the recipient
              -- into the routing table, update our list of peers closest to the
              -- target and mark the peer as queried.
              Success peer (ReturnNodes peers) -> do
                -- We successfully contacted (and thus authenticated) the peer,
                -- so it's safe to put him into the routing table.
                modifyMVarP_ pdRoutingTable $ unsafeInsertPeer pdConfig peer

                let newClosest = updateClosestWith failed closest peers
                -- If the closest peer changed, send another round of FindNode
                -- requests. Note that it's safe to call findMin here as closest
                -- can't be empty (we wouldn't be here if it was) and we just
                -- received peers, so newClosest also can't be empty.
                newPending <- case M.findMin closest == M.findMin newClosest of
                  True  -> return $ pending - 1
                  False -> do
                    chosen <- peersToQuery queried (configAlpha pdConfig) closest
                    sendFindNodeRequests queue chosen
                    return $ pending + length chosen - 1

                innerLoop newPending newClosest failed

              -- If FindNode request failed, remove the recipient from the list
              -- of closest peers and mark it as failed so that we won't add it
              -- to the list of closest peers again during the rest of the
              -- lookup.
              Failure targetDist peer -> do
                modifyMVarP_ pdRoutingTable $ timeoutPeer peer
                innerLoop (pending - 1) (M.delete targetDist closest)
                          (S.insert (nodeId peer) failed)

        updateClosestWith
          :: S.Set PeerId
          -> M.Map Distance Node
          -> [Node]
          -> M.Map Distance Node
        updateClosestWith failed closest =
          -- We need to keep more than k peers on the list. If we keep k, then
          -- the following might happen: we're in the middle of the lookup, we
          -- send queries to alpha closest peers. We get the responses, closest
          -- peer stays the same. We then send queries to all of the remaining k
          -- peers we didn't yet query. One or more of them fails (and we'll
          -- usually handle failure (timeout) as the last event, so the list of
          -- closest peers will not be updated anymore during this round). We
          -- remove it from the list of closest peers and we're ready for the
          -- next round to fill the gap, but now we don't have anyone left to
          -- query (because we just did) and we also have less than k closest
          -- peers.
          M.take ((configAlpha pdConfig + 1) * configK pdConfig) . foldr f closest
          where
            f peer acc =
              -- If a peer failed to return a response during lookup at any
              -- point, we won't consider it a viable candidate for the whole
              -- lookup duration even if other peers keep returning it.
              if nodeId peer `S.member` failed
              then acc
              else M.insert (distance targetId $ nodeId peer) peer acc

----------------------------------------

-- | Handle appropriate 'Request'.
handleRequest :: PeerDiscovery cm -> Peer -> RpcId -> Request -> IO ()
handleRequest pd@PeerDiscovery{..} peer rpcId req = case req of
  FindNodeR FindNode{..} -> do
    peers <- modifyMVar pdRoutingTable $ \oldTable -> do
      let mnode = fnPublicPort <&> \port ->
            Node { nodeId   = fnPeerId
                 , nodePeer = peer { peerPort = port }
                 }
      -- If we got a port number, we assume that peer is globally reachable
      -- under his IP address and received port number, so we insert him into
      -- our routing table. In case he lied it's not a big deal, he either won't
      -- make it or will be evicted soon.
      !table <- atomically (readTVar pdBootstrapState) >>= \case
        -- Do not modify the routing table until bootstrap was completed. This
        -- prevents an attacker from spamming us with requests before or during
        -- bootstrap phase and possibly gaining large influence in the routing
        -- table.
        BootstrapNeeded     -> return oldTable
        BootstrapInProgress -> return oldTable
        BootstrapDone       -> case mnode of
          -- If it comes to nodes who send us requests, we only insert them into
          -- the table if the highest bit of their id is different than
          -- ours. This way a potential adversary:
          --
          -- 1) Can't directly influence our neighbourhood by flooding us with
          -- reqeusts from nodes that are close to us.
          --
          -- 2) Will have a hard time getting a large influence in our routing
          -- table because the branch representing different highest bit
          -- accounts for half of the network, so its buckets will most likely
          -- be full.
          Just node
            | testPeerIdBit fnPeerId 0 /= testPeerIdBit (rtId oldTable) 0 ->
              case insertPeer pdConfig node oldTable of
                Right newTable -> return newTable
                Left oldNode -> do
                  -- Either the node address changed or we're dealing with an
                  -- impersonator, so we only update the address if we don't get
                  -- a response from the old address and we get a response from
                  -- the new one. Note that simply pinging the new address is
                  -- not sufficient, as an impersonator can forward ping request
                  -- to the existing node and then forward his response back to
                  -- us. He won't be able to modify the subsequent traffic
                  -- (because he can't respond to requests on its own as he
                  -- lacks the appropriate private kay), but he can block it.
                  sendRequest pd (Ping Nothing) oldNode
                    (sendRequest pd (Ping Nothing) node
                      (return ())
                      (\Pong ->
                         modifyMVarP_ pdRoutingTable $ unsafeInsertPeer pdConfig node))
                    (\Pong -> return ())
                  return oldTable
            | otherwise ->
              -- If the highest bit is the same, we at most reset timeout count
              -- of the node if it's in our routing table.
              return $ clearTimeoutPeer node oldTable
          _ -> return oldTable
      return (table, findClosest (configK pdConfig) fnTargetId table)
    sendResponse peer $ ReturnNodesR (ReturnNodes peers)
  PingR Ping{..} ->
    -- If port number was specified, respond there.
    let receiver = maybe peer (\port -> peer { peerPort = port }) pingReturnPort
    in sendResponse receiver $ PongR Pong
  where
    sendResponse receiver rsp =
      let signature = C.sign pdSecretKey pdPublicKey (toMessage rpcId req rsp)
      in sendTo pdCommInterface receiver $ Response rpcId pdPublicKey signature rsp

-- | Perform routing table maintenance by testing connectivity of nodes that
-- failed to respond to FindNode request by periodically sending them
-- subsequent, random FindNode requests (note that we can't use Ping requests
-- for that as in principle a node might ignore all FindNode requests, but
-- respond to Ping request and occupy a space in our routing table while being
-- useless).
--
-- If any of them consecutively fails to respond a specific number of times, we
-- then check whether the replacement cache of the corresponding bucket is not
-- empty and replace the node in question with the first node from the cache
-- that responds (if replacement cache is empty, we leave the node be).
--
-- Note that the whole maintenance process is strategically constructed so that
-- in case of network failure (i.e. no node responds to requests) we don't
-- change the structure of any bucket (apart from increasing timeout counts of
-- nodes).
performRoutingTableMaintenance :: PeerDiscovery cm -> IO ()
performRoutingTableMaintenance pd@PeerDiscovery{..} = do
  findNode <- do
    myId <- withMVarP pdRoutingTable rtId
    port <- readMVar pdPublicPort
    return $ \nid -> FindNode { fnPeerId     = myId
                              , fnPublicPort = port
                              , fnTargetId   = nid
                              }
  modifyMVar_ pdRoutingTable $ \table -> do
    -- TODO: might use forConcurrently here to speed things up.
    tree <- F.forM (rtTree table) $ \bucket -> do
      queue <- newTQueueIO
      let timedout = Seq.foldrWithIndex
            (\i ni acc -> if niTimeoutCount ni > 0
                          then (i, ni) : acc
                          else           acc)
            []
            (bucketNodes bucket)
      F.forM_ timedout $ \(i, ni@NodeInfo{..}) -> do
        targetId <- randomPeerId
        sendRequest pd (findNode targetId) niNode
          (      atomically $ writeTQueue queue (i, ni, False))
          (\_ -> atomically $ writeTQueue queue (i, ni, True))
      updateBucket findNode queue (length timedout) bucket Nothing
    return table { rtTree = tree }
  where
    updateBucket
      :: (PeerId -> FindNode)
      -> TQueue (Int, NodeInfo, Bool)
      -> Int
      -> Bucket
      -> Maybe (Seq.Seq (Node, Bool))
      -> IO Bucket
    updateBucket _ _ 0 bucket mcache = case mcache of
      -- If there were no attempts to ping the cache, no node timed out enough
      -- times to be considered for eviction, so just return the updated bucket.
      Nothing -> return bucket
      -- If some nodes timed out enough times to be considered for eviction,
      -- replace the old cache. We ignore whether nodes in cache were alive or
      -- not as it doesn't matter; they will either be ignored during the next
      -- iteration or replaced by new incoming nodes.
      Just cache -> return bucket { bucketCache = fst <$> cache }
    updateBucket findNode queue k bucket mcache = do
      (i, NodeInfo{..}, respondedCorrectly) <- atomically $ readTQueue queue
      if | respondedCorrectly -> updateBucket findNode queue (k - 1)
                                              (clearTimeoutPeerBucket niNode bucket)
                                              mcache
         | niTimeoutCount >= configMaxTimeouts pdConfig -> do
             cache <- case mcache of
               Just cache -> return cache
               Nothing    -> forConcurrently (bucketCache bucket) $ \node -> do
                 targetId <- randomPeerId
                 (node, ) <$> sendRequestSync pd (findNode targetId) node
                   (      return False)
                   (\_ -> return True)
             let (dead, maybeHasAlive) = Seq.breakl snd cache
             case Seq.viewl maybeHasAlive of
               (alive, _) Seq.:< rest ->
                 -- Pick the first alive node in the cache and replace the dead
                 -- one in the bucket with it.
                 let newNodeInfo = NodeInfo
                       { niNode         = alive
                       , niTimeoutCount = 0
                       }
                     newBucket = bucket
                       { bucketNodes = Seq.update i newNodeInfo (bucketNodes bucket)
                       }
                 in updateBucket findNode queue (k - 1) newBucket
                                 (Just $ dead Seq.>< rest)
               Seq.EmptyL ->
                 -- All nodes in the replacement cache are dead - most likely
                 -- explanation is network failure, so we don't do anything in
                 -- this case.
                 updateBucket findNode queue (k - 1) bucket (Just cache)
         | otherwise -> updateBucket findNode queue (k - 1)
                                     (timeoutPeerBucket niNode bucket)
                                     mcache
