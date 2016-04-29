{-# LANGUAGE ScopedTypeVariables #-}

module RegAlloc where

import Prelude
import qualified LLIR
import Data.Sequence
import Data.Foldable (toList)

data Stack a = Stack [a] deriving Show

emptyStack :: Stack a
emptyStack = Stack []

push :: Stack a -> a -> Stack a
push (Stack xs) x = Stack (x:xs)

pop :: Stack a -> (a, Stack a)
pop (Stack (x:xs)) = (x, Stack xs)

data Node = Node {
  uid :: Int,
  color :: Maybe Int,
  spilled :: Bool
} deriving Show

emptyNode :: Int -> Node
emptyNode i = Node i Nothing False

spilledNode :: Int -> Node
spilledNode i = Node i Nothing True

colorNode :: Node -> Int -> Node
colorNode (Node n _ _) c = Node n (Just c) False

data Graph = Graph {
  matrix :: Seq (Seq Bool),
  list :: Seq (Seq Node),
  nodes :: Seq Bool
  colors :: Seq Int
} deriving Show

initGraph :: Int -> Graph
initGraph n = Graph (Data.Sequence.replicate n (Data.Sequence.replicate n False)) (Data.Sequence.replicate n Data.Sequence.empty) (Data.Sequence.replicate n True) (Data.Sequence.replicate n -1)

numNodes :: Graph -> Int
numNodes g = Data.Sequence.length . Data.Sequence.filter (\x -> x) $ nodes g

addNeighbor :: Graph -> Node -> Node -> Graph
addNeighbor g n1 n2 = 
  let matrix1 = update (uid n1) (update (uid n2) True (index (matrix g) (uid n1))) (matrix g) 
      matrix2 = update (uid n2) (update (uid n1) True (index matrix1 (uid n2))) (matrix1)
      list1 = update (uid n2) (index (list g) (uid n2) |> n1) (list g)
      list2 = update (uid n1) (index list1 (uid n1) |> n2) (list1) in
        Graph matrix2 list2 (nodes g) (colors g)

isNeighbor :: Graph -> Node -> Node -> Bool
isNeighbor g n1 n2 = index (index (matrix g) (uid n2)) (uid n1)

numNeighbors :: Graph -> Node -> Int
numNeighbors g n = Data.Sequence.length $ getNeighbors g n

removeNode :: Graph -> Node -> Graph
-- removeNode g n =
--   let matrix1 = update n (Data.Sequence.replicate (nodes g) False) $ matrix g
--       matrix2 = fmap (\list -> update (uid n) False list) matrix1
--       list1 = fmap (\list -> Data.Sequence.filter (\a -> (uid a) /= n) list) $ list g
--       nodes1 = update n False $ nodes g in
--         Graph matrix2 list1 nodes1
removeNode g n =
  let nodes1 = update (uid n) False $ nodes g in
    Graph (matrix g) (list g) nodes1 (colors g)

-- isEmpty :: Graph -> Bool
-- isEmpty g = foldl (&&) (nodes g) True

restoreNode :: Graph -> Node -> Graph
restoreNode g n =
  let nodes1 = update (uid n) True $ nodes g
      colors1 = update (uid n) (color n) $ colors g in
    Graph (matrix g) (list g) nodes1 colors1

getPresentNodes :: Graph -> Seq Int
getPresentNodes g = fmap (\(i, present) -> i) (Data.Sequence.filter (\(i, present) -> present) $ Data.Sequence.zip (fromList [1..(Data.Sequence.length $ nodes g)]) (nodes g))

getNeighbors :: Graph -> Node -> Seq Node
getNeighbors g n = Data.Sequence.filter (\x -> uid x `elem` getPresentNodes g) $ index (list g) (uid n)

neighborColors :: Graph -> Node -> Seq Int
neighborColors g n = fmap (\x -> case color x of 
                          Just i -> i 
                          Nothing -> -1) $ getNeighbors g n

-- so janky. removes nodes with less than k neighbors until there are no
-- more, but will also remove nodes with degree more than k (optimistic
-- approach)
simplifyGraph :: Graph -> Stack Node -> Int -> (Graph, Stack Node)
simplifyGraph g (Stack []) k = (g, emptyStack)
simplifyGraph g s k = 
  let (simplified, stack, removed) = foldl  (\(graph, stack, removed) i -> 
                                                if removed then (graph, stack, removed) else
                                                           if numNeighbors g (emptyNode i) < k then (removeNode graph (emptyNode i), push stack $ emptyNode i, True) else (graph, stack, False))
                                            (g, s, False)
                                            (getPresentNodes g) in 
                                              if removed then simplifyGraph simplified stack k else
                                                         let remove = index (getPresentNodes g) 0 in
                                                            simplifyGraph (removeNode g (emptyNode remove)) (push stack $ emptyNode remove) k

-- implements the select phase. pops off the node stack, tries to color
-- the node, if it can't puts it in the spilled array. at the end, if
-- there's anything in the spilled array, returns the array; otherwise
-- everything got colored and return the colored graph
colorGraph :: Graph -> Stack Node -> [Node] -> Int -> Either [Node] Graph
colorGraph g (Stack []) [] k = Right g
colorGraph _ (Stack []) spilled k = Left spilled
colorGraph g s spilled k =
  let (nextNode, s1)  = pop s
      neighbors = neighborColors g nextNode
      colors = Prelude.filter (\x -> case x `elemIndexL` neighbors of
                               Just i  -> True
                               Nothing -> False)
                      [1..k] in
                        if Prelude.length colors > 0 then colorGraph (restoreNode g . colorNode nextNode $ colors !! 0) s1 spilled k else
                                             colorGraph g s1 (spilled ++ [nextNode]) k
