{-# LANGUAGE FlexibleInstances #-}
module Adventurers where

import Cp
import DurationMonad
import ListDur
import ListLogDur

-- The list of adventurers
data Adventurer = P1 | P2 | P5 | P10 deriving (Show,Eq)
-- Adventurers + the lantern
type Object = Either Adventurer ()

lantern = Right ()

-- The time that each adventurer needs to cross the bridge
-- To implement 
getTimeAdv :: Adventurer -> Int
getTimeAdv P1 = 1
getTimeAdv P2 = 2
getTimeAdv P5 = 5
getTimeAdv P10 = 10

{-- The state of the game, i.e. the current position of each adventurer
+ the lantern. The function (const False) represents the initial state
of the game, with all adventurers and the lantern on the left side of
the bridge. Similarly, the function (const True) represents the end
state of the game, with all adventurers and the lantern on the right
side of the bridge.  --}
type State = Object -> Bool

instance Show State where
  show s = (show . (fmap show)) [s (Left P1),
                                 s (Left P2),
                                 s (Left P5),
                                 s (Left P10),
                                 s (Right ())]

instance Eq State where
  (==) s1 s2 = and [s1 (Left P1) == s2 (Left P1),
                    s1 (Left P2) == s2 (Left P2),
                    s1 (Left P5) == s2 (Left P5),
                    s1 (Left P10) == s2 (Left P10),
                    s1 (Right ()) == s2 (Right ())]



-- The initial state of the game
gInit :: State
gInit = const False

-- The end state of the game
gEnd :: State
gEnd = const True


-- state for testing
st :: State
st (Left P1) = False
st (Left P2) = True
st (Left P5) = True
st (Left P10) = True
st ln = False


-- Changes the state of the game for a given object
changeState :: Object -> State -> State
changeState a s = let v = s a in (\x -> if x == a then not v else s x)

-- Changes the state of the game of a list of Object 
mChangeState :: [Object] -> State -> State
mChangeState os s = foldr changeState s os
                               
-- moves that take 0 minutes is an empty move 
rmEmptyMoves :: ListDur State -> ListDur State
rmEmptyMoves = LD . (filter g0) . remLD where
               g0 (Duration (0, _)) = False
               g0 _ = True

{-- For a given state of the game, the function presents all the
possible moves that the adventurers can make.  --}
allValidPlays :: State -> ListDur State
allValidPlays s = LD $ map Duration $ map (id >< (mCS s)) t where
  t = (map (addLantern . addTime) . combinationsUpTo2 . advsWhereLanternIs) s
  mCS = flip mChangeState

addTime :: [Adventurer] -> (Int, [Adventurer])
addTime = split (maximum . (map getTimeAdv)) id

addLantern :: (Int, [Adventurer]) -> (Int, [Object])
addLantern = id >< ((lantern :) . map Left)

advsWhereLanternIs :: State -> [Adventurer]
advsWhereLanternIs s = filter ((== s lantern) . s . Left) [P1, P2, P5, P10]

combinationsUpTo2 :: Eq a => [a] -> [[a]]
-- example : combinationsUpTo2 [1,2,3] = [[1], [2], [3], [1,2], [1,3], [2,3]]
combinationsUpTo2 = conc . (split f g) where
      f t = do {x <- t; return [x]}
      g t = do {x <- t; y <- (remove x t); return [x, y]}
      remove x [] = []
      remove x (h:t) = if x==h then t else remove x t

{-- For a given number n and initial state, the function calculates
all possible n-sequences of moves that the adventures can make --}
-- To implement 
exec :: Int -> State -> ListDur State
exec 0 s = allValidPlays s
exec n s = do ps <- exec (n-1) s
              allValidPlays ps 

{-- Is it possible for all adventurers to be on the other side
in <=17 min and not exceeding 5 moves ? --}
-- To implement
--leq17 :: Bool
leq17 = leq' 17 0 ||
        leq' 17 1 ||
        leq' 17 2 ||
        leq' 17 3 ||
        leq' 17 4 where
        leq' n i = leqList n . map fst . filter p . map remDur . remLD $ exec i gInit
        p (_, s) = s == gEnd
        remDur (Duration a) = a
        leqList x [] = False
        leqList x (h:t) = h <= x || leqList x t

{-- Is it possible for all adventurers to be on the other side
in < 17 min ? --}
-- To implement
--l17 :: Bool
l17 = minimum . map fst . filter p . map remDur . remLD $ exec 6 gInit where
      remDur (Duration a) = a
      p (_, s) = s == gEnd






