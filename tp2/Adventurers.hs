{-# LANGUAGE FlexibleInstances #-}
module Adventurers where

import DurationMonad
import Cp

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
st (Left P1) = True
st (Left P2) = False
st (Left P5) = False
st (Left P10) = False
st ln = True


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
-- To implement
allValidPlays :: State -> ListDur State
allValidPlays st = rmEmptyMoves $ manyChoice $ 
                   [advGoesAlone st P1] ++
                   [advGoesAlone st P2] ++
                   [advGoesAlone st P5] ++
                   [advGoesAlone st P10] ++
                   [advsGoTogether st (P1, P2)] ++
                   [advsGoTogether st (P1, P5)] ++
                   [advsGoTogether st (P1, P10)] ++
                   [advsGoTogether st (P2, P5)] ++
                   [advsGoTogether st (P2, P10)] ++
                   [advsGoTogether st (P5, P10)]

-- One adventurer crosses
-- if adventurers cannot grab the lantern, the state remains the same
advGoesAlone :: State -> Adventurer -> ListDur State
advGoesAlone st adv =
      if st (Left adv) == st lantern
      then LD $ [Duration (getTimeAdv adv, mChangeState [Left adv, lantern] st)]
      else return st

-- Two adventurers cross
-- if adventurers cannot grab the lantern, the state remains the same
advsGoTogether :: State -> (Adventurer, Adventurer) -> ListDur State
advsGoTogether st (adv1, adv2) =
      if st (Left adv1) == st (Left adv2) && st (Left adv1) == st lantern
      then LD $
        [Duration (max (getTimeAdv adv1) (getTimeAdv adv2),
         mChangeState [Left adv1, Left adv2, lantern] st)]
      else return st

-- With no monadic effect ------------------------------------------------
allValidPlays' :: State -> [State]
allValidPlays' s = filter (/= s) $
                   [advGoesAlone' s P1] ++
                   [advGoesAlone' s P2] ++
                   [advGoesAlone' s P5] ++
                   [advGoesAlone' s P10] ++
                   [advsGoTogether' s (P1, P2)] ++
                   [advsGoTogether' s (P1, P5)] ++
                   [advsGoTogether' s (P1, P10)] ++
                   [advsGoTogether' s (P2, P5)] ++
                   [advsGoTogether' s (P2, P10)] ++
                   [advsGoTogether' s (P5, P10)]

advGoesAlone' :: State -> Adventurer -> State
advGoesAlone' st adv = if st (Left adv) == st lantern
                       then mChangeState [Left adv, lantern] st
                       else st

advsGoTogether' :: State -> (Adventurer, Adventurer) -> State
advsGoTogether' st (adv1, adv2) =
                if st (Left adv1) == st (Left adv2) && st (Left adv1) == st lantern
                then mChangeState [Left adv1, Left adv2, lantern] st
                else st
--------------------------------------------------------------------------

{-- For a given number n and initial state, the function calculates
all possible n-sequences of moves that the adventures can make --}
-- To implement 
exec :: Int -> State -> ListDur State
exec = undefined

{-- Is it possible for all adventurers to be on the other side
in <=17 min and not exceeding 5 moves ? --}
-- To implement
leq17 :: Bool
leq17 = undefined

{-- Is it possible for all adventurers to be on the other side
in < 17 min ? --}
-- To implement
l17 :: Bool
l17 = undefined


--------------------------------------------------------------------------
{-- Implementation of the monad used for the problem of the adventurers.
Recall the Knight's quest --}

data ListDur a = LD [Duration a] deriving Show

remLD :: ListDur a -> [Duration a]
remLD (LD x) = x

-- To implement
instance Functor ListDur where
   fmap f = let f' = \(Duration (d, x)) -> (Duration (d, f x)) in
    LD . (map f') . remLD

-- To implement
instance Applicative ListDur where
   pure x = LD [Duration (0, x)]
   l1 <*> l2 = LD $ do x <- remLD l1
                       y <- remLD l2
                       g(x, y) where
                        g(Duration (d1, f), Duration (d2, x)) =
                          return $ Duration (d1 + d2, f x)

-- To implement
instance Monad ListDur where
   return = pure
   l >>= k = LD $ do x <- remLD l
                     g x where
                       g (Duration (d, a)) = 
                         map (\(Duration (d', a)) -> (Duration (d + d', a))) (remLD (k a))

manyChoice :: [ListDur a] -> ListDur a
manyChoice = LD . concat . (map remLD)
--------------------------------------------------------------------------
