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



--------------------------------------------------------------------------
-- Initial version - not very efficient because we are always comparing
-- the adventurer state with the lantern state
allValidPlays2 :: State -> ListDur State
allValidPlays2 st = rmEmptyMoves $ manyChoice $ 
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
--------------------------------------------------------------------------


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
        leq' n i = leqList n $ map fst $ filter p $ map remDur $ remLD $ exec i gInit
        p (_, s) = s == gEnd
        remDur (Duration a) = a
        leqList x [] = False
        leqList x (h:t) = h <= x || leqList x t

{-- Is it possible for all adventurers to be on the other side
in < 17 min ? --}
-- To implement
l17 :: Bool
l17 = undefined

-- é necessário provar que não é possível... como se prova? ainda não sei


--------------------------------------------------------------------------
{-- Implementation of the monad used for the problem of the adventurers.
Recall the Knight's quest --}

data ListDur a = LD [Duration a] deriving Show

remLD :: ListDur a -> [Duration a]
remLD (LD x) = x

instance Functor ListDur where
    fmap f = LD . (map (fmap f)) . remLD

instance Applicative ListDur where
    pure = LD . pure . pure
    l1 <*> l2 = LD $ do x <- remLD l1
                        y <- remLD l2
                        g(x, y) where
                        g(Duration (d1, f), Duration (d2, x)) =
                          return $ Duration (d1 + d2, f x)

instance Monad ListDur where
    return = pure
    l >>= k = LD $ do
      x <- remLD l
      g x where
        g (Duration (d, a)) = 
          map (\(Duration (d', a)) -> (Duration (d + d', a))) (remLD (k a))

manyChoice :: [ListDur a] -> ListDur a
manyChoice = LD . concat . (map remLD)
--------------------------------------------------------------------------


--------------------------------------------------------------------------
{-- monad para ter um trace das jogadas --}

data ListDurLogList a = LSD [Duration (String, a)] deriving Show

remLSD :: ListDurLogList a -> [Duration (String, a)]
remLSD (LSD x) = x

{-
k : a -> b
fmap k : Duration a -> Duration b
g : (String, Duration a) -> (String, Duration b)
g = id >< (fmap k)
map g : [(String, Duration a)] -> [(String, Duration b)]
-}
instance Functor ListDurLogList where
    fmap f = LSD . (map (fmap (id >< f))) . remLSD

instance Applicative ListDurLogList where
    pure = LSD . pure . pure . (\x -> ("", x))
    l1 <*> l2 = undefined

instance Monad ListDurLogList where
    return = pure
    l >>= k = let k' = LD . remLSD . k
                  l' = (LD . remLSD) l in
                  LSD $ remLD (l' >>= (auxLSDMonad k'))


auxLSDMonad :: (x -> ListDur (String, y)) -> ((String, x) -> ListDur (String, y))
auxLSDMonad = undefined


{-
k : X -> ListDurLogList Y
-----------------------------------------
k* : ListDurLogList X -> ListDurLogList Y    (definir)



k : X -> ListDur Y
---------------------------
k* : ListDur X -> ListDur Y   (já está definida)


k : X -> ListDur(S x Y)   LD [Duration (String,a)]
-------------------------
h : S x X -> ListDur(S x Y)
-------------------------------------
h* : ListDur(S x X) -> ListDur(S x Y)
-}