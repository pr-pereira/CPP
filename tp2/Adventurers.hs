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
  show s = show . show $ [s (Left P1),
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

state2List :: State -> [Bool]
state2List s = [s (Left P1),
             s (Left P2),
             s (Left P5),
             s (Left P10),
             s (Right ())]

indexesWithDifferentValues :: Eq a => ([a], [a]) -> [Int]
-- Example : indexesWithDifferentValues [1,2,3,4] [10,2,23,4] = [0,2]
indexesWithDifferentValues (l1, l2) = aux l1 l2 0 where
  aux :: Eq a => [a] -> [a] -> Int -> [Int]
  aux [] l _ = []
  aux l [] _ = []
  aux (h1:t1) (h2:t2) index = if h1 /= h2 then index : aux t1 t2 (index + 1)
                             else aux t1 t2 (index + 1)

-- pre-condition: list length is even
pairConsecutiveElements :: [a] -> [(a,a)]
pairConsecutiveElements [] = []
pairConsecutiveElements [x] = []
pairConsecutiveElements (x1:x2:xs) = (x1,x2) : pairConsecutiveElements (x2:xs) 

index2Adv :: Int -> String
index2Adv 0 = "P1"
index2Adv 1 = "P2"
index2Adv 2 = "P5"
index2Adv 3 = "P10"

prettyLog :: [String] -> String
prettyLog = Cp.cond ((>1) . length) f ((++ " cross\n") . head) where
    f = (++" crosses\n") . conc . ((concat . map (++" and ")) >< id) . (split init last)

printTrace :: [[Bool]] -> String
printTrace = concat . (map prettyLog) . (map ((map index2Adv) . 
             init . indexesWithDifferentValues)) . pairConsecutiveElements

-- Changes the state of the game for a given object
changeState :: Object -> State -> State
changeState a s = let v = s a in (\x -> if x == a then not v else s x)

-- Changes the state of the game of a list of Object 
mChangeState :: [Object] -> State -> State
mChangeState os s = foldr changeState s os


{-- For a given state of the game, the function presents all the
possible moves that the adventurers can make.  --}
allValidPlays :: State -> ListLogDur State
allValidPlays s = LSD $ map Duration $ map (id >< (split (toTrace s) id) . (mCS s)) t where
  t = (map (addLantern . addTime) . combinationsUpTo2 . advsWhereLanternIs) s
  mCS = flip mChangeState
  toTrace s = printTrace . ((state2List s) :) . singl . state2List

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
exec :: Int -> State -> ListLogDur State
exec 0 s = allValidPlays s
exec n s = do ps <- exec (n-1) s
              allValidPlays ps

-- executa até chegar a um estado que cumpra um determinado predicado
execPred :: (State -> Bool) -> Bool -> ListLogDur State
execPred = undefined

{-- Is it possible for all adventurers to be on the other side
in <=17 min and not exceeding 5 moves ? --}
leq17 :: Bool
leq17 = leq' 17 0 || leq' 17 1 || leq' 17 2 || leq' 17 3 || leq' 17 4 where
        leq' n i = leqList n . map fst . filter p . map remDur . remLSD $ exec i gInit
        p (_, (_,s)) = s == gEnd
        remDur (Duration a) = a
        leqList x [] = False
        leqList x (h:t) = h <= x || leqList x t

leqX :: Int -> (Int, Bool)
leqX = undefined

-- lX é igual a leqX mas em vez de ser <= é apenas <
lX :: Int -> (Int, Bool)
lX = undefined

-- este trace é específico para 4 execuções e um estado igual a gEnd com duração 17 min.
trace :: IO ()
trace = putStr . p1 . p2 . head . filter p . map remDur . remLSD $ exec 4 gInit where
        p (d, (_,s)) = d == 17 && s == gEnd
        remDur (Duration a) = a
        addInitSt = ((state2List gInit) :)

{-- Is it possible for all adventurers to be on the other side
in < 17 min ? --}
l17 :: Bool
l17 = undefined



