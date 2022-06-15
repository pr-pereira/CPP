teste2 :: (x -> ListDur (String, y)) -> (ListDur (String, x) -> ListDur (String, y))
teste2 f = let f' = teste f in kleisli f'

kleisli :: Monad m => (a -> m b) -> m a -> m b
kleisli = flip (>>=)

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