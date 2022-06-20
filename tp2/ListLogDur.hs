module ListLogDur where

import Cp
import DurationMonad
import ListDur

data ListLogDur a = LSD [Duration (String, a)] deriving Show

instance Functor ListLogDur where
    fmap f = LSD . (map (fmap (id >< f))) . remLSD

instance Applicative ListLogDur where
    pure = LSD . pure . pure . (\x -> ([], x))
    l1 <*> l2 = LSD $ do
        x <- remLSD l1
        y <- remLSD l2
        g(x,y) where
            g(Duration (d1,(s,f)),Duration (d2,(s',x))) = return (Duration (d1 + d2, (s++s', f x)))

instance Monad ListLogDur where
    return = pure
    l >>= k = LSD $ do
      x <- remLSD l
      g x k where
        g (Duration (d, (s, a))) k =
          map (\(Duration (d', (s', a))) -> (Duration (d + d', (s ++ s', a)))) (remLSD (k a))

remLSD :: ListLogDur a -> [Duration (String, a)]
remLSD (LSD x) = x

{-instance Monad ListLogDur where
    return = pure
    l >>= k = let k' = LD . remLSD . k
                  l' = (LD . remLSD) l in
                  LSD $ remLD (l' >>= (auxLSDMonad k')) where
                    auxLSDMonad :: (x -> ListDur (String, y)) -> ((String, x) -> ListDur (String, y))
                    auxLSDMonad = undefined -}