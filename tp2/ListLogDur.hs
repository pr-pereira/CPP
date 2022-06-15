module ListLogDur where

import Cp
import DurationMonad
import ListDur

data ListLogDur a = LSD [Duration (String, a)] deriving Show

remLSD :: ListLogDur a -> [Duration (String, a)]
remLSD (LSD x) = x

{-
k : a -> b
fmap k : Duration a -> Duration b
g : (String, Duration a) -> (String, Duration b)
g = id >< (fmap k)
map g : [(String, Duration a)] -> [(String, Duration b)]
-}
instance Functor ListLogDur where
    fmap f = LSD . (map (fmap (id >< f))) . remLSD

instance Applicative ListLogDur where
    pure = LSD . pure . pure . (\x -> ("", x))
    l1 <*> l2 = undefined

instance Monad ListLogDur where
    return = pure
    l >>= k = let k' = LD . remLSD . k
                  l' = (LD . remLSD) l in
                  LSD $ remLD (l' >>= (auxLSDMonad k')) where
                    auxLSDMonad :: (x -> ListDur (String, y)) -> ((String, x) -> ListDur (String, y))
                    auxLSDMonad = undefined


{-
k : X -> ListLogDur Y
-----------------------------------------
k* : ListLogDur X -> ListLogDur Y    (definir)



k : X -> ListDur Y
---------------------------
k* : ListDur X -> ListDur Y   (já está definida)


k : X -> ListDur(S x Y)   LD [Duration (String,a)]
-------------------------
h : S x X -> ListDur(S x Y)
-------------------------------------
h* : ListDur(S x X) -> ListDur(S x Y)
-}