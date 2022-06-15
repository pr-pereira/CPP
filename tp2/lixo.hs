teste2 :: (x -> ListDur (String, y)) -> (ListDur (String, x) -> ListDur (String, y))
teste2 f = let f' = teste f in kleisli f'

kleisli :: Monad m => (a -> m b) -> m a -> m b
kleisli = flip (>>=)