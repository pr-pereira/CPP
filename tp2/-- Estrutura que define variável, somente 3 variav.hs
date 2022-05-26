import Cp

-- (1) Datatype definitions -----------------------------------------------------

data Var = X | Y | Z deriving (Show, Eq)

data LTerm = Leaf (Either Var Double) | Scl Double LTerm | Add LTerm LTerm deriving Show

var = Leaf . Left

t_one = Leaf (Right 1)

data BTerm = L LTerm LTerm | Leq LTerm LTerm | G LTerm LTerm | Geq LTerm LTerm |
             Conj BTerm BTerm | Neg BTerm deriving Show

-- (2) Semantics ---------------------------------------------------------------

lSem :: LTerm -> (Var -> Double) -> Double 
lSem (Leaf (Left v)) m = m v
lSem (Leaf (Right r)) _ = r
lSem (Scl s t) m = s * lSem t m
lSem (Add t1 t2) m = lSem t1 m + lSem t2 m