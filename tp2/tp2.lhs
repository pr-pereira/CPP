\documentclass[a4paper]{article}
\usepackage[a4paper,left=15mm,right=15mm,top=15mm,bottom=15mm]{geometry}
\usepackage{palatino}
\usepackage[colorlinks=true,linkcolor=blue,citecolor=blue]{hyperref}
\usepackage{graphicx}
\usepackage{tp2}
\usepackage{subcaption}
\usepackage{adjustbox}
\usepackage{color}

\definecolor{red}{RGB}{255,  0,  0}
\definecolor{blue}{RGB}{0,0,255}
\def\red{\color{red}}
\def\blue{\color{blue}}

%================= lhs2tex=====================================================%
%include polycode.fmt
%format (div (x)(y)) = x "\div " y
%format succ = "\succ "
%format ==> = "\Longrightarrow "
%format map = "\map "
%format length = "\length "
%format fst = "\p1"
%format p1  = "\p1"
%format snd = "\p2"
%format p2  = "\p2"
%format Left = "i_1"
%format Right = "i_2"
%format i1 = "i_1"
%format i2 = "i_2"
%format >< = "\times"
%format >|<  = "\bowtie "
%format |-> = "\mapsto"
%format . = "\comp "
%format .=?=. = "\mathbin{\stackrel{\mathrm{?}}{=}}"
%format (kcomp (f)(g)) = f "\kcomp " g
%format -|- = "+"
%format conc = "\mathsf{conc}"
%format summation = "{\sum}"
%format (either (a) (b)) = "\alt{" a "}{" b "}"
%format (frac (a) (b)) = "\frac{" a "}{" b "}"
%format (uncurry f) = "\uncurry{" f "}"
%format (const (f)) = "\underline{" f "}"
%format (lcbr (x)(y)) = "\begin{lcbr}" x "\\" y "\end{lcbr}"
%format (split (x) (y)) = "\conj{" x "}{" y "}"
%format (for (f) (i)) = "\for{" f "}\ {" i "}"
%format B_tree = "\mathsf{B}\mbox{-}\mathsf{tree} "
%format <$> = "\mathbin{\mathopen{\langle}\$\mathclose{\rangle}}"
%format Either a b = a "+" b
%format fmap = "\mathsf{fmap}"
%format NA   = "\textsc{na}"
%format NB   = "\textsc{nb}"
%format inT = "\mathsf{in}"
%format outT = "\mathsf{out}"
%format outLTree = "\mathsf{out}"
%format inLTree = "\mathsf{in}"
%format inFTree = "\mathsf{in}"
%format outFTree = "\mathsf{out}"
%format Null = "1"
%format (Prod (a) (b)) = a >< b
%format fF = "\fun F "
%format k1 = "k_1 "
%format k2 = "k_2 "
%format h1 = "h_1 "
%format h2 = "h_2 "
%format f1 = "f_1 "
%format f2 = "f_2 "
%format l1 = "l_1 "
%format P1 = "P_1 "
%format P2 = "P_2 "
%format P5 = "P_5 "
%format P10 = "P_{10} "
%format map1 = "map_1 "
%format map2 = "map_2 "
%format map3 = "map_3"
%format l2 = "l_2 "
%format Dist = "\fun{Dist}"
%format IO = "\fun{IO}"
%format LTree = "{\LTree}"
%format FTree = "{\FTree}"
%format inNat = "\mathsf{in}"
%format (cata (f)) = "\cata{" f "}"
%format (cataNat (g)) = "\cataNat{" g "}"
%format (cataList (g)) = "\cataList{" g "}"
%format (anaList (g)) = "\anaList{" g "}"
%format Nat0 = "\N_0"
%format Rational = "\Q "
%format toRational = " to_\Q "
%format fromRational = " from_\Q "
%format muB = "\mu "
%format (frac (n)(m)) = "\frac{" n "}{" m "}"
%format (fac (n)) = "{" n "!}"
%format (underbrace (t) (p)) = "\underbrace{" t "}_{" p "}"
%format matrix = "matrix"
%format (bin (n) (k)) = "\Big(\vcenter{\xymatrix@R=1pt{" n "\\" k "}}\Big)"
%format `ominus` = "\mathbin{\ominus}"
%format % = "\mathbin{/}"
%format <-> = "{\,\leftrightarrow\,}"
%format <|> = "{\,\updownarrow\,}"
%format `minusNat`= "\mathbin{-}"
%format ==> = "\Rightarrow"
%format .==>. = "\Rightarrow"
%format .<==>. = "\Leftrightarrow"
%format .==. = "\equiv"
%format .<=. = "\leq"
%format .&&&. = "\wedge"
%format cdots = "\cdots "
%format pi = "\pi "
%format <= = "\leq"
%format (curry (f)) = "\overline{" f "}"
%format (cataLTree (x)) = "\llparenthesis\, " x "\,\rrparenthesis"
%format (cataFTree (x)) = "\llparenthesis\, " x "\,\rrparenthesis"
%format (anaLTree (x)) = "\mathopen{[\!(}" x "\mathclose{)\!]}"
%format delta = "\Delta "
\newlabel{eq:fokkinga}{{3.93}{110}{The mutual-recursion law}{section.3.17}{}}
%format (plus (f)(g)) = "{" f "}\plus{" g "}"
%format ++ = "\mathbin{+\!\!\!+}"
%format Integer  = "\mathbb{Z}"
\def\plus{\mathbin{\dagger}}
\def\ana#1{\mathopen{[\!(}#1\mathclose{)\!]}}

%---------------------------------------------------------------------------

\begin{document}

\setlength\parindent{0pt}

\title{\bfseries Modelling and Analysis of a Cyber-Physical System \\ {\Large Cyber-Physical Programming --- Practical Assignment 1}}

\author{
    Melânia Pereira \quad\quad Paulo R. Pereira\\\texttt{\{pg47520, pg47554\}@@alunos.uminho.pt}
}

\maketitle

%if False
\begin{code}
{-# OPTIONS_GHC -XNPlusKPatterns #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveDataTypeable, FlexibleInstances #-}
module Adventurers where

import DurationMonad
import Cp
import Nat
import List
\end{code}
%endif

In the middle of the night, four adventurers encounter a shabby rope-bridge spanning a deep ravine.
For safety reasons, they decide that no more than 2 people should cross the bridge at the same
time and that a flashlight needs to be carried by one of them in every crossing. They have only
one flashlight. The 4 adventurers are not equally skilled: crossing the bridge takes them 1, 2, 5,
and 10 minutes, respectively. A pair of adventurers crosses the bridge in an amount of time equal
to that of the slowest of the two adventurers.

The list of adventurers
\begin{code}
data Adventurer = P1 | P2 | P5 | P10 deriving (Show,Eq)
\end{code}

\begin{code}
type Objects = Either Adventurer ()
\end{code}
The time that each adventurer needs to cross the bridge
\begin{code}
getTimeAdv :: Adventurer -> Int
getTimeAdv P1 = 1
getTimeAdv P2 = 2
getTimeAdv P5 = 5
getTimeAdv P10 = 10
\end{code}

The state of the game, i.e. the current position of each adventurer
+ the lantern. The function (const False) represents the initial state
of the game, with all adventurers and the lantern on the left side of
the bridge. Similarly, the function (const True) represents the end
state of the game, with all adventurers and the lantern on the right
side of the bridge.
\begin{code}
type State = Objects -> Bool

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


\end{code}
The initial state of the game
\begin{code}
gInit :: State
gInit = const False
\end{code}

Changes the state of the game for a given object
\begin{code}
changeState :: Objects -> State -> State
changeState a s = let v = s a in (\x -> if x == a then not v else s x)
\end{code}

Changes the state of the game of a list of objects
\begin{code}
mChangeState :: [Objects] -> State -> State
mChangeState os s = foldr changeState s os
\end{code}                             

For a given state of the game, the function presents all the
possible moves that the adventurers can make.
\begin{code}
allValidPlays :: State -> ListDur State
allValidPlays = undefined
\end{code}

For a given number n and initial state, the function calculates
all possible n-sequences of moves that the adventures can make
\begin{code}
exec :: Int -> State -> ListDur State
exec = undefined
\end{code}

Is it possible for all adventurers to be on the other side
in |<=| 17 min and not exceeding 5 moves ?
\begin{code}
leq17 :: Bool
leq17 = undefined
\end{code}

Is it possible for all adventurers to be on the other side
in $<$ 17 min ?
\begin{code}
l17 :: Bool
l17 = undefined
\end{code}

Implementation of the monad used for the problem of the adventurers.
Recall the Knight's quest.

\begin{code}
data ListDur a = LD [Duration a] deriving Show

remLD :: ListDur a -> [Duration a]
remLD (LD x) = x

instance Functor ListDur where
   fmap f = undefined

instance Applicative ListDur where
   pure x = undefined
   l1 <*> l2 = undefined

instance Monad ListDur where
   return = undefined
   l >>= k = undefined

manyChoice :: [ListDur a] -> ListDur a
manyChoice = LD . concat . (map remLD)
\end{code}

%----------------- Apêndice ---------------------------------------------------%
\appendix



%----------------- Índice remissivo (exige makeindex) -------------------------%

%\printindex

%----------------- Bibliografia (exige bibtex) --------------------------------%

%\bibliographystyle{plain}
%\bibliography{tp2}

%----------------- Fim do documento -------------------------------------------%
\end{document}
