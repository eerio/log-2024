{-# LANGUAGE UnicodeSyntax, TypeSynonymInstances, FlexibleInstances #-}

import Data.List
import Control.Monad
import Test.QuickCheck
import System.IO.Unsafe

-- updating a function
update :: Eq a => (a -> b) -> a -> b -> a -> b
update ρ x v = \y -> if x == y then v else ρ y

-- useful for debugging
debug :: Show a => String -> a -> a
debug str x = seq (unsafePerformIO $ do putStr "<"; putStr str; putStr ": "; print x; putStr ">") x

todo :: a
todo = undefined

-- propositional variable names are just strings
type PropName = String

data Formula =
      T
    | F
    | Prop PropName -- atomic formulas
    | Not Formula
    | And Formula Formula
    | Or Formula Formula
    | Implies Formula Formula
    | Iff Formula Formula
    deriving (Eq, Show)

infixr 8 /\, ∧
(/\) = And
(∧) = And -- input with "\and"

infixr 5 \/, ∨, ==>
(\/) = Or
(∨) = Or -- input with "\or"
(==>) = Implies

infixr 4 <==>, ⇔
(<==>) = Iff
(⇔) = Iff -- input with "\lr"

p, q, r, s, t :: Formula

p = Prop "p"
q = Prop "q"
r = Prop "r"
s = Prop "s"
t = Prop "t"

satisfiable_formulas = [
    p ∧ q ∧ s ∧ p,
    T,
    p,
    Not p,
    (p ∨ q ∧ r) ∧ (Not p ∨ Not r),
    (p ∨ q) ∧ (Not p ∨ Not q)
  ]

unsatisfiable_formulas = [
    p ∧ q ∧ s ∧ Not p,
    T ∧ F,
    F,
    (p ∨ q ∧ r) ∧ Not p ∧ Not r,
    (p ⇔ q) ∧ (q ⇔ r) ∧ (r ⇔ s) ∧ (s ⇔ Not p)
  ]

instance Arbitrary Formula where
    arbitrary = sized f where
      
      f 0 = oneof $ map return $ [p, q, r, s, t] ++ [T, F]

      f size = frequency [
        (1, liftM Not (f (size - 1))),
        (4, do
              size' <- choose (0, size - 1)
              conn <- oneof $ map return [And, Or, Implies, Iff]
              left <- f size'
              right <- f $ size - size' - 1
              return $ conn left right)
        ]

-- truth valuations
type Valuation = PropName -> Bool

-- the evaluation function
eval :: Formula -> Valuation -> Bool
eval T _ = True
eval F _ = False
eval (Prop p) ρ = ρ p
eval (Not p) ρ = not (eval p ρ)
eval (And p q) ρ = eval p ρ && eval q ρ
eval (Or p q) ρ = eval p ρ || eval q ρ
eval (Implies p q) ρ = not (eval p ρ) || eval q ρ
eval (Iff p q) ρ = eval p ρ == eval q ρ

ρ0 = const True
ρ1 = const False
ρ2 = update ρ0 "p" False

test_eval =
  eval (p ∧ Not p) ρ0 == False &&
  eval (p ∧ Not p) ρ1 == False &&
  eval (p ∨ q) ρ2 == True

-- >>> quickCheck test_eval

-- check that the eval function is efficient
-- ifformula 3 == Iff (Iff (Iff T T) T) T
ifformula :: Int -> Formula
ifformula 0 = T
ifformula n = Iff (ifformula (n-1)) T

-- this should evaluate within a fraction of second
test_eval2 = eval (ifformula 23) (const True) == True

-- >>> quickCheck test_eval2

variables :: Formula -> [PropName]
variables = nub . go where
  go T = []
  go F = []
  go (Prop p) = [p]
  go (Not p) = go p
  go (And p q) = go p ++ go q
  go (Or p q) = go p ++ go q
  go (Implies p q) = go p ++ go q
  go (Iff p q) = go p ++ go q

type SATSolver = Formula -> Bool

-- the list of all valuations on a given list of variables
valuations :: [PropName] -> [Valuation]
valuations [] = [undefined]
valuations (x : xs) = concat [[update ρ x True, update ρ x False] | ρ <- valuations xs]

satisfiable :: SATSolver
satisfiable p = or [eval p ρ | ρ <- valuations (variables p)]

tautology :: Formula -> Bool
tautology p = and [eval p ρ | ρ <- valuations (variables p)]

is_nnf :: Formula -> Bool
is_nnf T = True
is_nnf F = True
is_nnf (Prop _) = True
is_nnf (Not (Prop _)) = True
is_nnf (And phi psi) = is_nnf phi && is_nnf psi
is_nnf (Or phi psi) = is_nnf phi && is_nnf psi
is_nnf (Implies phi psi) = False
is_nnf (Iff phi psi) = False
is_nnf (Not _) = False

-- >>> quickCheck $
-- >>>  is_nnf (Not p ∧ (q ∨ (r ∧ s)))  -- NNF example
-- >>> && (not $ is_nnf $ Not (p ∨ q)) -- NNF non-example

nnf :: Formula -> Formula
nnf T = T
nnf F = F
nnf (Prop p) = Prop p
nnf (Not T) = F
nnf (Not F) = T
nnf (Not (Prop p)) = Not (Prop p)
nnf (Not (Not p)) = nnf p
nnf (Not (And p q)) = nnf (Or (Not p) (Not q))
nnf (Not (Or p q)) = nnf (And (Not p) (Not q))
nnf (Not e) = nnf $ Not (nnf e)
nnf (And p q) = nnf p /\ nnf q
nnf (Or p q) = nnf p \/ nnf q
nnf (Implies p q) = nnf (Not p \/ q)
nnf (Iff p q) = nnf ((p /\ q) \/ (Not p /\ Not q))

prop_nnf :: Formula -> Bool
prop_nnf p = let q = nnf p in is_nnf q && (tautology $ p ⇔ q)

-- prop> prop_nnf

data Literal = Pos PropName | Neg PropName deriving (Eq, Show, Ord)

literal2var :: Literal -> PropName
literal2var (Pos p) = p
literal2var (Neg p) = p

type DNFClause = [Literal]
type DNF = [DNFClause]

dnf2formula :: [[Literal]] -> Formula
dnf2formula [] = F
dnf2formula lss = foldr1 Or (map go lss) where
  go [] = T
  go ls = foldr1 And (map go2 ls)
  go2 (Pos p) = Prop p
  go2 (Neg p) = Not (Prop p)

dnf :: Formula -> DNF
-- convert a formula to DNF form by using NNF form
dnf e = go $ nnf e where
  go T = [[]]
  go F = []
  go (Prop p) = [[Pos p]]
  go (Not (Prop p)) = [[Neg p]]
  go (Or p q) = go p ++ go q
  go (And p q) = [ls ++ ls' | ls <- go p, ls' <- go q]

test_dnf :: Formula -> Bool
test_dnf p = tautology $ p ⇔ (dnf2formula (dnf p))

-- >>> quickCheckWith (stdArgs {maxSize = 18}) test_dnf

sat_dnf :: SATSolver
sat_dnf = satisfiable . dnf2formula . dnf

prop_sat_dnf :: Formula -> Bool
prop_sat_dnf phi = sat_dnf phi == satisfiable phi

-- >>> quickCheckWith (stdArgs {maxSize = 20}) prop_sat_dnf

test_solver :: SATSolver -> Bool
test_solver solver = and $ map solver satisfiable_formulas ++ map (not . solver) unsatisfiable_formulas

-- >>> quickCheck (test_solver sat_dnf)

main :: IO ()
main = do
  quickCheck test_eval
  quickCheck test_eval2
  quickCheck $ is_nnf (Not p ∧ (q ∨ (r ∧ s)))  -- NNF example
  quickCheck $ not $ is_nnf $ Not (p ∨ q) -- NNF non-example
  quickCheckWith (stdArgs {maxSize = 18}) test_dnf
  quickCheckWith (stdArgs {maxSize = 20}) prop_sat_dnf
  quickCheck (test_solver sat_dnf)
  return ()
