module Exercises.File4

import Data.Fin
import Data.Vect

data LC : Nat -> Type where
  Var : Fin n -> LC n
  Zero : LC 0
  Succ : LC 0 -> LC 0
  Lam : LC (S n) -> LC n
  Apply : LC n -> LC n -> LC n

identity :  LC 0
identity = Lam (Var 0)

const : LC 0
const = Lam (Lam (Var 1))

zero : LC 0
zero = const

-- λ 2 . λ 1 . λ 0 . 0 (2 1 0)
succ : LC 0
succ = Lam (Lam (Lam (Apply (Var 0) (Apply (Apply (Var 2) (Var 1)) (Var 0)))))

-- λ 3 2 1 0 . 2 (3 1 0) 0
plus : LC 0
plus = Lam (Lam (Lam (Lam (Apply (Apply (Var 2) (Apply (Apply (Var 3) (Var 1)) (Var 0))) (Var 0)))))

fromInteger : (i : Integer) -> {n : Nat} -> {auto 0 check : So (integerLessThanNat i n)} -> LC n
fromInteger i = Var (fromInteger i)

infixl 1 $$

($$) : LC n -> LC n -> LC n
($$) = Apply

prefix 2 \\

(\\) : LC (S n) -> LC n
(\\) = Lam

-- λ 3 2 1 0 . 2 (3 1 0) 0
plus' : LC 0
plus' = \\ \\ \\ \\ (2 $$ (3 $$ 1 $$ 0) $$ 0)

one : LC 0
one = succ $$ zero

two : LC 0
two = succ $$ (succ $$ zero)

three : LC 0
three = plus $$ one $$ two

true : LC 0
true = \\ \\ 1

false : LC 0
false = \\ \\ 0

subst : LC (S n) -> LC n -> LC n
subst (Var x) y = y
subst (Lam x) y = ?subst_rhs_1
subst (Apply x z) y = Apply (subst x y) (subst z y)

interpret : LC n -> Vect n (LC 0) -> LC 0
interpret x [] = x
interpret x (y :: xs) = ?interpret_rhs_1

