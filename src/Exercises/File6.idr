module Exercises.File6


import Data.Fin
namespace Lambda
  public export
  data LC : Nat -> Type where
    Var : Fin n -> LC n
    Lam : LC (S n) -> LC n
    App : LC n -> LC n -> LC n
infixl 1 $$

($$) : LC n -> LC n -> LC n
($$) = App

prefix 2 \\

(\\) : LC (S n) -> LC n
(\\) = Lam

fromInteger : (i : Integer) -> {n : Nat} -> {auto 0 check : So (integerLessThanNat i n)} -> LC n
fromInteger i = Var (fromInteger i)

-- λx. λy. x
const : LC 0
const = \\ \\ 1

-- λx. x
id : LC 0
id = \\ 0

constId : LC 0
constId = const $$ id $$ id

-- λx. λy. x
-- always use the first argument
true : LC 0
true = \\ \\ 1

-- λx. λy. y
-- always use the second argument
false : LC 0
false = \\ \\ 0

constOrId : LC 0
constOrId = \\ 0 $$ const $$ id

-- λx. λy. x
-- like const
zero : LC 0
zero = \\ \\ 1

-- λx. λy. λz. z (x y z)
-- λ2. λ1. λ0. 0 (2 1 0)
-- λλλ 0 (2 1 0)
succ : LC 0
succ = \\ \\ \\ (0 $$ (2 $$ 1 $$ 0))

namespace LambdaNat
  public export
  data LCNat : Nat -> Type where
    Var : Fin n -> LCNat n
    Lam : LCNat (S n) -> LCNat n
    App : LCNat n -> LCNat n -> LCNat n
    Zero : LCNat n
    Succ : LCNat n -> LCNat n
    Case : (scrutinee : LCNat n)
        -> (zero : LCNat n)
        -> (succ : LCNat (S n))
        -> LCNat n
    Mu : LCNat (S n) -> LCNat n

  export
  ($$) : LCNat n -> LCNat n -> LCNat n
  ($$) = App

  export
  (\\) : LCNat (S n) -> LCNat n
  (\\) = Lam

  export
  fromInteger : (i : Integer) -> {n : Nat} -> {auto 0 check : So (integerLessThanNat i n)} -> LCNat n
  fromInteger i = Var (fromInteger i)

  export
  print : LCNat n -> String
  print (Var n) = show n
  print (Lam body) = "λ \{print body}"
  print (App fn arg) = "\{print fn} \{print arg}"
  -- this is multi-line syntax in Idris
  print (Case v z s) = """
    case \{print v} of
        Zero => \{print z}
        Succ 0 => \{print s}
    """
  print n = either id show (fromNat n)
    where
      fromNat : LCNat _ -> Either String Nat
      fromNat Zero = Right Z
      fromNat (Succ n) = bimap ("S " ++) S (fromNat n)
      fromNat x = Left (print x)

one : LCNat n
one = Succ Zero

two : LCNat n
two = Succ (Succ Zero)

-- λx. λy. case x of Z => y ; (S n) => S (plus n y)
plus : LCNat 0
plus = Mu (\\ \\ Case 1 0 (\\ Succ (3 $$ 0 $$ 1)))

ex : (Fin n -> Fin m) -> Fin (S n) -> Fin (S m)
ex f FZ = FZ
ex f (FS x) = FS (f x)

rename : (Fin n -> Fin m) -> LCNat n -> LCNat m
rename f (Var x) = Var (f x)
rename f (Lam x) = Lam (rename (ex f) x)
rename f (App x y) = App (rename f x) (rename f y)
rename f Zero = Zero
rename f (Succ x) = Succ (rename f x)
rename f (Case scrutinee zero succ) =
  Case (rename f scrutinee) (rename f zero) (rename (ex f) succ)
rename f (Mu x) = Mu (rename (ex f) x)

data Value : LCNat n -> Type where
  ZeroValue : Value Zero
  SuccValue : Value n -> Value (Succ n)
  LamValue : Value (Lam x)

eval : (expr : LCNat n) -> Maybe (Value expr)
eval (Var x) = Nothing
eval (Lam x) = Just LamValue
eval (App x y) = ?eval_rhs_2
eval Zero = ?eval_rhs_3
eval (Succ x) = ?eval_rhs_4
eval (Case scrutinee zero succ) = ?eval_rhs_5
eval (Mu x) = ?eval_rhs_6
