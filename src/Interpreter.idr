module Interpreter

data Expr
  = App Expr Expr
  | Lam Expr
  | Zero
  | Succ Expr
  | Var Nat
  | Case Expr Expr Expr
  | Mu Expr

infixl 0 $$

($$) : Expr -> Expr -> Expr
($$) x y = App x y

subst : (at : Nat) -> (with_ : Expr) -> (inside : Expr) ->  Expr
subst n wth (App x y) = App (subst n wth x) (subst n wth y)
subst n wth (Lam x) = Lam (subst (S n) wth x)
subst n wth Zero = Zero
subst n wth (Succ x) = Succ (subst n wth x)
subst n wth (Var k) = if k == n then wth else Var k
subst n wth (Case x y z) = Case (subst n wth x) (subst n wth y) (subst (S n) wth z)
subst n wth (Mu x) = Mu (subst (S n) wth x)

eval : Expr -> Expr
eval (App f x) =
  case eval f of
       Lam body => eval (subst {at = 0, inside = body, with_ = x})
       other => App other x
eval (Lam x) = Lam x
eval Zero = Zero
eval (Succ x) = Succ x
eval (Var k) = Var k
eval (Case sc ifZero ifSucc) =
  case eval sc of
       Zero  => eval ifZero
       Succ n => eval (App ifSucc n)
       x => Case x ifZero ifSucc
eval (Mu x) = (subst 0 (Mu x) x)

fromInteger : Integer -> Expr
fromInteger i = natToExpr (fromInteger i)
  where
    natToExpr : Nat -> Expr
    natToExpr Z = Zero
    natToExpr (S n) = Succ (natToExpr n)

evalTest1 : eval (App (Lam (Var 0)) (Succ Zero)) = Succ Zero
evalTest1 = Refl

add : Expr
add = Mu $ Lam $ Lam $ Case (Var 1) (Var 0) (Lam (Var 4 $$ Var 0 $$ Succ (Var 2)))

const : Expr
const = Lam $ Lam (Var 0)

constTest : Interpreter.eval (Interpreter.const $$ 3 $$ 2) = 2
constTest = Refl

addTest : eval (Interpreter.add $$ 2 $$ 3) =  5
addTest = Refl

