module ScopedInterpreter

import Data.Fin

data Expr : Nat -> Type where
  App : (fn : Expr n) -> (arg : Expr n) -> Expr n
  Lam : Expr (S n) -> Expr n
  Zero : Expr n
  Succ : Expr n -> Expr n
  Var : Fin n -> Expr n
  Case : (scrutinee : Expr n) -> (ifZero : Expr n) -> (ifSucc : Expr (S n)) -> Expr n
  Mu : Expr (S n) -> Expr n

infixl 0 $$

($$) : Expr n -> Expr n -> Expr n
($$) x y = App x y

subst : (at : Fin n) -> (with_ : Expr n) -> (inside : Expr n) ->  Expr n
subst i wth (App x y) = App (subst i wth x) (subst i wth y)
subst i wth (Lam x) = Lam (subst {n = S n} ?wwhua ?ad x) --(subst (FS n) wth (?weaken x))
subst i wth Zero = Zero
subst i wth (Succ x) = Succ (subst i wth x)
subst i wth (Var k) = if k == i then wth else Var k
subst i wth (Case x y z) = Case (subst i wth x) (subst i wth y) ?substNext--(subst (S n) wth z)
subst i wth (Mu x) = ?subtnn --Mu (subst (S n) wth x)

{-

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

