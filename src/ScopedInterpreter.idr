module ScopedInterpreter

import Data.Fin
import Data.Vect

%default total

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

ext : (Fin n -> Fin m) -> Fin (S n) -> Fin (S m)
ext f FZ = FZ
ext f (FS x) = FS (f x)

rename : (Fin n -> Fin m) -> Expr n -> Expr m
rename f (App fn arg) = App (rename f fn) (rename f arg)
rename f (Lam x) = Lam (rename (ext f) x)
rename f Zero = Zero
rename f (Succ x) = Succ (rename f x)
rename f (Var x) = Var (f x)
rename f (Case scrutinee ifZero ifSucc) =
  Case (rename f scrutinee) (rename f ifZero) (rename (ext f) ifSucc)
rename f (Mu x) = Mu (rename (ext f) x)

-- subst : (at : Fin n) -> (with_ : Expr n) -> (inside : Expr n) -> Expr n
-- subst i wth (App x y) = App (subst i wth x) (subst i wth y)
-- subst i wth (Lam x) = Lam (subst {n = S n} (FS i) (rename FS wth) x) --(subst (FS n) wth (?weaken x))
-- subst i wth Zero = Zero
-- subst i wth (Succ x) = Succ (subst i wth x)
-- subst i wth (Var k) = if k == i then wth else Var k
-- subst i wth (Case x y z) = Case (subst i wth x) (subst i wth y) (subst {n = S n} (FS i) (rename FS wth) z)
-- subst i wth (Mu x) = Mu (subst (FS i) (rename FS wth) x)

substContext : Vect n (Expr m) -> Expr n -> Expr m
substContext ctx (App fn arg) = App (substContext ctx fn) (substContext ctx arg)
substContext ctx (Lam x)      = Lam (substContext (Var FZ :: map (rename FS) ctx) x)
substContext ctx Zero         = Zero
substContext ctx (Succ x)     = Succ (substContext ctx x)
substContext ctx (Var x)      = index x ctx
substContext ctx (Mu x)       = Mu (substContext (Var FZ :: map (rename FS) ctx) x)
substContext ctx (Case scrutinee ifZero ifSucc) =
  Case (substContext ctx scrutinee) (substContext ctx ifZero) (substContext (Var FZ :: map (rename FS) ctx) ifSucc)

exprRange : {n : Nat} -> Vect n (Expr n)
exprRange = map Var range

subst0 : {n : _} -> (with_ : Expr m) -> (inside : Expr (S n)) -> Expr m
subst0 with_ inside = substContext (with_ :: ?whui) inside

{-
eval : {n : _} -> Expr n -> Expr n
eval (App f x) =
  case eval f of
       Lam body => assert_total $ eval (subst0 { inside = body, with_ = x})
       other => App other x
eval (Lam x)  = Lam x
eval Zero     = Zero
eval (Succ x) = Succ x
eval (Var k)  = Var k
eval (Mu x)   = subst0 (Mu x) x
eval (Case sc ifZero ifSucc) =
  case eval sc of
       Zero  => eval ifZero
       Succ n => subst0 n ifSucc
          -- case eval ifSucc of
          --      Lam body => assert_total $ eval (subst0 { inside = ?bbb, with_ = n})
          --      other => App ?nnn n --App other ?aan
       x => Case x ifZero ifSucc

fromInteger : Integer -> Expr n
fromInteger i = natToExpr (fromInteger i)
  where
    natToExpr : Nat -> Expr n
    natToExpr Z = Zero
    natToExpr (S n) = Succ (natToExpr n)

evalTest1 : eval (App (Lam (Var 0)) (Succ Zero)) = Succ Zero
-- evalTest1 = Refl

add : Expr n
add = Mu $ Lam $ Lam $ Case (Var 1) (Var 0) (Lam (Var 4 $$ Var 0 $$ Succ (Var 2)))

const : Expr n
const = Lam $ Lam (Var 0)

constTest : ScopedInterpreter.eval (ScopedInterpreter.const $$ 3 $$ 2) = 2
-- constTest = Refl

addTest : eval (ScopedInterpreter.add $$ 2 $$ 3) =  5
addTest = ?asd

