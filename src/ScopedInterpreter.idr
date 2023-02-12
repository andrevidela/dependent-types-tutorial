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

ext : (Fin n -> Fin m)
   -> (Fin (S n) -> Fin (S m))
ext f FZ = FZ
ext f (FS x) = FS (f x)

rename :
     (Fin n -> Fin m)
    -----------------------
  -> (Expr n -> Expr m)
rename f (Var x)   = Var (f x)
rename f (Lam x)   = Lam (rename (ext f) x)
rename f (App x y) = App (rename f x) (rename f y)
rename f Zero      = Zero
rename f (Succ n)  = Succ (rename f n)
rename f (Mu x)    = Mu (rename (ext f) x)
rename f (Case scrutinee ifZero ifSucc) =
  Case (rename f scrutinee) (rename f ifZero) (rename (ext f) ifSucc)

exts : (Fin n -> Expr m)
    -> (Fin (S n) -> Expr (S m))
exts f FZ = Var FZ
exts f (FS x) = rename FS (f x)

subst : (Fin n -> Expr m)
     -> (Expr n -> Expr m)
subst f (Var x)   = f x
subst f (Lam x)   = Lam (subst (exts f) x)
subst f (App x y) = App (subst f x) (subst f y)
subst f Zero      = Zero
subst f (Succ x)  = Succ (subst f x)
subst f (Mu x)    = Mu (subst (exts f) x)
subst f (Case scrutinee ifZero ifSucc) = Case (subst f scrutinee) (subst f ifZero) (subst (exts f) ifSucc)

subst0 : (with_ : Expr n) ->(inside : Expr (S n)) ->  Expr n
subst0 y x = subst (\case FZ => y; (FS n) => Var n) x

substCtx : Vect n (Expr m) -> Expr n -> Expr m
substCtx xs x = subst (\i => index i xs) x

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
       Succ n => assert_total $ eval $ subst0 n (eval ifSucc)
       x => Case x ifZero ifSucc

fromInteger : Integer -> Expr n
fromInteger i = natToExpr (fromInteger i)
  where
    natToExpr : Nat -> Expr n
    natToExpr Z = Zero
    natToExpr (S n) = Succ (natToExpr n)

evalTest1 : eval (App (Lam (Var 0)) (Succ Zero)) = Succ Zero
evalTest1 = Refl

add : Expr n
add = Mu $ Lam $ Lam $ Case (Var 1) (Var 0) ((Var 3 $$ Var 0 $$ Succ (Var 1)))

double : Expr n
double = Mu $ Lam $ Case (Var 0) Zero (Lam (Var 3 $$ Succ (Succ (Var 0))))

identity : Expr n
identity = Lam (Var 0)

natIdentity : Expr n
natIdentity = Lam $ Case (Var 0) Zero (Succ (Var 0))

testNatId : ScopedInterpreter.eval (ScopedInterpreter.natIdentity $$ 2) = 2
testNatId = Refl

testIdentity :  ScopedInterpreter.eval (ScopedInterpreter.identity $$ ScopedInterpreter.identity) = ScopedInterpreter.identity
testIdentity = Refl


testDouble : ScopedInterpreter.eval (ScopedInterpreter.double $$ 2) = 4
testDouble = ?ww

const : Expr n
const = Lam $ Lam (Var 0)

constTest : ScopedInterpreter.eval (ScopedInterpreter.const $$ 3 $$ 2) = 2
constTest = Refl

addTest : eval (ScopedInterpreter.add $$ 2 $$ 3) = 5
addTest = Refl

fail : Expr n
fail = double $$ identity

testFail : ScopedInterpreter.eval ScopedInterpreter.fail = 0
testFail = ?hole

