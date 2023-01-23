module Scoped2

import Data.Fin
import Data.Vect
import Data.List.Elem

Contains : List a -> a -> Type
Contains ls x = x `Elem` ls

data LCType  : Type where
  (=>>) : LCType -> LCType -> LCType
  Nat : LCType

infix 4 |-

infixr 5 =>>

data Expr : (0 _ : Nat)  -> Type where

  -- a type variable
  Val : Fin n -> Expr n

  -- lambda abstraction
  Lam : Expr (S n) -> Expr n

  Case : (scrutinee : Expr n)
      -> (ifZero : Expr n)
      -> (ifSucc : Expr (S n))
      -> Expr n

  -- application
  App :
        Expr n
     -> Expr n
      ------------------
     -> Expr n

  Zero : Expr n

  Succ : Expr n -> Expr n

  Mu : Expr (S n) -> Expr n

ext :
      (Fin n -> Fin m)
   -> (Fin (S n) -> Fin (S m))
ext f FZ = FZ
ext f (FS x) = FS (f x)

rename :
     (Fin n -> Fin m)
    -----------------------
  -> (Expr n -> Expr m)
rename f (Val x)   = Val (f x)
rename f (Lam x)   = Lam (rename (ext f) x)
rename f (App x y) = App (rename f x) (rename f y)
rename f Zero      = Zero
rename f (Succ n)  = Succ (rename f n)
rename f (Mu x)    = Mu (rename (ext f) x)
rename f (Case scrutinee ifZero ifSucc) =
  Case (rename f scrutinee) (rename f ifZero) (rename (ext f) ifSucc)

exts : (Fin n -> Expr m)
    -> (Fin (S n) -> Expr (S m))
exts f FZ = Val FZ
exts f (FS x) = rename FS (f x)

subst : (Fin n -> Expr m)
     -> (Expr n -> Expr m)
subst f (Val x)   = f x
subst f (Lam x)   = Lam (subst (exts f) x)
subst f (App x y) = App (subst f x) (subst f y)
subst f Zero      = Zero
subst f (Succ x)  = Succ (subst f x)
subst f (Mu x)    = Mu (subst (exts f) x)
subst f (Case scrutinee ifZero ifSucc) = Case (subst f scrutinee) (subst f ifZero) (subst (exts f) ifSucc)

subst1 : Expr (S n) -> Expr n -> Expr n
subst1 x y = subst (\case FZ => y; (FS n) => Val n) x

substCtx : Vect n (Expr m) -> Expr n -> Expr m
substCtx xs x = subst (\i => index i xs) x

fromInteger : Integer -> Expr n
fromInteger i = natToExpr (fromInteger i)
  where
    natToExpr : Nat -> Expr n
    natToExpr Z = Zero
    natToExpr (S n) = Succ (natToExpr n)

infixl 0 $$

($$) : Expr n -> Expr n -> Expr n
($$) x y = App x y

partial
eval : Expr n -> Expr n
eval (Val x) = Val x
eval (Lam x) = Lam x
eval (Case Zero ifZero ifSucc) = eval ifZero
eval (Case (Succ x) ifZero ifSucc) = eval $ App (Lam ifSucc) x
eval (Case other ifZero ifSucc) = assert_total $ idris_crash "stuck"
eval (App f x) = case eval f of
  Lam body => eval (subst1 body x)
  other =>  App other x
eval Zero = Zero
eval (Succ x) = Succ x
eval (Mu x) = subst1 x (Mu x)

evalTest1 : eval (App (Lam (Val 0)) (Succ Zero)) = Succ Zero
evalTest1 = Refl

add : Expr n
add = Mu $ Lam $ Lam $ Case (Val 1) (Val 0) (Lam (Val 4 $$ Val 0 $$ Succ (Val 2)))

const : Expr n
const = Lam $ Lam (Val 0)

constTest : Scoped2.eval (Scoped2.const $$ 3 $$ 2) = 2
constTest = Refl

addTest : eval ((Scoped2.add $$ 2) $$ 3) = 5
addTest = ?adddddd

