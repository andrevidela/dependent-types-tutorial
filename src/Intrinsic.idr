module Intrinsic

import Data.List.Elem

Contains : List a -> a -> Type
Contains ls x = x `Elem` ls

data LCType  : Type where
  (=>>) : LCType -> LCType -> LCType
  Nat : LCType

infix 4 |-

infixr 5 =>>

data (|-) : (0 _ : List LCType) -> (0 _ : LCType) -> Type where

  -- a type variable
  Val : gamma `Contains` e -> gamma |- e

  -- lambda abstraction
  Lam : a :: gamma |- b
      ------------------
     -> gamma |- a =>> b

  Case : (scrutinee : gamma |- Nat)
      -> (ifZero : gamma |- a)
      -> (ifSucc : Nat :: gamma |- a)
      -> gamma |- a

  -- application
  App : {a : _}
     -> gamma |- a =>> b
     -> gamma |- a
      ------------------
     -> gamma |- b

  Zero : gamma |- Nat

  Succ : gamma |- Nat
      -> gamma |- Nat

  Mu : a :: gamma |- a
    -> gamma |- a

ext : forall gamma, delta.
      (forall a.         gamma `Contains` a ->      delta `Contains` a)
   -> (forall a, b. b :: gamma `Contains` a -> b :: delta `Contains` a)
ext f Here = Here
ext f (There x) = There (f x)

rename : forall gamma, delta.
     (forall a. gamma `Contains` a -> delta `Contains` a)
    -----------------------
  -> (forall a. gamma |- a -> delta |- a)
rename f (Val x)   = Val (f x)
rename f (Lam x)   = Lam (rename (ext f) x)
rename f (App x y) = App (rename f x) (rename f y)
rename f Zero      = Zero
rename f (Succ n)  = Succ (rename f n)
rename f (Mu x)    = Mu (rename (ext f) x)
rename f (Case scrutinee ifZero ifSucc) =
  Case (rename f scrutinee) (rename f ifZero) (rename (ext f) ifSucc)

exts : forall gamma, delta.
       (forall a.         gamma `Contains` a -> delta |- a)
    -> (forall a, b. b :: gamma `Contains` a -> b :: delta |- a)
exts f Here = Val Here
exts f (There x) = rename There (f x)

subst : forall gamma, delta.
        (forall a. gamma `Contains` a -> delta |- a)
     -> (forall a. gamma |-         a -> delta |- a)
subst f (Val x)   = f x
subst f (Lam x)   = Lam (subst (exts f) x)
subst f (App x y) = App (subst f x) (subst f y)
subst f Zero      = Zero
subst f (Succ x)  = Succ (subst f x)
subst f (Mu x)    = Mu (subst (exts f) x)
subst f (Case scrutinee ifZero ifSucc) = Case (subst f scrutinee) (subst f ifZero) (subst (exts f) ifSucc)

subst1 : forall gamma, a, b.
         b :: gamma |- a
      -> gamma |- b
        ---------
      -> gamma |- a
subst1 x y = subst (\case Here => y
                          (There z) => Val z) x

data Value : g |- a -> Type where
  VLam : Value (Lam n)
  VZero : forall gamma. Value {g = gamma} (Zero {gamma})
  VSucc : forall gamma. {0 v : gamma |- Nat} ->  Value v -> Value (Succ v)

infixr 0 ~~>

data (~~>) : forall gamma, a. gamma |- a -> gamma |- a -> Type where
  -- congruence-like rules
  CongApp1 : forall gamma, a, b.
             {0 l, l' : gamma |- a =>> b}
          -> {0 m : gamma |- a}
          -> (l ~~> l') -> (App l m ~~> App l' m)

  CongApp2 : forall gamma, a, b.
             {0 v : gamma |- a =>> b}
          -> {0 m, m' : gamma |- a}
          -> Value {g = gamma, a = a =>> b} v
          -> (m ~~> m')
          -> (App v m ~~> App v m')
  CongSucc : forall gamma.
             {0 m, m' : gamma |- Nat}
          -> (m ~~> m')
          -> Succ m ~~> Succ m'

  CongCase : forall gamma, a.
             {0 l, l' : gamma |- Nat}
          -> {0 m : gamma |- a}
          -> {0 n : Nat :: gamma |- a}
          -> l ~~> l'
          -> Case l m n ~~> Case l' m n

  -- beta-like rules
  BetaLam : forall gamma, a, b.
            {0 n : a :: gamma |- b}
         -> {0 w : gamma |- a}
         -> Value w
         -> App (Lam n) w ~~> subst1 n w

  BetaZero : forall gamma, a.
             {0 m : gamma |- a}
          -> {0 n : Nat :: gamma |- a}
          -> Case Zero m n ~~> m

  BetaSucc : forall gamma, a.
             {0 v : gamma |- Nat}
          -> {0 m : gamma |- a}
          -> {0 n : Nat :: gamma |- a}
          -> Value v
          -> Case (Succ v) m n ~~> subst1 n v

  BetaMu : forall gamma, a.
           {0 n : a :: gamma |- a}
        -> Mu n ~~> subst1 n (Mu n)

total
eval : gamma |- a -> gamma |- a
eval (Val x) = Val x
eval (App x y) = case eval x of
     Lam n => assert_total $ eval (subst1 n y)
     other => App other y
eval (Lam x) = Lam x
eval (Mu x) = subst1 x (Mu x)
eval Zero = Zero
eval (Succ x) = Succ x
eval (Case scrutinee ifZero ifSucc) =
  case eval scrutinee of
       Zero => ifZero
       (Succ x) => assert_total $ eval $ App (Lam ifSucc) x
       other => Case scrutinee ifZero ifSucc

infixl 0 $$

($$) : {a : _}
     -> gamma |- a =>> b
     -> gamma |- a
      ------------------
     -> gamma |- b
($$) x y = App x y


evalTest1 : eval (App (Lam (Val Here)) (Succ Zero)) = Succ Zero
evalTest1 = Refl

add : gamma |- Nat =>> Nat =>> Nat
add = Mu $ Lam $ Lam $ Case (Val Here)
  (Val (There Here)) -- if zero return the first
  (Lam (Lam (Val (There $ There $ There $ There $ Here)))
    $$ Val Here -- recursive call with the smaler first argument
    $$ Succ (Val (There $ There Here))) -- and increase the second argument

add2 : gamma |- Nat =>> Nat =>> Nat
add2 = Mu $ Lam $ Lam $ Case (Val $ There Here) -- analyse the second argument
  (Val (Here)) -- if zero return the first
  (Lam (Lam (Val (There $ There $ There $ There $ Here)))
    $$ Succ (Val (There $ There Here))  -- recursivecall with the successor of the first argument
    $$ Val Here)                -- and the smaller second argument
-- add = Mu $ Lam $ Lam $ Case (Val (There Here)) (Val Here) (Lam (Val (There $ There $ There $ There $ Here) $$ Val Here $$ Succ (Val (There $ There $ Here))))

const : b :: a :: gamma |- a
const = (Val (There Here))

const' : gamma |- a =>> b =>> a
const' = Lam $ Lam (Val (There Here))

constTest : Intrinsic.eval (Lam (Lam Intrinsic.const) $$ Zero $$ (Succ Zero)) = Zero
constTest = Refl

constTest2 : Intrinsic.eval (Lam (Lam (Val $ There Here)) $$ Zero $$ (Succ Zero)) = Zero
constTest2 = Refl

constTest3 : Intrinsic.eval (Intrinsic.const' $$ Zero $$ (Succ Zero)) = Zero
constTest3 = Refl

addTest : eval (Intrinsic.add $$ (Succ (Succ Zero)) $$ (Succ $ Succ Zero)) = (Succ $ Succ $ Succ $ Succ Zero)
addTest = ?adddddd


lt : Nat -> Nat -> Bool
lt Z n = True
lt (S m) (S n) = lt m n
lt _ _ = False


t : Nat -> Type
t n = if (S Z `lt` n )
  then Nat
  else (Nat, Nat)

f : (n : Nat) -> t n
f n with (S Z `lt` n) proof p
  f n | True = 0
  f n | False = (1, 2)
