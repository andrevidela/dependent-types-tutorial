module Exercises.File5

import Data.Nat
import Data.List
import Data.List.Elem
import Data.List.Quantifiers
import Data.So
import Data.Fin

infixr 5 =>>

record Fix2 (f : Type -> Type -> Type) (a : Type) where
  constructor Rec2
  unFix : Lazy (f a (Fix2 f a))

-- a type is either a natural number of a function
data Kind  : Type where
  (=>>) : Kind -> Kind -> Kind
  Star : Kind

-- a context is a snoc list
-- data Context : Type where
--   Lin : Context
--   (:<) : Context -> Kind -> Context

-- Proof that a type is in context
-- data In : Kind -> Context -> Type where
--   Here : ty `In` (gamma :< ty)
--   There : ty `In` gamma -> ty `In` (gamma :< sy)

fromInteger : (i : Integer)
           -> {auto 0 xs : List Kind}
           -> {auto 0 prf : So (integerLessThanNat i (length xs))}
           -> Elem Star xs

infix 4 |-

-- a well typed judgement
data (|-) : (0 _ : List Kind) -> (0 _ : Kind) -> Type where

  -- a type variable
  Val : e `Elem` gamma -> gamma |- e

  -- lambda abstraction
  Lam : a :: gamma |- b
      ------------------
     -> gamma |- a =>> b

  -- Type application
  App : {a : _}
     -> gamma |- a =>> b
     -> gamma |- a
      ------------------
     -> gamma |- b

  Zero : gamma |- Star
  One : gamma |- Star

  Times : gamma |- Star
       -> gamma |- Star
       -> gamma |- Star

  Plus : gamma |- Star
      -> gamma |- Star
      -> gamma |- Star

  Mu : a :: gamma |- a
    -> gamma |- a

-- -- If we can map "a in gamma" to "a in delta" then we can also
-- -- map it whenever gamma and delta are extended with one more variable
-- ext : {0 gamma, delta : List Kind} ->
--       ({0 a    : Kind} -> a `Elem` gamma       -> a `Elem` delta) ->
--       ({0 a, b : Kind} -> a `Elem` b :: gamma -> a `Elem` b :: delta)
-- ext f Here = Here
-- ext f (There x) = There (f x)
--
-- rename : {0 delta, gamma : List Kind}
--       -> ({0 a : Kind} -> a `Elem` gamma -> a `Elem` delta)
--       -> ({0 a : Kind} -> gamma |- a -> delta |- a)
-- rename f  (Val x) = Val (f x)
-- rename f {a = (a =>> b)} (Lam x) = Lam (rename (ext f) x)
-- rename f (App x y) = App (rename f x) (rename f y)
-- rename f (Mu x) = Mu (rename (ext f) x)
-- rename f (Plus x y) = Plus (rename f x) (rename f y)
-- rename f (Times x y) = Times (rename f x) (rename f y)
-- rename f Zero = Zero
-- rename f One = One
--
-- exts : {0 gamma, delta : List Kind}
--   -> ({0 a    : Kind} -> a `Elem` gamma      -> delta      |- a)
--   -> ({0 a, b : Kind} -> a `Elem` b :: gamma -> b :: delta |- a)
-- exts f Here = Val Here
-- exts f (There x) = rename There (f x)
--
-- substitution : {0 gamma, delta : List Kind}
--   -> ({0 a : Kind} -> a `Elem` gamma -> delta |- a)
--   -> ({0 a : Kind} -> gamma |- a -> delta |- a)
-- substitution f (Val x) = f x
-- substitution f (Lam x) = Lam (substitution (exts f) x)
-- substitution f (App x y) = App (substitution f x) (substitution f y)
-- substitution f (Mu x) = Mu (substitution (exts f) x)
-- substitution f (Plus x y) = Plus (substitution f x) (substitution f y)
-- substitution f (Times x y) = Times (substitution f x) (substitution f y)
-- substitution f Zero = Zero
-- substitution f One = One
--
-- -- substitution of one variable
-- subst1 : {0 gamma, a, b : _}
--   -> b :: gamma |- a
--   -> gamma |- b
--   -> gamma |- a
-- subst1 x y = substitution {gamma = b :: gamma} replaceZero x
--   where
--     -- replace every occurence of `Here` with the variable y
--     replaceZero : {0 c : Kind} -> c `Elem` b :: gamma  -> gamma |- c
--     -- if we find a variable at 0, we return `y` instead
--     replaceZero Here = y
--     -- if we find a variable that's not 0 we return a variable that's its
--     -- predecessor. Because the new context is one variable smaller
--     replaceZero (There x) = Val x

KindType : Kind -> Type
KindType Star = Type
KindType (a =>> b) = KindType a -> KindType b

record Fix (f : Type -> Type)  where
  constructor Rec
  unFix : Lazy (f (Fix f))

ToType : {kind : Kind} -> {kinds : List Kind} -> kinds |- kind -> All KindType kinds -> KindType kind
ToType {kinds = (x :: xs)} (Val Here) (y :: ys) = y
ToType {kinds = (x :: xs)} (Val (There z)) (y :: ys) = ToType {kinds = xs} (Val z) ys
ToType {kind = (a =>> b)} {kinds = kinds} (Lam x) y = \arg => ToType x (arg :: y)
ToType {kind = kind} {kinds = kinds} (App x z) y = (ToType x y) (ToType z y)
ToType {kind = Star} {kinds = kinds} (Mu x) y = Fix (\ty => ToType x (ty :: y))
ToType {kind = (Star =>> Star) } {kinds = kinds} (Mu x) y =
  Fix2 (\a, b => ?unimplemented2)
ToType {kind = (a =>> b) } {kinds = kinds} (Mu x) y = ?unimplemented
ToType {kind = Star} {kinds} (Plus x y) z = Either (ToType x z) (ToType y z)
ToType {kind = Star} {kinds} (Times x y) z = Pair (ToType x z) (ToType y z)
ToType Zero _ = Void
ToType One _ = Unit

ChoiceVal : Bool -> Type -> Type -> Type
ChoiceVal True a b = a
ChoiceVal False a b = b

record FunkyEither (a, b : Type) where
  constructor MkFunkyEither
  choice : Bool
  value : ChoiceVal choice a b

MkLeft : a -> FunkyEither a b
MkLeft x = MkFunkyEither True x

MkRight : b -> FunkyEither a b
MkRight y = MkFunkyEither False y


EitherDesc : Star ::  Star :: gamma |- Star
EitherDesc = Plus (Val Here) (Val (There Here))

MaybeDesc : [Star] |- Star
MaybeDesc = App (Lam EitherDesc) One

EitherLam : gamma |- Star =>> Star =>> Star
EitherLam = Lam (Lam EitherDesc)

EitherOne : [] |- Star
EitherOne = App (App EitherLam One) One

EitherType : Type -> Type -> Type
EitherType = ToType EitherLam []

EitherOneTy : ToType EitherOne []
EitherOneTy = Left ()

ListDesc : Star :: gamma |- Star
ListDesc = Mu (Plus One (Times (Val (There Here)) (Val $ Here)))

EitherList : Type -> Type -> Type
EitherList a b = List (Either a b)

ListEitherDesc : gamma |- Star =>> Star =>> Star
ListEitherDesc = Lam $ Lam $ App (Lam ListDesc) (App (App EitherLam (Val Here)) (Val (There Here)))

ListType : Type -> Type
ListType = ToType (Lam ListDesc) []

ListNil : ListType a
ListNil = Rec (Left ())

ListCons : a -> ListType a -> ListType a
ListCons x y = Rec (Right (x, y))

TreeDesc : [] |- (Star =>> Star) =>> Star
TreeDesc = Lam $ Mu (Times One (App (Val $ There Here) (Val Here)))

Identity : [n] |- n
Identity = Val Here

AppId : [] |- Star =>> Star
AppId = App (Lam Identity ) (Lam MaybeDesc)

MaybeId : Type -> Type
MaybeId = ToType AppId []

MaybeIdNothing : MaybeId a
MaybeIdNothing = Left ()

MaybeIdJust : a -> MaybeId a
MaybeIdJust x = Right x

