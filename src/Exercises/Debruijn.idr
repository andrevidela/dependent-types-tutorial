module Exercises.Debruijn

import Data.Nat

infix 5 =>>

-- a type is either a natural number of a function
data Ty  : Type where
  (=>>) : Ty -> Ty -> Ty
  N : Ty

-- a context is a snoc list
data Context : Type where
  Lin : Context
  (:<) : Context -> Ty -> Context

-- Proof that a type is in context
data In : Ty -> Context -> Type where
  Here : ty `In` (gamma :< ty)
  Later : ty `In` gamma -> ty `In` (gamma :< sy)

infix 4 |-

-- a well typed judgement
data (|-) : (0 _ : Context) -> (0 _ : Ty) -> Type where
  Val : e `In` gamma -> gamma |- e
  Lam : gamma :< a |- b
      ------------------
     -> gamma |- a =>> b
  App : gamma |- a =>> b
     -> gamma |- a
      ------------------
     -> gamma |- b

  Zero : gamma |- N
  Succ : gamma |- N
      -> gamma |- N

  Case : gamma |- N
      -> gamma |- a
      -> gamma :< N |- a
      ------------------
      -> gamma |- a

  Mu : gamma :< a |- a
    -> gamma |- a

-- we can compute the length of a context
length : Context -> Nat
length [<] = Z
length (x :< y) = S (length x)

-- we can lookup in the context if we have a index within bounds
lookup : (gamma : Context) -> (n : Nat) -> {auto p : n `LT` length gamma} -> Ty
lookup [<] _ impossible
lookup (x :< y) 0 {p = (LTESucc LTEZero)} = y
lookup (x :< y) (S k) {p = (LTESucc z)} = lookup x k {p = z}

count : (gamma : Context) -> (n : Nat) -> {auto p : n `LT` length gamma} -> lookup gamma n `In` gamma
count [<] _ impossible
count (x :< y) 0 {p = (LTESucc LTEZero)} = Here
count (x :< y) (S k) {p = (LTESucc z)} = Later (count x k)


-- If we can map "a in gamma" to "a in delta" then we can also
-- map it whenever gamma and delta are extended with one more variable
ext : {0 gamma, delta : Context} ->
      ({0 a    : Ty} -> a `In` gamma       -> a `In` delta) ->
      ({0 a, b : Ty} -> a `In` gamma :< b  -> a `In` delta :< b)
ext f Here = Here
ext f (Later x) = Later (f x)

rename : {0 delta, gamma : Context}
      -> ({0 a : Ty} -> In a gamma -> In a delta)
      -> ({0 n : Ty} -> gamma |- n -> delta |- n)
rename f {n = n} (Val x) = Val (f x)
rename f {n = (a =>> b)} (Lam x) = Lam (rename (ext f) x)
rename f {n = n} (App x y) = App (rename f x) (rename f y)
rename f {n = N} Zero = Zero
rename f {n = N} (Succ x) = Succ (rename f x)
rename f {n = n} (Case x y z) = Case (rename f x) (rename f y) (rename (ext f) z)
rename f {n = n} (Mu x) = Mu (rename (ext f) x)

exts : {0 gamma, delta : Context}
  -> ({0 a    : Ty} -> a `In` gamma      -> delta      |- a)
  -> ({0 a, b : Ty} -> a `In` gamma :< b -> delta :< b |- a)
exts f Here = Val Here
exts f (Later x) = rename Later (f x)

substitution : {0 gamma, delta : Context}
  -> ({0 a : Ty} -> a `In` gamma -> delta |- a)
  -> ({0 a : Ty} -> gamma |- a -> delta |- a)
substitution f (Val x) = f x
substitution f (Lam x) = Lam (substitution (exts f) x)
substitution f (App x y) = App (substitution f x) (substitution f y)
substitution f Zero = Zero
substitution f (Succ x) = Succ (substitution f x)
substitution f (Case x y z) = Case (substitution f x) (substitution f y) (substitution (exts f) z)
substitution f (Mu x) = Mu (substitution (exts f) x)


-- substitution of one variable
subst1 : {0 gamma, a, b : _}
  -> gamma :< b |- a
  -> gamma |- b
  -> gamma |- a
subst1 x y = substitution {gamma = gamma :< b} replaceZero x
  where
    -- replace every occurence of `Here` with the variable y
    replaceZero : {0 c : Ty} -> c `In` gamma :< b -> gamma |- c
    -- if we find a variable at 0, we return `y` instead
    replaceZero Here = y
    -- if we find a variable that's not 0 we return a variable that's its
    -- predecessor. Because the new context is one variable smaller
    replaceZero (Later x) = Val x
