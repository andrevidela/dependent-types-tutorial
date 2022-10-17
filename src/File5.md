```idris
module File5

import Data.Fin
import Data.Vect
import Data.List.Elem

record Fix (f : Type -> Type)  where
  constructor Rec
  unFix : Lazy (f (Fix f))
```

After getting accustomed to the algebra of data types we are going to add two new things:
type application, and substitution.

Type Application will allow us to instanciate types that have variables in them. A type
such as `Maybe` has one variable, once it's instanciated completely it will be something
like `Maybe Int` or `Maybe String`.

Effectively, applying a type to another type will replace all occurences of the variable
with the type we give in argument.

```idris
namespace Application
  data CFT : Nat -> Type where
    Var : Fin n -> CFT n
    Zero : CFT n
    One  : CFT n
    Plus : CFT n -> CFT n -> CFT n
    Times : CFT n -> CFT n -> CFT n
    Mu : CFT (S n) -> CFT n
    Apply : CFT (S n) -> CFT n -> CFT n
```

We've just added one constructor `Apply` which requires its first argument to have at least
one variable, and another one that has one less variable in it.

We can now create the type maybe

```idris
  MaybeDesc : CFT 1
  MaybeDesc = Plus One (Var 0)

  BoolDesc : CFT 0
  BoolDesc = Plus One One

  MaybeBool: CFT 0
  MaybeBool = Apply MaybeDesc BoolDesc
```

`MaybeBool` now describes the type of `Maybe Bool`

What is now left is to implement `ToType` to accomodate for our additional constructor:

```idris
  ToType : CFT n -> Vect n Type  -> Type
  ToType (Var x) xs = index x xs
  ToType Zero xs = Void
  ToType One xs = Unit
  ToType (Plus x y) xs = Either (ToType x xs) (ToType y xs)
  ToType (Times x y) xs = Pair (ToType x xs) (ToType y xs)
  ToType (Mu x) xs = Fix (ToType x . (:: xs))
  -- ToType (Apply x y) xs = ?apply_type
```

if we look into the type of the hole `apply_type` we see that we are asked to return a
`Type` and are given both `CFT n` and `CFT (S n)`. We could just return `ToType y xs` because
the size of the context `xs` matches `y`, but that would be wrong because this would just
return the type of the _argument_ of the application.

```
 0 n : Nat
   y : CFT n
   x : CFT (S n)
   xs : Vect n Type
------------------------------
apply_type : Type
```

Beacuse we are given `x` and `y` we could just recusrively call `ToType` on y and use the result
to extend the context `xs` in order to have a value of type `Vect (S n) Type` and then
use `ToType again on `x` with our augmented vector:

```idris
  ToType (Apply x y) xs =
    let arg = ToType y xs -- first we compute the argument
    in ToType x (arg :: xs) -- then we extend the context and compute x
```

We can now write application of types with descriptions we've already seen. Here is the definition
of `Nat` as the application of `List` on `One`

```idris
  ListDesc : CFT 1
  ListDesc = Mu (Plus One (Times (Var 1) (Var 0)))

  ListType : Type -> Type
  ListType x = ToType ListDesc [x]

  NatDesc : CFT 0
  NatDesc = Apply ListDesc One

  NatType : Type
  NatType = ToType NatDesc []
```

## Exercises

- Add constructors for `Nil` and `Cons` of type `ListType`.

- Using those list constructors, build constructors for `Zero : NatType` and
`Succ : NatType -> NatType`.

- Implement booleans as the application of `Maybe` with `One`, and implement
  the `True` and `False` constructuer for it.

- Implement `Maybe` as the application of `Either` with `Zero`,

- Implement `Unit` as the application of `List` with `Zero`

# Programming limitations

One thing we cannot do that should work is that we cannot replace a variable by a term that has itself
variables.

For example the following will fail:

```idris
  Identity : CFT 1
  Identity = Var 0

  failing
    AppId : CFT 1
    AppId = Apply Identity MaybeDesc
```

This is because we required each application to be with a term that has strictly less variables. We
can cheat by allowing the context to be flexible and adding dummy variables:

```idris
  IdentityN : CFT (1 + n)
  IdentityN = Var 0

  AppId : CFT 1
  AppId = Apply IdentityN MaybeDesc
```

Here is another example that ought to work. We're applying `Either` to `List`
in hopes of creating a type that will be a list of eithers. The resulting type
should have two type variables, one for each side of the either.

```idris
  EitherDesc : CFT 2
  EitherDesc = Plus (Var 0) (Var 1)

  failing
    ListEitherDesc : CFT 2
    ListEitherDesc = Apply ListDesc EitherDesc
```

This was a little bit optimistic since even Idris does not allow us to write:

```idris
  failing
    EitherList' : Type -> Type -> Type
    EitherList' = List Either
```

But we can write

```idris
  EitherList : Type -> Type -> Type
  EitherList a b = List (Either a b)
```

Wouldn't it be nice if we could write those program in our type language?

Finally one important thing to mention is that we allow non-sensical type applications:

```idris
  Weird : CFT 0
  Weird = Apply One One
```

Clearly the type `One` has no variables in it so there is no sense in applying an argument
to it, and yet it works. This is becasue  we do not check that applications are done with
something that expects an _argument_ as input.

# Addressing limitations

To fix all those issues we are going to update our language with a _typing context_. That is,
in addition to keeping track of how many variables we need, we are also going to track what kind
of variables we are dealing with. In order to avoid any confusion between idris _types_ and the
types inside our language, we are going to call the later "kinds". This is also to remain consistent
with existing literature about haskell where the "type of types" is called a _kind_.

Our language, therefore, has two _kinds_: Either we are a plain kind,
like One, Zero, or a fully applied type like `Either Nat Nat`, or we are a function kind.
Function kinds can be applied but plain kinds cannot, `Maybe` is one because it expects
to be given a type argument before being fully applied.

```idris
infixr 1 =>>

data Kind : Type where
  Plain : Kind
  (=>>) : Kind -> Kind -> Kind
```

We use a custom operator to ease the reading of those kinds, I read the operator as the "fat arrow"
which is mean to be the idris analogous of `->`. Think of it as the outline of a regular
arrow.

Our typing context (or kinding context?) is now a list of kinds, rather than a natural number, here
is a helpful alias:

```idris
Context : Type
Context = List Kind
```

We need to keep track of an additional parameter and that is the kind of the term we are building.
Without it, we cannot ensure that we apply the correct values together. With context and kind
taken into account, our type declaration looks like this:

```idris
data TyC : (0 _ : Context) -> (0 _ : Kind) -> Type where
```

We rewrite our usual definitions as before but we adapt our types to match our new `Context` rather
than `Nat`.
Previously we used `Fin n` to ensure that our variables were within the range `n` of variables. Now,
we use the type `Elem` from `Data.List.Elem` which ensure we only refer to elements that
are present in the list. Here is what the documentation says about it:

```
Main> :doc Elem
data Data.List.Elem.Elem : a -> List a -> Type
  A proof that some element is found in a list.
  Totality: total
  Visibility: public export
  Constructors:
    Here : Elem x (x :: xs)
      A proof that the element is at the head of the list
    There : Elem x xs -> Elem x (y :: xs)
      A proof that the element is in the tail of the list
```

`Here` replaces our `FZ` and `There` replaces `FS`.

```idris
  -- a type variable, it has kind `e`
  Var : e `Elem` ctx -> TyC ctx e
```

The other definitions follow from what we've written for our previous implementation,
we just replace our variable counter `n` by a context variable `ctx`:

```idris

  -- Zero and One are plain types
  Zero : TyC ctx Plain
  One  : TyC ctx Plain

  -- Times only works on plain types
  Times : TyC ctx Plain
       -> TyC ctx Plain
       -> TyC ctx Plain

  -- Plus only works on plain types
  Plus : TyC ctx Plain
      -> TyC ctx Plain
      -> TyC ctx Plain

  -- Mu has kind `a`
  Mu : TyC (a :: ctx) a
    -> TyC       ctx a
```

We haven't implemented our application constructor and that's because we will actually need two
things for this to work.

Application can only work on a term of kind `a =>> b` and would only work if we provide if a term
of kind `a`, it would return a term of kind `b`. This is pretty much exactly function application
that you know from languages such as Idris:


```idris
  -- Type application
  App : {a : _}
     -> TyC ctx (a =>> b)
     -> TyC ctx a
     -> TyC ctx b
```

Now if we leave it at that we notice a problem. There is actually no way to create a value of kind
`a =>> b` which means we can never use the constructor. We therefore need to find a way to construct
values of `a =>> b`. To make up for this we introduce the constructor `Lam` which stands for "lambda"
or "lambda abstraction". It allows to change a term with a value `a` in context to a term without
the value in context but with a kind `a =>> b`.

```idris
  -- lambda abstraction
  Lam : TyC (a :: ctx) b
      ------------------
     -> TyC ctx (a =>> b)
```

Effectively it's the inverse operation of `App`. `App` removes instances of `a =>> b` and `Lam` creates
them.

The names don't lie, we ended up implementing the simply typed lambda calulus in our description languages.
While we do not have an interpreter or semantics for this language, we can build terms for them and they
will allways be correctly typed. Typically we cannot apply `One` to `One` anymore:

```idris
failing
  failApply : TyC [] Plain
  failApply = App One One
```

Here is how to implement `Either`:

```idris
EitherDesc : TyC (Plain :: Plain :: ctx) Plain
EitherDesc = Plus (Var Here) (Var (There Here))
```

## Exercises

- Implement `EitherLam : TyC ctx (Plain =>> Plain =>> Plain)`

- Implement `MaybeDesc` using `EitherLam` and `One`

- Implement `ListDesc`, it should be very similar to the version without contexts.

- Here is the same `Identity` as before but with typed contexts:

```idris
Identity : TyC [n] n
Identity = Var Here
```

- Apply `MaybeDesc` to `Identity` to achieve what was not possible with `CFT`

- Apply `EitherDesc` to `ListDesc` to obtain this signature:

```
ListEitherDesc : TyC ctx (Plain =>> Plain =>> Plain)
```

