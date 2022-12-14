```idris
module File4

import Data.Vect
```

For this module we are going to keep doing what we were doing last time. We left off with the following challenge:

> We can define types with any number of values but we cannot describe type _variables_.
> We would like to describe types like `Either` and `Pair` with them.

As a first attempt you might be tempted by the following data structure:

```
data Desc' : Type where
  Var   : String -> Desc'
  Zero  : Desc'
  One   : Desc'
  Plus  : Desc' -> Desc' -> Desc'
  Times : Desc' -> Desc' -> Desc'
```

To implement our `ToType` function we now need to provide a list of names with an associated type so that we
can extract the type for each varable.

But doing so will make it impossible to imlement our `ToType` function regardless:

```
ToType : List (String, Type) -> Desc' -> Type
ToType ctx (Var n) = ?what
```

Because we cannot ensure that the variable `n` can be found in the list `List (String, Type)`.
We could do it by returning `Maybe Type` but in that case it would be very clumsy to use `ToType`.

An easier solution is to limit the number of variables to 1:

```idris
data DescVar : Type where
  Var   : DescVar
  Zero  : DescVar
  One   : DescVar
  Plus  : DescVar -> DescVar -> DescVar
  Times : DescVar -> DescVar -> DescVar
```

This way we can implement `ToType` with the following signature :

```idris
ToType : DescVar -> Type -> Type
ToType Var ty = ty
ToType Zero ty = Void
ToType One ty = Unit
ToType (Plus x y) ty = Either (ToType x ty) (ToType y ty)
ToType (Times x y) ty = Pair (ToType x ty) (ToType y ty)
```

We now see that we can define data structures with one single variable in them. The other observation we make
is that `ToType` is now a _Functor_ because it goes from `Type` to `Type`.

We can define our first type with variables: Maybe. Maybe has two values, either we have _nothing_ or we have
_something_ we call them `Nothing` and `Just`, and traditionally define them like this: 
`data Maybe a = Nothing | Just a`. The nothing case carries no value but the something case carries a value
of the type of the variable.
Because we are given a choice of two constructors we are going to represent this with a `Plus`, the `Nothing`
case will be represented with `1` and the `Just` case will be handled by our variable:

```idris
MaybeDesc : DescVar
MaybeDesc = Plus One Var
```

In algebraic terms, our maybe type can be defined as `Maybe a = 1 + a`.

### Exercise

Ensure that `ToType` defined as above is a functor.

```idris
IsFunctor : (a -> b) -> (ctx : DescVar) -> ToType ctx a -> ToType ctx b
```

Write a type description that holds the same type three times.

```idris
Three : DescVar

ThreeTy : Type -> Type
ThreeTy = ToType Three

MkThree : (a : Type) -> a -> a -> a -> ThreeTy a

get1 : ThreeTy a -> a
get2 : ThreeTy a -> a
get3 : ThreeTy a -> a
```

## Multiple variables

While using one variable is useful, it is not useful enough to write types such as `Pair` or `Either`.

To implement multiple variables, we are going to use two tricks:
- Write variables as numbers
- Use Vectors instead of Lists to track our context.

Using numbers will work the same way as using `String`, the difference is that the number now needs to point
to a value in context. This way `Pair a b` will really be `Pair [a, b]` and `0` to refer to the first variable
and `1` to refer to the second variable.

Additionally, this enables us to write `index n ctx` and always return a values from our context. This is what
we've seen during the second set of exercises: safe indexing into a list.
Recalling those exercises, you will notice that the type of `index` is `Fin n -> Vect n a -> a`. This means
that the size of the index must match the size of the vector. How do we achieve that?
We need to _index_ our Descriptions with the number of variables it has so that we can match it with the size
of the context:

```idris
namespace Variables
  data Context : Nat -> Type where
    Var   : Fin n -> Context n
    Zero  : Context n
    One   : Context n
    Plus  : Context n -> Context n -> Context n
    Times : Context n -> Context n -> Context n
```

From this we can write the function `ToType` given a vector of `n` Types if the description
contains `n` variables.

```idris
  ToType : Context n -> Vect n Type  -> Type
  ToType (Var x) xs = index x xs
  ToType Zero xs = Void
  ToType One xs = Unit
  ToType (Plus x y) xs = Either (ToType x xs) (ToType y xs)
  ToType (Times x y) xs = Pair (ToType x xs) (ToType y xs)
```

With this we can now write the description for the types `Either`, `Pair` and more.

### Exercises

Write the descriptions for the types `Either`, `Pair` as well as:

```
data Tri a b c = First a | Second b | Third c

data EitherBoth a b = Left a | Right b | Both a b

data Triple a b v = MkTriple a b c
```

## Lists and recursive types

Our updated version does not allow to write types that have a resursive structure like `Nat`,
`List` and `Tree`.

To fix that we are going to add a new constructor that describe types that reference themselves.
For this we are going to use the convention that any expression under that constructor have their
first variable, variable 0, to be a reference to itself.

```idris
namespace Recursive
  public export
  data CFT : Nat -> Type where
    Var   : Fin n -> CFT n
    Zero  : CFT n
    One   : CFT n
    Plus  : CFT n -> CFT n -> CFT n
    Times : CFT n -> CFT n -> CFT n
    Mu    : CFT (S n) -> CFT n
        --   ▲
        --   └ When under `Mu` the 0 variable refers to itself
```

We renamed our description of types 'CFT' for _Context Free Types_ which is the name given to them
by Michael Abbots in his thesis.

The problem now it that we cannot implement our `ToType` function because of the recursive nature
of `Mu`.


```idris
  ToTypeFail : CFT n -> Vect n Type  -> Type
  ToTypeFail (Var x) xs = index x xs
  ToTypeFail Zero xs = Void
  ToTypeFail One xs = Unit
  ToTypeFail (Plus x y) xs = Either (ToTypeFail x xs) (ToTypeFail y xs)
  ToTypeFail (Times x y) xs = Pair (ToTypeFail x xs) (ToTypeFail y xs)
  ToTypeFail (Mu x) xs = ?what
```


We cannot write `ToType x xs` because we need to extend the context with a new type. This makes
sense since we said that whenever we find ourself under a `Mu` we create a new variable at index
`0` which refers to the type itself. But doing do results in the infinite loop:


```
  ToTypeFail (Mu x) = ToType x (ToType (Mu x) xs :: xs)
```

For this to work we are going to need a new trick: fixpoints

## Fixpoints

In mathematucal vocabulary a fixpoint is a function and a value for which applications
of the function changes nothing: `x = f(x)`

To fix our `Mu` problem, we are going to use the equivalent structure but for types:

```idris
  record Fix (f : Type -> Type) where
    constructor In
    unFix : Inf (f (Fix f))
```

The `Fix` type takes a Functor `f : Type -> Type` and carries a value of type `f (Fix f)`.
If we apply this to the `Maybe` type we notice that the possible inhabitants are

```
Nothing
Just Nothing
Just (Just Nothing)
...
```

If you look at the hole in the value `In (Just ?here)` you will notice that the type of
`here` is the same as the outside type. This is how we are going to use `Fix`, as a way
to infinitely nest expressions.

Additionally, we've just encoded `Nat` using `Fix Maybe` and the reason for this can be
understood using our description of `Maybe`. We've defined as `1 + n` where `n` is our
type variable. If we replace `n` by `1 + n` we obtain `1 + (1 + n)` if we keep this
process going we can generate any natural number.

Using our fixpoint type we can implement the type of `Mu` to be

```
  ToType (Mu x) xs = Fix (\self => ToType x (self :: xs))
```

Our final version looks like this:

```idris
  export
  ToType : CFT n -> Vect n Type  -> Type
  ToType (Var x) xs = index x xs
  ToType Zero xs = Void
  ToType One xs = Unit
  ToType (Plus x y) xs = Either (ToType x xs) (ToType y xs)
  ToType (Times x y) xs = Pair (ToType x xs) (ToType y xs)
  ToType (Mu x) xs = Fix (\self => ToType x (self :: xs))
```
## Exercises

Define `Nat`, `List` and `Tree`.

```idris
NatDesc : CFT Z

NatTy : Type
NatTy = ToType NatDesc []

ListDesc : CFT (S n)

ListTy : Type -> Type
ListTy ty = ToType ListDesc [ty]

TreeDesc : CFT (S n)
TreeTy : Type -> Type
```

Define the constructors :

```idris
Z : NatTy

S : NatTy -> NatTy

Empty : (a : Type) -> ListTy a
Cons : (a : Type) -> a -> ListTy a -> ListTy a

Leaf : (a : Type) -> TreeTy a
Branch : (a : Type) -> a -> TreeTy a -> TreeTy a -> TreeTy a
```

Then write addition for our custom `Nat`, length for `List` and `inorder : Tree a -> List a`.

```idris
add : NatTy -> NatTy -> NatTy

length : ListTy a -> NatTy

inorder : TreeTy a -> ListTy a
```
