```idris
module File3

import Iso

%hide Prelude.Bool
%hide Prelude.True
%hide Prelude.False
```

# Algebraic data types

We've seen how we can use functions to return types, in this section we are going
to use this feature to implement and understand what are _algebraic data types_.

The term _algebraic_ comes from the fact that data declaration follow an _algebra_,
a set of terms and operation on terms that can be interpreted in a given context.
For us, we are going to define the terms `0`, `1` and the operations `*` and `+`.
To those terms we are going to interpret them in the contex of _Idris Types_.

We use the following data declaration for our algebra of types:

```idris
data Desc : Type where
  Zero  : Desc
  One   : Desc
  Plus  : Desc -> Desc -> Desc
  Times : Desc -> Desc -> Desc
```

Where `Zero` represents the term `0` and `One` represents the term `1`. What is left
now is to interpret values of `Desc` as an idris type:

```idris
ToType : Desc -> Type
ToType Zero = Void
ToType One = Unit
ToType (Plus x y) = Either (ToType x) (ToType y)
ToType (Times x y) = Pair (ToType x) (ToType y)
```

This is where what we're doing becomes clear:

`Zero` is the term that represent the _type_ with `0` inhabitants. This type is called
`Void` in Idris. Similarly, `One` is the term that represents the _type_ with `1`
inhabitant (or 1 value) and this type is `Unit` in Idris, otherwise written as `()`.
The definitions for those types are as follow:

```
data Void : Type where
  -- nothing here

data Unit : Type where
  MkUnit : Unit
```

Idris has a slight idiocyntracie that both the _type_ `Unit` and the _value_ `MkUnit`
can be written as `()`. To avoid confusion we're going to write `Unit` and `MkUnit`
instead.

`Plus` and `Times` are represented as the types `Either` and `Pair`, this is because,
technically, those are the _coproduct_ and _product_ operators on types. _Coproducts_
allow you to obtain a _choice_ of values wheras _products_ give you multiple values
as once. This is exactly what `Either` and `Pair` give you respectively: a choice of
two values, and two values simultaneously.

Once our algbra of type has been defined we can start creating types, for example
the type `Bool` has only two values so it can be defined as

```idris
BoolDesc : Desc
BoolDesc = One `Plus` One
```

This algebra of types also explains why those types are _isomorphic_, that is, we
can conver from and to each other without losing any information:

```idris
BoolDesc1 : Desc
BoolDesc1 = One `Plus` (One `Plus` Zero)

BoolDesc2 : Desc
BoolDesc2 = Zero `Plus` (One `Plus` One)
```

### Exercises

#### Isomorphisms

Using the `Iso` type given in the file `Iso.idr`, prove that `ToType BoolDesc` is isomorphic to
`ToType BoolDesc` and `ToType BoolDesc2`

```idris

iso1 : ToType BoolDesc `Iso` ToType BoolDesc1

iso2 : ToType BoolDesc `Iso` ToType BoolDesc2

iso3 : ToType BoolDesc1 `Iso` ToType BoolDesc1
```

#### Functions


Write a type `DBool : Type` and its values, based on `BoolDesc`. Then implement `not`, `and`, `or`, `xor` on `BoolDesc`

```idris
DBool : Type

True : DBool

False : DBool

not : DBool -> DBool

and : DBool -> DBool -> DBool

or : DBool -> DBool -> DBool

xor : DBool -> DBool -> DBool
```

#### Extra credit

We can define types with any number of values but we cannot describe type _variables_.
We would like to describe types like `Either` and `Pair` with them.

Attempt a definition of `Desc` with variables and attempt a definition of `ToType`,
you might find it difficult, if so, why?

```
data DescVar : Type where

ToType2 : DescVar -> Type
```
