# File 0, lists and vectors

Content:

- Syntax for data declarations
- Syntax for functions
- List and Nat examples
- List length and Nat addition

## Preamble about syntax

This is how we start a new module. This is file number 0 so we are going to call it `File0`

```idris
module File0

%hide Prelude.List
%hide Prelude.Nat
%hide List.length

```
Here is how to define new data structures:

```idris
data Nat = Z -- Z for Zero
         | S Nat -- S for Successor
```

This represents "natural numbers", the set of whole numbers starting from 0 and increasing from there.
We will see how this is a very useful data structure for dependent types.

Here is a definition of lists:

```idris
data List a = Empty
            | Node a (List a)
```

This defines a list with two constructors, either the list is empty (`Nil`) or the list is
a node that contains an element of type `a` and a pointer to the rest of the list. Note that
`a` here means that the content of the list could be anything, it's a placeholder for whatever
the content is going to be when you instanciate the list.

Functions are written like this:

```idris
length : List a -> Nat
length Empty = Z
length (Node x xs) = S (length xs)
```

`length : List a -> Nat` declares the name and type of the function, here it takes a `List` and returns a `Nat`.

Coming from other programming languages, you might be tempted to use `int` as a return value for this function
but `Nat` has multiple benefits:

- It's strictly positive, you cannot represent negative numbers, which makes sense if you want to represent the length of a list for example
- It's infinite
- It's defined recursively which makes it a prime candidate for writing proofs, `Int` is a primitive type, which makes writing proofs difficult

[^1]: `Nat` are converted to `Int` internally so they aren't too slow to work with.

Back to `length`, the two other lines are the _body_ of the function and they are defined via _pattern matching_:

	length Empty = Z

means "in case the list is empty, return the `Nat` `Z`".

	length (Node x xs) = S (length xs)

means "in case the list contains an element, return `S (length xs)` which is the successor of `length xs` which itself is the length of the rest of the list.

In other words, if we're empty we return the number `0` if we are not empty we recursively compute the size of the list and we add `+ 1` to it.

## Indexed data structures

Dependents types allow us to add information to our type definitions, we call this an _index_. For this we use a slightly different syntax:

```idris
data Fin : Nat -> Type where
  FZ : Fin (S n)
  FS : Fin n -> Fin (S n)
```

This describes a number that is at most `n` if its type is `Fin n`. The name stands for `Finite`. Here are a couple of examples:

- The number `0` is smaller than 3, therefore is can be represented with the value `FZ : Fin 3`
- The number `3` is smaller than 4, therefore it can be represented with the value `FS (FS (FS FZ)) : Fin 4`
- The number `0` is not smaller than `0` therefore we cannot represent it. In other words, there is no value that has the type `Fin 0`
- The number `5` is not smaller than `5` therefore any representation of it must be of type `Fin 6` or more. `Fin 5` does not contain
the number `5`.

```idris
data Vect : Nat -> Type -> Type where
  Nil : Vect Z a
  (::) : a -> Vect n a -> Vect (S n) a
```

This describes a list with a `Nat` index. We've setup the constructors such that the `Nat` index represents the length of the list.
Let's go through the definition line by line:

    data Vect : Nat -> Type -> Type where

This line declares what is the signature of the type `Vect`. In order to be a valid type `Vect` requires a `Nat` (its length) and a `Type` (its content).

`Nil : Vect Z a` is our first constructor and it takes no arguments and constructs a value of type `Vect Z a`. This means a vector of length `Z` (zero) containing values of type `a`. You will notice we haven't specified `a` anywhere, this means that `a` could be anything. Indeed an empty vector could contain any sort of value!

`(::) : a -> Vect n a -> Vect (S n) a` is our second constructor and it takes two arguments, a value of type `a` which is the value that is contained in this node of the list. And a value of type `Vect n a` which is the rest of the list. The rest of the list has length `n` which means, by adding a new element to the list we construct a vector `Vect (S n) a` where `(S n)` increases the size of our vector by 1.

Finally, notice that we have used different names for the constructors of `Vect` than for list. We used `Nil` and the operator `(::)` for
what we called `Empty` and `Node` before. Since the second operator is an _infix operator_ we construct values of type `Vect` like this:

```idris
myVect : Vect (S (S (S Z))) Nat
myVect = Z :: S Z :: S (S Z) :: Nil
```

The benefit of using those names is that idris has some special _syntactic sugar_ that allow us to write `[Z, S Z, S (S Z)]` instead, which
is a lot more readable.

Finally, using `Z` and `S` in order to write numbers is quickly becoming tedious, so we are going to make use of another feature from Idris
in order to convert number that you type into values of `Nat`.

```idris
fromInteger : Integer -> Nat
fromInteger x = if x <= 0 then Z else S (fromInteger (x - 1))
```

And now we can write:

```idris
myVect2 : Vect 4 Nat
myVect2 = [0, 1, 2, 3]
```

# Exercises

### List concatenation

Implement the following function:

	concat : List a -> List a -> List a

### List access

	indexAt : Nat -> List a -> Maybe a

	head : List a -> Maybe a

	tail : List a -> Maybe (List a)

Is there a way to get rid of the `Maybe`??

### List Zip

Implement the `zip` function on lists which pairs up each element

	zip : List a -> List B -> List (a, b)


### Vector Concatenation

	concatVect : Vect n a -> Vect m a -> Vect (n + m) a


What is wrong with

	concatVect' : Vect n a -> Vect m a -> Vect (m + n) a

and is there a way to fix it?

### Vector Zip

	zipVect : Vect n a -> Vect n b -> Vect n (a, b)
	zipWithVect : (a -> b -> c) -> Vect n a -> Vect n b -> Vect n c

### Vector access

	indexAt : Fin n -> Vect n a -> a

	head : Vect (S n) a -> a

	tail : Vect (S n) a -> Vect n a


### Matrix map

	map : (a -> b) -> Matrix m n a -> Matrix m n b


### Matrix col & line

	col : Fin n -> Matrix m n a -> Vect m a

	line : Fin m -> Matrix m n a -> Vect n a


### Matrix transpose

	transpose : Matrix m n a -> Matrix n m a


