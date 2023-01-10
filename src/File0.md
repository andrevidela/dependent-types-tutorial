# File 0

Welcome to this series of tutorial on dependent types. The goal of this document is to introduce someone to dependently
typed theories by using and implementing them. The files are written in _literate idris_ code which allows you compile the file
and play with the code.

This tutorial is aimed as people who are already familiar with functional programming but not necessarily with dependent types.

## Installation

Before we jump into the code, you will need to install Idris & it's associated tools.
For this I recommend you use [pack](https://github.com/stefan-hoeck/idris2-pack).

Once installed, we can start with the tutorial, there are multiple ways to use Idris with this tutorial:

- Using an editor that supports LSP
- Using and editor that supports the IDE mode
- Using the REPL

### Using LSP

You can use any editor that supports LSP, the github page for the idris-lsp project details the installation details.
Additionally you can use `pack` to install idris and idris-lsp:

LSP editors include VSCode, vim, nvim, emacs, sublime text and more. The editor with the most documentation around it
LSP support is VSCode and for this reason I suggest you use it.

It is worth noting that VSCode will not identify `.md` files as being idris files. For this, you need to change
the file type to "literate idris" once you open it in VSCode. This will enable LSP on the code snippets.

You can install the LSP with pack as well

### Using IDE mode

You can use the native IDE mode of Idris2. If you use vim, there is a plugin to support IDE mode here. If you use emacs
there is another plugin here.

### Using the REPL

If you are accustomed to interacting with programs through a REPL, you can use Idris through its repl. For this, run
`rlwrap idris2 --find-ipkg` in the `src` directory of the project. This will run the idris2 REPL, allow you to use arrow
movement thanks to `rlwrap` and will compile files that you can load with `:l "src/File0.md"`. Do not forget the quotation
marks around the filepath.


Once you've chosen your editor and installed idris and its tools, we can get started with a short summary of what you need
to know to use Idris effectively.

## Syntax

This is how we start a new module. This is file number 0 so we are going to call it `File0`

```idris
module File0
```

Because we are going to re-declare some types we will use `%hide` to hide them from the standard library. This way the built-in
version of those types will not clash with the ones we are going to define now.

```idris
%hide Prelude.List
%hide Prelude.Nat
%hide List.length

```

Here is how to define new data structures:

```idris
data Nat : Type where
  Z : Nat        -- Z for Zero
  S : Nat -> Nat -- S for Successor
```

This represents "natural numbers", the set of whole numbers starting from 0 and increasing from there.

```
  ┌ keyword to start a data declaration
  │
  │          ┌ The signature of the type we are describing
╭─┴─╮      ╭─┴─╮
data Nat : Type where
     ╰┬╯
      └ The name of the type we are definint
```

The body of the definition hosts the _constructors_ of the type. `Nat` has two _constructors_ either `Z` which
represents the number `0`. or `S` which takes a nat in argument and represents the successor of the argument.

```
  Z : Nat        -- Z for Zero
  S : Nat -> Nat -- S for Successor
```

This way `S Z` is the number `1`, `S (S Z)` the number `2` etc.

Nats may seem like an inefficient way to represent numbers but they are very useful because they are defined
_inductively_ rather than with a array of bits. This makes them particularly suitable for proofs. The compiler
does the necessary work to represent them as plain `Int` when the program is executed.


We move on to a more complicated type: Linked lists, or just `List`:

```idris
namespace List
  public export
  data List : Type -> Type where
    Nil : List a
    (::) : a -> List a -> List a
```

This defines a list with two constructors, either the list is empty (`Nil`) or the list is
a node that contains an element of type `a` and a pointer to the rest of the list. Note that
`a` here means that the content of the list could be anything, it's a placeholder for whatever
the content is going to be when you instanciate the list.

Functions are written like this:

```idris
length : List a -> Nat
length Nil = Z
length (x :: xs) = S (length xs)
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

This tutorial series will be very focused on exercises, and that is why it is written in a literate style. This way
you can open this file in your favorite editor with Idris2 support and start playing with the examples. The exercises
have a correction, but don't let it influence your achievements too much. If you managed to make the program that was
asked for, and the tests pass, then you deserve full credit.

## Exercises: Lists

### List notation, namespaces & exports

Go back to your existing definition of `List` and change the name of the constructors to use `Nil` and `(::)` in order to
enable the list syntax sugar. If you do this without any further changes you will get an error (actually a lot of errors).

Those are due to the name clash between the constructors for `List` and the constructors for `Vect`, they are both `Nil` and
`(::)`. To resolve this issue, you will have to place them in different _namespaces_ in order to allow idris to disambiguate
between the two. To use a namespace, write `namespace` at the top level and indent the definitions that will living within the
namespace. The namespace also needs a name, pick one that captures the kind of content you would find within it.

For examples if you have

    definition1
    definition2

And you want to put them in a namespace, do:

    namespace MyDefinitions
        definition1
        definition2

This will place `definition1` and `definition2` in the namespace `MyDefinitions`. Finally, the namespace's name must start
with a capital letter.

Even after doing all this you will encounter another error: impossible to use the constructors for list. That is because
using namespaces encapsulates the definitions within it, to make them usable from outside the namespace we need to _export_
them. Idris has 2 export mechanisms: `export` and `public export`. The first one exports the definition name and its type, the second
one exports the definition name, it's type, and its implementation, this is important for proofs. If the definition you are
exporting is a data structure, `export` will provide the type and `public export` will provide the type _and the constructors_
which are necessary in order to create values and perform pattern matching. Since we want to use our list from outside the module
and we want to use its constructors, we need to use `public export`. Here is the same example as before, but with export directives:

    namespace MyDefinitions
        public
        definition1

        public export
        definition2

You are now ready to finish this assignment, what you have left to do is convert the existing definitions that used `Empty` and `Node`
to `Nil` and `(::)`, you can also use bracket `[…]` notation.


### List concatenation

Implement the following function:

```idris
concat : List a -> List a -> List a
```

The following tests should pass:

```idris
-- catEmpty : File0.concat [1,2,3] [] === [1,2,3]
-- catEmpty = Refl

-- emptyCat : File0.concat [] [3,4,5] === [3,4,5]
-- emptyCat = Refl

-- normalCat : File0.concat [1,2,3][4,5,6] === [1,2,3,4,5,6]
-- normalCat = Refl
```

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


notes for next time:
- Exercises too easy?
- What to do with the correction?
    - Give explanation with corrections
    - Diff
- Maybe more theory?
    - exercises
- How to steer toward a solution that makes use of the previous definitions?
    - Present this as a challenge (try to do this only using 3 functions)
    - speed golf? space golf?
- editor/interactive features?
    - vscode
    - idris-lsp
      - :t id
      - holes
      - :doc
      - :browse
- programming games
    - Shenzhen IO
    - Factorio
    - Minecraft redstone
    - Human resource machine
