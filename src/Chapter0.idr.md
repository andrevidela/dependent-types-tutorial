# Chapter 0

Welcome to this series of tutorial on dependent types. The goal of this document is to introduce someone to dependently
typed theories by using and implementing them. The files are written in _literate idris_ code which allows you compile the file
and play with the code.

This tutorial is aimed as people who are already familiar with functional programming but not necessarily with dependent types. You will need to be familiar with idris/haskell/ml syntax to understand the code and write your own solutions.

## Installation

Before we jump into the code, you will need to install Idris & its associated tools.
For this I recommend you use [pack](https://github.com/stefan-hoeck/idris2-pack). 

Once installed, we can start with the tutorial, there are multiple ways to use Idris with this tutorial:

- If you are using `pack`, install the LSP server with `pack install-app idris2-lsp`, and use an editor that supports LSP, for example:
    - [VSCode](https://code.visualstudio.com) with the associated [lsp plugin](https://github.com/bamboo/idris2-lsp-vscode)
    - [neovim](https://neovim.io) with [idris2 integration](https://github.com/ShinKage/idris2-nvim)
- Using and editor that supports the IDE mode:
    - [idris2-mode for emacs](https://github.com/idris-community/idris2-mode)
    - [idris2-mode for vim](https://github.com/edwinb/idris2-vim)
- Using the [REPL](https://idris2.readthedocs.io/en/latest/tutorial/interactive.html#editing-at-the-repl)

## Using the REPL

Using the REPL is the least infrastructure-heavy solution, if you are not familiar with LSP or compiler plugins, I suggest you stick with the REPL.

Because the REPL does not support arrow movement, I also suggest you install `rlwrap` using your system's package manager.

To invoke the repl with the project'd settings, you need to go into the `src` directory and call `rlwrap idris2 --find-ipkg`. This will invoke the REPL and you should see

```
     ____    __     _         ___
    /  _/___/ /____(_)____   |__ \
    / // __  / ___/ / ___/   __/ /     Version 0.7.0
  _/ // /_/ / /  / (__  )   / __/      https://www.idris-lang.org
 /___/\__,_/_/  /_/____/   /____/      Type :? for help

Welcome to Idris 2.  Enjoy yourself!
Main>
```

You can now load files, this will compile them and allow you to ask questions about them. For example, to load this file, type `:l src/File0.idr.md`. You should see

```
Main> :l "src/File0.idr.md"
1/1: Building File0 (src/File0.idr.md)
Loaded file src/File0.idr.md
File0>
```

Now you can ask the type of definitions in scope with `:t`. For example, to get the type of the `putStrLn` function that prints some text in the console, type: `:t putStrLn` and you should get

```
File0> :t putStrLn
Prelude.putStrLn : HasIO io => String -> io ()
```

If you changed the file and want to recompile it, use `:r` or `:reload`.

If you see a syntax construct that you don't know about, or forgot, try to ask for their documentation with `:doc`, for example:

```
File0> :doc infixl
Fixity declarations:

  Operators can be assigned a priority level and associativity. During parsing
  operators with a higher priority will collect their arguments first and the
  declared associativity will inform how subterms are grouped.

  For instance the expression `a + b * c * d + e` is parsed as
  `(a + ((b * c) * d)) + e` because:
    `(+)` is at level 8 and associates to the left
    `(*)` is at level 9 and associates to the left
```

`:doc` also works for your own definitions & library definitions, and will give you some more information beside the type `:doc putStrLn`:

```
File0> :doc putStrLn
Prelude.putStrLn : HasIO io => String -> io ()
  Output a string to stdout with a trailing newline.
  Totality: total
  Visibility: export
```
```
File0> :doc IO
data PrimIO.IO : Type -> Type
  The internal representation of I/O computations.
  Totality: total
  Visibility: export
  Constructor: MkIO : (1 _ : PrimIO a) -> IO a
  Hints:
    Applicative IO
    Functor IO
    HasLinearIO IO
    Monad IO
```

If you type an expression in the REPL like the string `"Hello World"`, you will only get the value printed out

```
File0> "Hello World"
"Hello World"
```

You can set the `showyypes` option to see the type of the expression

```
File0> :set showtypes
File0> "Hello World Again"
"Hello World Again" : String
```

If you are looking for a function from a module, but you cannot quite remember the name, you can look at all the definitions exported by a module by using `browse`.

```
:browse Prelude
```

The above will show all the functions exported by `Prelude`, the standard library of Idris.

If you write a program that interacts with the system using `IO` and want to run it, you need to use `:exec`

```
File0> :exec putStrLn "hello"
hello
```

### Recap

- `:t` to get the type of something.
- `:l` to load a file.
- `:r` to reload a file.
- `:doc` to obtain documentation.
- `:browse` to see all the definitions of a module.
- `:exec` to execute `IO` programs.

## Syntax

This is how we start a new module. This is file number 0 so we are going to call it `File0`

```idris
module File0
```

Because we are going to re-declare some types we will use `%hide` to hide them from the standard library. This way the built-in
version of those types will not clash with the ones we are going to define now.

```idris
%hide Prelude.List
%hide List.length

```

Here is how to define new data structures:

```
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

```
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
