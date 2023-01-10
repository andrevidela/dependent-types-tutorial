```idris
module File6

import Data.Fin
```

# Lambda Calculus

The lambda calculus is a foundational calculus that captures the essence of _computation_. Any
problem that can be written as a term in the lambda calculus can be "computed", in practice,
it means that we can make a computer perform the work described by our lambda term. The lambda
calculus is a great tool for learning about programming languages and type theory because it is
quite small, and can be extended in order to obtain more sophisticated languages.

At its core, the lambda calculus only has three constructs: Variables, Application, and Lambda
abstraction. So we can either refer to a variable from an argument we have, apply a function
to some value and create a function. The code will look fairly similar to what we have seen
with `CFT`:

```idris
namespace Lambda
  public export
  data LC : Nat -> Type where
    Var : Fin n -> LC n
    Lam : LC (S n) -> LC n
    App : LC n -> LC n -> LC n
```

Just like before we are going to keep track of how many variables are in scope using a `Nat`
index. Variables emerge from uses of `Lam` which stands for _lambda_. The name comes from the
greek letter lambda, written λ, and was first used in the first definitions of the lambda
calculus. An identity function in the lambda calculus is written as `λx. x` where `λ` denotes
the beginig of a lambda declaration, the dot `.` separates the argument of the function with
its body and on the right side of the dot is the function body. The syntax can be summarised
as `λ *argument* . *body*`. Because we are going to use numbers instead of variables we are
going to write `λ 0` instead of `λx. x` to indicate that the variable is immediately used.

The translation from variables names to numbers can be achieved by enumerating successive
layers of λ and replacing the variable names with their number. here is another example with
the function `const` which ignores its second argument:

```
const = λx. λy. x
 = λ1. λ0. 1
 = λ λ 1
```

`App` represents function application. To apply a function to another we combine the function
with its argument using the `App` constructor.

Let's say we have the functions `id = λx. x = λ0` and `const = λx. λy. x = λ λ 1` if we apply `const`
to `id` we write

```
App id const
```

In the lambda calculus we usuall write application using whitespace between identiers, just
like in Idris `f x y = (f x) y = App (App f x) y`.

Idris allows us to define custom operators that will make writing lambda calculus programs a
lot closer to what it is like to write informally. First we define `$$` as an infix operator
for `App`. Then we define `\\` as a prefix operator to replace `λ`

```idris
infixl 1 $$

($$) : LC n -> LC n -> LC n
($$) = App

prefix 2 \\

(\\) : LC (S n) -> LC n
(\\) = Lam
```

Finally we do not have to write `Var` every time we want to use a variable if we provide a
function `fromInteger` that returns a lambda calculus term of the correct variable:

```idris
fromInteger : (i : Integer) -> {n : Nat} -> {auto 0 check : So (integerLessThanNat i n)} -> LC n
fromInteger i = Var (fromInteger i)
```

We can check this works by writing the programs `const` and `id`:

```idris
-- λx. λy. x
const : LC 0
const = \\ \\ 1

-- λx. x
id : LC 0
id = \\ 0

constId : LC 0
constId = const $$ id $$ id
```

## Writing programs

The lambda calculus is very powerful but a little bit hard to decypher. For example, we can
implement conditionals witht the following encoding:

```
-- λx. λy. x
-- always use the first argument
true : LC 0
true = \\ \\ 1

-- λx. λy. y
-- always use the second argument
false : LC 0
false = \\ \\ 0
```

if we want to write the program that returns either `const` or `id` depending on a variable `b`
we can write `λb. b const id` or in our program

```idris
constOrId : LC 0
constOrId = \\ 0 $$ const $$ id
```

Numbers can also be represented in the lambda calculus, the encoding is as follows:

```
-- λx. λy. x
-- like const
zero : LC 0
zero = \\ \\ 1

-- λx. λy. λz. z (x y z)
-- λ2. λ1. λ0. 0 (2 1 0)
-- λλλ 0 (2 1 0)
--
succ : LC 0
succ = \\ \\ \\ 0 $$ (2 $$ 1 $$ 0)
```

Unfortunately that can be a little bit hard to read. To fix this we are going to build-in numbers
directly by providing two constructors `Zero` and `Succ` in the lambda calculus:


```
namespace LambdaNat
  public export
  data LCNat : Nat -> Type where
    Var : Fin n -> LCNat n
    Lam : LCNat (S n) -> LCNat n
    App : LCNat n -> LCNat n -> LCNat n
    Zero : LCNat n
    Succ : LCNat n -> LCNat n
```

We're missing one thing however and that's an induction principle in order to iterate over
natural numbers. in the church encoding of numbers this is taken care of by the numbers themselves
the numbers and their induction structure are one and the same. But here we need to teach our
language to deal with them. Induction on nat makes the rules under which recursion is ok explicit:
Either we are in the base-case because we've hit `Zero` or we are in an inductive case with `Succ n`.

```idris
namespace LambdaNat
  public export
  data LCNat : Nat -> Type where
    Var : Fin n -> LCNat n
    Lam : LCNat (S n) -> LCNat n
    App : LCNat n -> LCNat n -> LCNat n
    Zero : LCNat n
    Succ : LCNat n -> LCNat n
    Case : (scrutinee : LCNat n)
        -> (zero : LCNat n)
        -> (succ : LCNat (S n))
        -> LCNat n
    Mu : LCNat (S n) -> LCNat n

  export
  ($$) : LCNat n -> LCNat n -> LCNat n
  ($$) = App

  export
  (\\) : LCNat (S n) -> LCNat n
  (\\) = Lam

  export
  fromInteger : (i : Integer) -> {n : Nat} -> {auto 0 check : So (integerLessThanNat i n)} -> LCNat n
  fromInteger i = Var (fromInteger i)
```

I've given names to the different arguments of the `Case` constructor. The first argument is the number
we want to analyse, the second argument is what to do in case the number is `0`, the third one is
the program we run in the `Succ n` case. We see that the context is extended by one since the number
`n` is now in scope.

We can now print lambda terms and numbers so that we can see better what's going on:

```idris
  export
  print : LCNat n -> String
  print (Var n) = show n
  print (Lam body) = "λ \{print body}"
  print (App fn arg) = "\{print fn} \{print arg}"
  -- this is multi-line syntax in Idris
  print (Case v z s) = """
    case \{print v} of
        Zero => \{print z}
        Succ 0 => \{print s}
    """
  print n = either id show (fromNat n)
    where
      fromNat : LCNat _ -> Either String Nat
      fromNat Zero = Right Z
      fromNat (Succ n) = bimap ("S " ++) S (fromNat n)
      fromNat x = Left (print x)
```

With this we can write natural numbers much more easily:

```idris
one : LCNat n
one = Succ Zero

two : LCNat n
two = Succ (Succ Zero)
```

We are missing one more thing and that's a way to define recursion. Just like with our type descriptions
we need a way to have functions refer to themselves.

```idris
-- λx. λy. case x of Z => y ; (S n) => S (plus n y)
plus : LCNat 0
plus = Mu (\\ \\ Case 1 0 (\\ Succ (3 $$ 0 $$ 1)))
```

## Evaluate programs

In order to test our functions we need to evaluate them, for this we will use the following substitution:

```
(λx.f x) y
=
f y
```

```idris
subst : LCNat n -> Fin n -> LCNat n -> LCNat n
subst (Var i) index term = if i == index then term else (Var i)
subst (Lam b) index term = ?lamSub
subst (App f a) index term = ?appSub
subst Zero index term = ?zeroSub
subst (Succ n) index term = ?succSub
subst (Case n z s) index term = ?caseSubst
subst (Mu b) index term = ?mySUb
```


A problem with this implementation is that there is nothing stopping us from applying a function to something
that is not a function. Or give a function to the first argument of `Case`


# Exercises


