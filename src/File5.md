```idris
module File5

import Data.Fin
```

After getting accustomed to the algebra of data types we are going to add two new things:
type application, and substitution.

Type Application will allow us to instanciate types that have variables in them. A type
such as `Maybe` has one variable, once it's instanciated completely it will be something
like `Maybe Int` or `Maybe String`.

Effectively, applying a type to another type will replace all occurences of the variable
with the type we give in argument.

```idris
data Desc : Nat -> Type where
  Var : Fin n -> Desc n
  Zero : Desc n
  One  : Desc n
  Plus : Desc n -> Desc n -> Desc n
  Times : Desc n -> Desc n -> Desc n
  Mu : Desc (S n) -> Desc n
  Apply : Desc (S n) -> Desc n -> Desc n
```

We've just added one constructor `Apply` which requires its first argument to have at least
one variable, and another one that has one less variable in it.

We can now create the type maybe

```idris
MaybeDesc : Desc 1
MaybeDesc = Plus One (Var 0)

BoolDesc : Desc 0
BoolDesc = Plus One One

MaybeBool: Desc 0
MaybeBool = Apply MaybeDesc BoolDesc
```

`MaybeBool` now describes the type of `Maybe Bool`

What is now left is to implement `ToType` to accomodate for our additional constructor:

```
ToType : CFT n -> Vect n Type  -> Type
ToType (Var x) xs = index x xs
ToType Zero xs = Void
ToType One xs = Unit
ToType (Plus x y) xs = Either (ToType x xs) (ToType y xs)
ToType (Times x y) xs = Pair (ToType x xs) (ToType y xs)
ToType (Mu x) xs = Fix (ToType x . (:: xs))
ToType (Apply x y) xs = ?apply_type
```

I have left the implementation of `Apply` as a hole because it is not easy to come up with.
As a first attempt looking at the type of `apply_type` we see


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

```
ToType (Apply x y) xs =
  let arg = ToType y xs -- first we compute the argument
  in ToType x (arg :: xs) -- then we extend the context and compute x
```

However this does not work, try the following test:

That is because whenever we apply a type to a `Mu` we need to place the provided type in _second_
position in the context, rather than in first. Remember that the first position is reserved for the
recursive definition.


assume we want to write the following type :

```
ListOfList : Type -> Type
ListOfList a = List (List a)
```

and we want to instanciate it with the type `Nat`

```
ListOfListNat : Type
ListOfListNat = ListOfList Nat`
```

We would write this in our language as:

```
ListOfListDesc : CFT 1
ListOfListDesc = App ListDesc ListDesc

```
ListAppOne : CFT 0
ListAppone = (Mu (Plus One (Times (Mu (Plus One (Times (Var 2) (Var 0)))) (Var 0)))) `

ToType ListAppOne [Unit]
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
index. Variables come from uses of `Lam` which stands for _lambda_. The name comes from the
greek letter lambda, written λ, and was first used in the first definitions of the lambda
calculus. An identity function in the lambda calculus is written as `λx. x` where `λ` denotes
the beginig of a lambda declaration, the dot `.` separates the argument of the function with
its body and on the right side of the dot is the function body. The syntax can be summarised
as `λ *argument* . *body*`. Because we are going to use numbers instead of variables we are
going to write `λ 0` instead of `λx. x` to indicate that the variable is immediately used.

The translatio can be achieved by enumerating successive layers of λ and replacing the variable
names with their number. here is another example with the function `const` which ignores its
second argument:

```
const = λx. λy. x
 = λ1. λ0. 1
 = λ λ 1
```

`App` is just function application so if we want to apply a function to another we have
to give the function as a first argument to `App` and the argument as the second argument.

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
```




# Exercises


