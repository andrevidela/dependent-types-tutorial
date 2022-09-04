```idris
module Exercises.File2
```


## Exercices implicits and type-level functions

For this series of exercises we are going to be explicit about all the types we introduce, for this we use
this pragma that will make sure you declare every argument you use in your function, including the type
arguments.

```idris
%unbound_implicits off
```

### Reverse a list

The first exercise is an explicit version of `reverse` which takes an extra argument for the type of the
content of the list.

```idris
failing
  reverseFail : List a -> List a

reverse : (a : Type) -> List a -> List a
```

### Ad-hoc vectors

We've seen how to use vectors to ensure the length of lists is tracked in the type. We can actually write a function
that create data types that _look like_ vectors without creating a new datatype.

```idris
Vect : Nat -> Type -> Type
Vect Z ty = Unit
Vect (S n) ty = Pair ty (Vect n ty)
```

This function returns the type `Unit` when the vector is meant to be empty (length `Z`) and returns _the type of pairs_
which contain a value of type `ty` as a first element and another vector of length 1 shorter than the one we started
with.

This way, given `Vect 3 Nat` we expect a triple of three `Nat`.

With this we can re-implement the operations we've impelmented before but without relying on a new data declaration.

First, complete the type signature of `zip` such that every argument is declared explicitly. Your code should
compile without the `failing` block. Then implement the function.

```idris
failing
   zip : -- add the arguments here
      (n : Nat) -> (a -> b -> c) -> Vect n a -> Vect n b -> Vect n c
```

Here is a test that you program should pass:

```idris
vect1 : Vect 3 String
vect1 = ("hello", "world", "!", ())

zipTest : File2.zip 3 (++) File2.vect1 File2.vect1
        = ("hellohello", "worldworld", "!!", ())
zipTest = Refl
```

Another staple function of vectors is the `map` function which respects the length of the vectors.

Same as before, add the missing arguments and implement the function

```
failing
  map : (a -> b) -> Vect n a -> Vect n b
```

Your implementation should allow the following test to pass

```idris
mapTest : map 3 String.length File2.vect1 = (5, 5, 1, ())
mapTest = Refl
```

### Ad-hoc Fin

Just like Vect, we can write a function that constructs data types that _look like_ `Fin` without actually having
to declare `Fin`.

```idris
Fin : Nat -> Type
Fin Z = Void
Fin (S n) = Either Unit (Fin n)
```

If we have `Fin` and we have `Vect` we should be able to recover our `index` function from before.
Careful, you may have to deal with _impossible patterns_.

```idris
index : {a : Type} -> (n : Nat) -> Fin n -> Vect n a -> a
```

here is a test your implementation should pass:

```idris
indexTest : index 3 (Right (Left ())) File2.vect1 = "world"
indexTest = Refl
```


