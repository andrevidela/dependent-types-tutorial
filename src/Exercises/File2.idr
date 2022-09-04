module Exercises.File2


data Sum : (0 _ : Type) -> (0 _ : Type) -> Type where
  L : a -> Sum a b
  R : b -> Sum a b


0 TNat : Type
TNat = Sum () TNat

add : TNat -> TNat -> TNat
add (L ()) r = r
add (R n) r = Right (add n r)

mult : TNat -> TNat -> TNat
mult (L ()) n = Left ()
mult (R m) n = n `add` mult m n

addTest : File2.add (Right (Right (Right (Left ())))) (Right (Left ())) = Right (Right (Right (Right (Left ()))))
addTest = Refl

multTest : File2.mult (Right (Right (Right (Left ())))) (Right (Left ())) = Right (Right (Right (Right (Right (Left ())))))
multTest = Refl

-- concat (Left ()) ys = ys
-- concat (Right (MkPair x xs)) ys = Right (x, concat xs ys)
--
-- concatTest : concat (Right (False, Right (True, Left ()))) (Right (True, Left ()))
--            = Right (False, Right (True, Right (True, Left ())))
-- concatTest = Refl

--    ## Exercices implicits and type-level functions
--
--    For this series of exercises we are going to be explicit about all the types we introduce, for this we use
--    this pragma that will make sure you declare every argument you use in your function, including the type
--    arguments.
--
--    ```idris
%unbound_implicits off
--    ```
--
--    ### Reverse a list
--
--    The first exercise is an explicit version of `reverse` which takes an extra argument for the type of the
--    content of the list.
--
--    ```idris
failing
  reverseFail : List a -> List a

reverse : (a : Type) -> List a -> List a
reverse ty [] = []
reverse ty (x :: xs) = reverse ty xs ++ [x]
--    ```
--
--    ### Ad-hoc vectors
--
--    We've seen how to use vectors to ensure the length of lists is tracked in the type. We can actually write a function
--    that create data types that _look like_ vectors without creating a new datatype.
--
--    ```idris

Vect : Nat -> Type -> Type
Vect Z ty = Unit
Vect (S n) ty = Pair ty (Vect n ty)

zip : {a : Type} -> {b : Type} -> {c : Type} ->
      (n : Nat) -> (a -> b -> c) -> Vect n a -> Vect n b -> Vect n c
zip Z f xs ys = ()
zip (S n) f (x, xs) (y, ys) = (f x y, zip n f xs ys)

vect1 : Vect 3 String
vect1 = ("hello", "world", "!", ())

zipTest : File2.zip 3 (++) File2.vect1 File2.vect1
        = ("hellohello", "worldworld", "!!", ())
zipTest = Refl

map : {a : Type} -> {b : Type} -> (n : Nat) -> (a -> b) -> Vect n a -> Vect n b
map Z f () = ()
map (S n) f (x, xs) = (f x, map n f xs)


mapTest : map 3 String.length File2.vect1 = (5, 5, 1, ())
mapTest = Refl

--    ```
--
--    ### Ad-hoc Fin
--
--    Just like Vect, we can write a function that constructs data types that _look like_ `Fin` without actually having
--    to declare `Fin`.
--
--    ```idris
Fin : Nat -> Type
Fin Z = Void
Fin (S n) = Either Unit (Fin n)
--    ```
--
--    If we have `Fin` and we have `Vect` we should be able to recover our `index` function from before.
--
--    ```idris
index : {a : Type} -> (n : Nat) -> Fin n -> Vect n a -> a
index Z _ _ impossible
index (S n) (Left ()) (x, xs) = x
index (S n) (Right ns) (x, xs) = index n ns xs
--    ```

indexTest : index 3 (Right (Left ())) File2.vect1 = "world"
indexTest = Refl
