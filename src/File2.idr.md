
```idris
module File2

import Data.SortedMap
```

# Dependent types

Until now we've only seen dependent types as some additional information for
_data structures_ but dependent types are more generally useful as _programs_
that occur at the type-level. For example a function that returns an `Int` or
a `String` can be written like this:

```idris
intOrString : (b : Bool) -> if b then Int else String
intOrString True = 3
intOrString False = "three"
```
In this function `if b then Int else String` is a _function_ that return either
the type `Int` or the type `String`. We can give this function a name:

```idris
IntOrStringType : Bool -> Type
IntOrStringType b = if b then Int else String
```

Once this is setup we can call it in the _type_ of a function:

```idris
intOrString2 : (b : Bool) -> IntOrStringType b
intOrString2 True = 3
intOrString2 False = "three"
```
You will notice the `(b : Bool)` syntax is slightly different from what we've
seen before. Previously, we would only use `Bool`, but now we gave the argument a
name `b` and this allows us to use it in the rest of the signature. In this case
we used the name `b` for our `if _ then _ else _` function and in `intOrString2`
we used it to call the function `IntOrStringType`.

Another note about syntax is that we used _uppercase_ letter for `IntOrString`, this
is because lowercase identifiers are turned into _type variables_ and upper case ones
are left alone. We will see what type variables are in a later section.

## Types of types

Something curious you might have noticed is that the function `IntOrStringType` returns a
value of type `Type`. This is because values such as `Int`, `String`, `Nat` etc, are all
values of type `Type`. We are going to distinguish between _Types_ which are broad
descriptions of values (like `Int` is the classification for 32bit integers, `String`
is the classification of values which are character buffers, etc) and _values_ which are
computer objects which take up memory and are described by a type. So the number 3
is a value of type `Int` and the name "mark" is a value of type `String`. In the jargon
we say that _values inhabit a type_ or that a type is _inhabited_ by values.

In that context there are two intersting types: `Void` and `Unit`. `Void` is a type
that has no inhabitants, in other words, you cannot find a value that has the type
`Void`. `Unit` has exactly one value. Here is a table of some types and their values

| Types: | String | Int | Void | Unit | Bool | List Int |
|--------|--------|-----|------|------|------|----------|
| Values: | "hello", "", "a" | 0, 1, 2, ... | ∅ | () | False, True | Nil, [0], [3,4,5], ...|

Finally, the type `Type` is inhabited by values such as `Bool`, `Int`, `String`, `Void`, `Unit`, etc.
It describes all values that are types, and crucially, `Type` is of type `Type` itself

[^1]: The fact that `Type : Type` is a big problem if you want to use your type system as a logical
foundation, but this tutorial will mostly be focused on software engineering rather than formal logic

## Type aliases and Type-level functions

You noticed that `IntOrStringType` returns a value of type `Type`, and that it was used in the
type signature of the function `intOrString2`. It turns our that you can use _any program_ that
returns a type in a type signature. Typically a very common usage of this feature is type-aliases.

In lots of programming languages you can declare a different name as a shorthand for an existing type.
For example you might write:

```
typealias Users = List<String>
```

In idris this is unnecessary because we can now declare a new variable that return the type we
are trying to describe:

```idris
Users : Type
Users = List String
```

This also works for more complicated types, for example a type of maps between `String` and values:

```idris
Dict : Type -> Type
Dict a = SortedMap String a
```

You will notice that `Dict` is a _function_ which takes a `Type` in argument and returns a `Type`.

This means we can use it everywhere we expect a `Type` provided we give it a type. For example:

```
toDictionary : List (String, Int) -> Dict Int
```

The argument `Int` is passed to the function `Dict` in order to build the type `SortedMap String Int`.

## Type variables & implicit arguments

We just wrote `toDictionary : List (String, Int) -> Dict Int` to describe type-level functions, what would
happen if we wrote `toDictionary : List (String, a) -> Dict a` ? Well, if we try it out, we notice it just works:

```idris
toDictionary : List (String, a) -> Dict a
```

This is because when you write `List (String, a) -> Dict a` you are implicitly declaring an additional
variable `a`. In idris, any lower case identifier is assumed to be
a _type variable_, so in reality `toDictionary : List (String, a) -> Dict a` is syntax sugar for
`toDictionary : (a : Type) -> List (String, a) -> Dict a` where `a` is an additional argument to the function.

If we look at a simpler example, the identity function, we can explain the entire signature using what
we have seen before:

```idris
explicitIdentity : (a : Type) -> a -> a
explicitIdentity ty v = v
```

The first argument is the type of the value we are going to pass to the function identity and the second
is the value itself:

```idris
testIdentity : explicitIdentity String "hello" = "hello"
testIdentity = Refl
```

If you were to have to give the type as the first argument of `identity` for each call that would get annoying.
Thankfully, Idris is able to infer what the type should be and can insert the value of the first argument for you:

```idris
testIdentity2 : explicitIdentity _ True = True
testIdentity2 = Refl
```

Of course this is still more tedious than we would like to, instead we write arguments that should be inferrable
in curly braces `{` `}` to indicate that they are _implicit_:

```idris
identity : {a : Type} -> a -> a
identity v = v
```

This allow us to write `identity False` without having to give the argument `Bool` to it. Idris can insert it for you.



