module Exercises.Test

import Data.Vect

xor : Bool -> Bool -> Bool
xor False True = True
xor True False = True
xor _ _ = False

addB : Vect 32 Bool -> Vect 32 Bool -> (Bool, Vect 32 Bool)
addB xs ys = foldr ?add_rhs (False, xs) ys
  where
    addCarry : Bool -> Bool -> Pair Bool Bool
    addCarry b1 b2 = MkPair (b1 `xor` b2) (b1 && b2)

    add3 : Bool -> Bool -> Bool -> Pair Bool Bool
    add3 x y z = let (c, r) = addCarry x y in (c, r || z)
