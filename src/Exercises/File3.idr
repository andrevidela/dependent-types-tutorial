module Exercises.File3

import Data.List
import Data.Fin
import Data.Vect
import Data.Vect.Quantifiers
import Language.JSON
import Iso

%hide Prelude.Bool
%hide Prelude.True
%hide Prelude.False
%hide Prelude.pow
-- %hide Int

%default total


data Desc : Type where
  Zero  : Desc
  One   : Desc
  Plus  : Desc -> Desc -> Desc
  Times : Desc -> Desc -> Desc

ToType : Desc -> Type
ToType Zero = Void
ToType One = Unit
ToType (Plus x y) = Either (ToType x) (ToType y)
ToType (Times x y) = Pair (ToType x) (ToType y)

BoolDesc : Desc
BoolDesc = One `Plus` One

BoolDesc1 : Desc
BoolDesc1 = One `Plus` (One `Plus` Zero)

BoolDesc2 : Desc
BoolDesc2 = Zero `Plus` (One `Plus` One)

iso1 : ToType BoolDesc `Iso` ToType BoolDesc1
iso1 = MkIso
  (\case (Left x) => Left x
         (Right x) => Right ())
  (bimap id Left)
  (\case (Left x) => Refl
         (Right (Left ())) => Refl
         (Right (Right x)) => absurd x)
  (\case (Left x) => Refl
         (Right ()) => Refl)

iso2 : ToType BoolDesc `Iso` ToType BoolDesc2
iso2 = MkIso
  (\case (Left x) => absurd x
         (Right x) => x)
  (\x => Right x)
  (\case (Left x) => void x
         (Right x) => Refl)
  (\x => Refl)

iso3 : ToType BoolDesc1 `Iso` ToType BoolDesc2
iso3 = symmetric iso1 `transitive` iso2

Bool : Type
Bool = ToType BoolDesc

True : Bool
True = Left ()

False : Bool
False = Right ()

not : Bool -> Bool
not (Left x) = Right x
not (Right x) = Left x

namespace Variables
  data Desc2 : Type where
    Var : String -> Desc2
    Zero  : Desc2
    One   : Desc2
    Plus  : Desc2 -> Desc2 -> Desc2
    Times : Desc2 -> Desc2 -> Desc2

  ToType : List (String, Desc2) -> Desc2 -> Maybe Type
  ToType context (Var str) = assert_total (Variables.ToType context =<< lookup str context)
  ToType context Zero = Just Void
  ToType context One = Just Unit
  ToType context (Plus x y) = Either <$> ToType context x <*> ToType context y
  ToType context (Times x y) = Pair <$> ToType context x <*> ToType context y

  EitherDesc : Desc2
  EitherDesc = (Var "a") `Plus` (Var "b")

  BoolDesc : Desc2
  BoolDesc = Plus One One

  failing
    Bool : Type
    Bool = ToType [] BoolDesc

namespace Scoped
  data CFT : Nat -> Type where
    Var : Fin n -> CFT n
    Zero : CFT n
    One  : CFT n
    Plus : CFT n -> CFT n -> CFT n
    Times : CFT n -> CFT n -> CFT n
    Mu : CFT (S n) -> CFT n
    Apply : CFT (S n) -> CFT n -> CFT n

  pow : CFT n -> Nat -> CFT n
  pow n Z = One
  pow n (S Z) = n
  pow n (S m) = n `Times` (n `pow` m)

  Ren : Nat -> Nat -> Type
  Ren n m = Fin n -> Fin m

  ext : Ren n m -> Ren (S n) (S m)
  ext s  FZ    = FZ
  ext s (FS x) = FS (s x)

  rename : Ren a b -> CFT a -> CFT b
  rename f (Var v) = Var (f v)
  rename f Zero = Zero
  rename f One = One
  rename f (Plus y z) = rename f y `Plus` rename f z
  rename f (Times y z) = rename f y `Times` rename f z
  rename f (Mu y) = Mu (rename (ext f) y)
  rename f (Apply y z) = Apply (rename (ext f) y) (rename f z)

  weaken : CFT a -> CFT (S a)
  weaken = rename FS

  substitute : CFT (S n) -> CFT n -> CFT n
  substitute (Var FZ) y = y
  substitute (Var (FS x)) y = Var x
  substitute Zero y = Zero
  substitute One y = One
  substitute (Plus x z) y = Plus (substitute x y) (substitute z y)
  substitute (Times x z) y = Times (substitute x y) (substitute z y)
  substitute (Mu x) y = Mu (substitute x (weaken y))
  substitute (Apply x z) y = Apply (substitute x (weaken y)) (substitute z y)

  record Fix (f : Type -> Type)  where
    constructor Rec
    unFix : Inf (f (Fix f))

  ToType : CFT n -> Vect n Type  -> Type
  ToType (Var x) xs = index x xs
  ToType Zero xs = Void
  ToType One xs = Unit
  ToType (Plus x y) xs = Either (ToType x xs) (ToType y xs)
  ToType (Times x y) xs = Pair (ToType x xs) (ToType y xs)
  ToType (Apply x y) xs = assert_total $ ToType (substitute x y) xs
  ToType (Mu x) xs = Fix (ToType x . (:: xs))

  EitherDesc : CFT 2
  EitherDesc = Var 0 `Plus` Var 1

  Either : Vect 2 Type -> Type
  Either ctx = ToType EitherDesc ctx

  DLeft : a -> Either [a, b]
  DLeft x = Left x

  DRight : b -> Either [a, b]
  DRight x = Right x

  ListDesc : CFT 1
  ListDesc = Mu (One `Plus` (Var 1 `Times` Var 0))

  DList : Type -> Type
  DList ty = ToType ListDesc [ty]

  DNil : DList a
  DNil = Rec (Left ())

  DCons : a -> DList a -> DList a
  DCons x y = Rec (Right (x, y))

  DEither : Vect 2 Type -> Type
  DEither ctx = ToType EitherDesc ctx

  DLeft' : a -> DEither [a, b]
  DLeft' x = Left x

  DRight' : b -> DEither [a, b]
  DRight' x = Right x

  NatFromList : CFT 0
  NatFromList = ListDesc `Apply` One

  DNat : Type
  DNat = ToType NatFromList []

  DZero : DNat
  DZero = Rec (Left ())

  DSucc : DNat -> DNat
  DSucc n = Rec (Right (n, ()))

  BoolDesc : CFT n
  BoolDesc = One `Plus` One

  Word : CFT n
  Word = BoolDesc `pow` 4

  CharDesc : CFT n
  CharDesc = BoolDesc `pow` 8

  IntDesc : CFT n
  IntDesc = BoolDesc `pow` 32

  -- Left is true, Right is false
  DBool : Type
  DBool = ToType BoolDesc []

  DInt : Type
  DInt = ToType IntDesc []

  index : (i : Fin n) -> {xs : Vect n Type} -> All f xs -> f (Vect.index i xs)
  index FZ (x :: y) = x
  index (FS y) (x :: z) = index y z

  toJSON : (t : CFT n) -> {xs : Vect n Type} -> {auto ser : All (\x => x -> JSON) xs} -> ToType t xs -> JSON
  toJSON (Var n) val = let serialiser = index n ser in serialiser val
  toJSON Zero _ impossible
  toJSON One _ = JObject []
  toJSON (Plus y z) (Left x) = JObject [("left", toJSON y x {xs} {ser} )]
  toJSON (Plus y z) (Right x) = JObject [("right", toJSON z x {xs} {ser} )]
  toJSON (Times y z) (x, w) = JObject [("_1", toJSON y x {xs} {ser}), ("_2", toJSON z w {xs} {ser})]
  toJSON (Mu y) (Rec rec) =
    assert_total $ toJSON {xs = _ :: xs} {ser = (\z => toJSON {ser} (Mu y) z) :: ser} y rec
  toJSON (Apply y z) x = toJSON {ser} (substitute y z) x

  natToJSON : Nat -> JSON
  natToJSON = cast {from = Double} . cast

  jsonToNat : JSON -> Maybe Nat
  jsonToNat json = ?www

  testList : DList Nat
  testList = DCons 3 (DCons 2 DNil)

  listToJSON : JSON
  listToJSON = toJSON ListDesc testList {xs = [Nat]} {ser = [natToJSON]}

  twoToJSON : JSON
  twoToJSON = toJSON NatFromList {xs = []} (DSucc (DSucc DZero))

  fromJSON : (t : CFT n) -> {xs : Vect n Type} -> {auto deSer : All (\x => JSON -> Maybe x) xs} -> JSON -> Maybe (ToType t xs)
  fromJSON (Var x) json = let deserialiser = index x deSer in deserialiser json
  fromJSON Zero json = Nothing
  fromJSON One (JObject []) = Just ()
  fromJSON One _ = Nothing
  fromJSON (Plus x y) (JObject [("left", z)]) = Left <$> fromJSON {deSer} x z
  fromJSON (Plus x y) (JObject [("right", z)]) = Right <$> fromJSON {deSer} y z
  fromJSON (Plus x y) _ = Nothing
  fromJSON (Times x y) (JObject [("_1", l), ("_2", r)]) = MkPair <$> fromJSON {deSer} x l <*> fromJSON {deSer} y r
  fromJSON (Times x y) _ = Nothing
  fromJSON (Mu x) json =
    case fromJSON {xs = _ :: xs} {deSer = fromJSON {deSer} (Mu x) :: deSer } x json of
         Just w => Just $ Rec w
         Nothing => Nothing
  fromJSON (Apply x y) json = assert_total $ fromJSON {deSer} (substitute x y) json

  deserialiseNat : Maybe DNat
  deserialiseNat = fromJSON NatFromList {xs = []} twoToJSON


