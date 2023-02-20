module Exercises.File3

import Data.List
import Data.Nat
import Data.Fin
import Data.Vect
import Data.Vect.Elem
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

namespace Context
  data Func : Type where
    Var   : Func
    Zero  : Func
    One   : Func
    Plus  : Func -> Func -> Func
    Times : Func -> Func -> Func

  ToType : Func -> Type -> Type
  ToType Var ty = ty
  ToType Zero ty = Void
  ToType One ty = Unit
  ToType (Plus x y) ty = Either (ToType x ty) (ToType y ty)
  ToType (Times x y) ty = Pair (ToType x ty) (ToType y ty)

  IsFunctor : (a -> b) -> (ctx : Func) -> ToType ctx a -> ToType ctx b
  IsFunctor f Var x = f x
  IsFunctor f Zero x = void x
  IsFunctor f One x = x
  IsFunctor f (Plus y z) x = bimap (IsFunctor f y) (IsFunctor f z) x
  IsFunctor f (Times y z) x = bimap (IsFunctor f y) (IsFunctor f z) x

infix 2 =>>


record Fix (f : Type -> Type)  where
  constructor Rec
  unFix : Lazy (f (Fix f))

record Fix2 (f : Type -> Type -> Type) (a : Type) where
  constructor Rec2
  unFix : Lazy (f a (Fix2 f a))

namespace Scoped
  data CFT : Nat -> Type where
    Var : Fin n -> CFT n
    Mu : CFT (S n) -> CFT n
    One : CFT n
    Zero : CFT n
    Plus : CFT n -> CFT n -> CFT n
    Times : CFT n -> CFT n -> CFT n
    Let : (expr : CFT n) -> (body : CFT (S n)) ->  CFT n

  ToType : CFT n -> Vect n Type  -> Type
  ToType (Var x) xs = index x xs
  ToType One xs = Unit
  ToType Zero xs = Void
  ToType (Mu x) xs = Fix (ToType x . (:: xs))
  ToType (Plus x y) xs = Either (ToType x xs) (ToType y xs)
  ToType (Times x y) xs = Pair (ToType x xs) (ToType y xs)
  ToType (Let var body) xs =
    let arg = ToType var xs -- first we compute the argument
    in ToType body (arg :: xs) -- then we extend the context and compute x

  MaybeDesc : CFT 1
  MaybeDesc = Plus One (Var 0)

  Identity : CFT 1
  Identity = Var 0

  failing
    fail : CFT 1
    fail = Apply Identity MaybeDesc

  ListDesc : CFT (S n)
  ListDesc = Mu (Plus One (Times (Var 1) (Var 0)))

  ListEither : Type -> Type -> Type
  ListEither a b = List (Either a b)

  EitherDesc : CFT 2
  EitherDesc = Plus (Var 0) (Var 1)

  ListEitherDesc : CFT 2
  ListEitherDesc = Let EitherDesc ListDesc

  -- not illegal anymore, we're just bringing a `Zero` into scope
  Illegal : CFT 0
  Illegal = Let Zero One

  IllegalType : Type
  IllegalType = ToType Illegal []

  IllegalValue : IllegalType
  IllegalValue = ()

  ListType : Type -> Type
  ListType x = ToType ListDesc [x]

  ListNil : ListType a
  ListNil = Rec (Left ())

  ListCons : a -> ListType a -> ListType a
  ListCons x xs = Rec (Right (MkPair x xs))

  NatDesc : CFT 0
  NatDesc = Let One ListDesc

  NatType : Type
  NatType = ToType NatDesc []

  NatZero : NatType
  NatZero = ListNil

  NatSucc : NatType -> NatType
  NatSucc = ListCons ()

  ListNatType : Type
  ListNatType = ToType (Let NatDesc ListDesc) []

  ZeroOneTwo : ListNatType
  ZeroOneTwo = ListCons NatZero
             $ ListCons (NatSucc NatZero)
             $ ListCons (NatSucc $ NatSucc NatZero)
             $ ListNil

  GenericRose : (Type -> Type) -> Type -> Type
  GenericRose f = Fix2 (\a, b => f (a, b))

  Rose : Type -> Type
  Rose = GenericRose List

  RoseNil : Rose a
  RoseNil = Rec2 []

  RoseNest : List (a, Rose a) -> Rose a
  RoseNest x = Rec2 x

  ListGen : Type -> Type
  ListGen = GenericRose Maybe

  GenNil : ListGen a
  GenNil = Rec2 Nothing

  GenCons : a -> ListGen a -> ListGen a
  GenCons x y = Rec2 (Just (x, y))

  NatGen : Type
  NatGen = ListGen Unit

  ZeroGen : NatGen
  ZeroGen = GenNil

  SuccGen : NatGen -> NatGen
  SuccGen = GenCons ()

  GenericRoseDesc : CFT 2
  GenericRoseDesc = Mu $ Let (Let (Var 1) (Var 0)) ListDesc

  RoseDesc : CFT 1
  RoseDesc = Let ListDesc GenericRoseDesc

  RoseTree : Type -> Type
  RoseTree x = ToType RoseDesc [x]

  RoseNil' : RoseTree a
  RoseNil' = Rec ListNil

  RoseAdd : a -> RoseTree a -> RoseTree a
  RoseAdd x (Rec xs) = Rec (ListCons (Rec (Right (x, Rec (Left ())))) xs )


{-
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
  DSucc n = ?notsure

  BoolDesc : CFT n
  BoolDesc = One `Plus` One

  Word : CFT n
  Word = BoolDesc `pow` 4

  CharDesc : CFT n
  CharDesc = BoolDesc `pow` 8

  IntDesc : CFT n
  IntDesc = BoolDesc `pow` 32

  ListNat : CFT 0
  ListNat = ListDesc `Apply` NatFromList

  ListNatTy : Type
  ListNatTy = ToType ListNat []

  ZeroWrong : ListNatTy
  ZeroWrong = Rec (Delay (Left ()))

  SuccWrong : ListNatTy -> ListNatTy
  SuccWrong n = Rec (Delay (Right (Rec (Delay (Left ())), n)))

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
  toJSON (Apply y z) x = toJSON {ser} ?ww (?wwaa x) --toJSON {ser} (substitute y z) x

  {-
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



