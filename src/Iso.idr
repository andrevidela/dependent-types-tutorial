module Iso

import Control.Relation

public export
record Iso (t1, t2 : Type) where
  constructor MkIso
  from : t2 -> t1
  to : t1 -> t2
  toFrom : (x : t2) -> to (from x) = x
  fromTo : (x : t1) -> (from (to x)) = x

export
Reflexive Type Iso where
  reflexive = MkIso id id (\_ => Refl) (\_ => Refl)

export
Transitive Type Iso where
  transitive i1 i2 = MkIso
    (i1.from . i2.from)
    (i2.to . i1.to)
    (\x => rewrite i1.toFrom (i2.from x) in i2.toFrom x)
    (\x => rewrite i2.fromTo (i1.to x) in i1.fromTo x)

export
Symmetric Type Iso where
  symmetric i = MkIso i.to i.from i.fromTo i.toFrom
