module Types.Finite

import Uninhabited
import Control.Isomorphism


%default total

absurd : Uninhabited t => t -> a
absurd t = FalseElim (uninhabited t)

to : Iso a b -> a -> b
to (MkIso to from toFrom fromTo) = to

from : Iso a b -> b -> a
from (MkIso to from toFrom fromTo) = from

class Finite a (n : Nat) where
  total
  isFinite : Iso a (Fin n)

total
toFin : Finite a n => a -> Fin n
toFin = to isFinite


total
fromFin : Finite a n => Fin n -> a
fromFin = from isFinite


instance Finite () 1 where
  isFinite = MkIso to from ok1 ok2
    where to : () -> Fin 1
          to () = fZ
          from : Fin 1 -> ()
          from fZ     = ()
          from (fS f) = absurd f
          ok2 : (x : ()) -> from (to x) = x
          ok2 () = refl
          ok1 : (x : Fin 1) -> to (from x) = x
          ok1 fZ     = refl
          ok1 (fS f) = absurd f

instance Finite Bool 2 where
  isFinite = MkIso to from ok1 ok2
    where to : Bool -> Fin 2
          to False = 0
          to True  = 1
          from : Fin 2 -> Bool
          from fZ = False
          from (fS fZ) = True
          from (fS (fS x)) = FalseElim (uninhabited x)
          ok1 : (f : Fin 2) -> to (from f) = f
          ok1 fZ = refl
          ok1 (fS fZ) = refl
          ok1 (fS (fS x)) = FalseElim (uninhabited x)
          ok2 : (b : Bool) -> from (to b) = b
          ok2 False = refl
          ok2 True = refl


