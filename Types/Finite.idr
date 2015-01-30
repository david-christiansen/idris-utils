module Types.Finite

import Data.Fin
import Control.Isomorphism


%default total

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
          to () = FZ
          from : Fin 1 -> ()
          from FZ     = ()
          from (FS f) = absurd f
          ok2 : (x : ()) -> from (to x) = x
          ok2 () = Refl
          ok1 : (x : Fin 1) -> to (from x) = x
          ok1 FZ     = Refl
          ok1 (FS f) = absurd f

instance Finite Bool 2 where
  isFinite = MkIso to from ok1 ok2
    where to : Bool -> Fin 2
          to False = 0
          to True  = 1
          from : Fin 2 -> Bool
          from FZ = False
          from (FS FZ) = True
          from (FS (FS x)) = absurd x 
          ok1 : (f : Fin 2) -> to (from f) = f
          ok1 FZ = Refl
          ok1 (FS FZ) = Refl
          ok1 (FS (FS x)) = absurd x 
          ok2 : (b : Bool) -> from (to b) = b
          ok2 False = Refl
          ok2 True = Refl

-- Isomorphisms over Maybe
maybeVoidUnit2 : Iso (Maybe Void) ()
maybeVoidUnit2 = MkIso to from iso1 iso2
  where to : Maybe Void -> ()
        to Nothing = ()
        to (Just x) = absurd x
        from : () -> Maybe Void
        from () = Nothing
        iso1 : (x : ()) -> to (from x) = x
        iso1 () = Refl
        iso2 : (y : Maybe Void) -> from (to y) = y
        iso2 Nothing = Refl
        iso2 (Just x) = absurd x

