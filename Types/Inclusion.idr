module Types.Inclusion

import Syntax.PreorderReasoning
import Control.Isomorphism

%default total

-- An inclusion from a to b
data Inclusion : (a, b : Type) -> Type where
  Include : (upcast : a -> b) ->
            (downcast : b -> Maybe a) ->
            (upThenDown : (x : a) -> downcast (upcast x) = Just x) ->
            (downThenUp : (y : b) -> maybe () (\x => upcast x = y) (downcast y)) ->
            Inclusion a b

includeRefl : Inclusion a a
includeRefl = Include id Just (\x => Refl) (\y => Refl)


includeTrans : Inclusion a b -> Inclusion b c -> Inclusion a c
includeTrans {a} {b} {c} (Include u d ud du) (Include u' d' ud' du') =
  Include (\x => u' (u x))
          (\y => (d' y) >>= d)
          ok1
          ok2

    where ok1 : (x : a) -> (d' (u' (u x))) >>= d = Just x
          ok1 x = ((d' (u' (u x))) >>= d) ={ cong {f=(>>= d)} (ud' (u x)) }=
                  ((Just (u x)) >>= d)    ={ Refl }=
                  (d (u x))               ={ ud x }=
                  (Just x)                QED

          ok2 : (y : c) -> maybe () (\x => u' (u x) = y) ((d' y) >>= d)
          ok2 y = ok2' (d' y) (du' y) -- Do the first case analysis, but keep the proof
            where ok2' : (z : Maybe b) ->
                         maybe () (\x => u' x = y) z ->
                         maybe () (\x => u' (u x) = y) (z >>= d)
                  ok2' Nothing prf = ()
                  ok2' (Just x) prf = ok2'' (d x) (du x) -- second analysis, keep proof
                    where ok2'' : (z : Maybe a) ->
                                  maybe () (\w => u w = x) z ->
                                  maybe (the Type ()) (\x1 => u' (u x1) = y) z
                          ok2'' Nothing prf2 = ()
                          ok2'' (Just v) prf2 = (u' (u v)) ={ cong prf2 }=
                                                (u' x)     ={ prf       }=
                                                y          QED

-- Enable preorder reasoning syntax over inclusions
qed : (a : Type) -> Inclusion a a
qed a = includeRefl

step : (a : Type) -> Inclusion a b -> Inclusion b c -> Inclusion a c
step a incl1 incl2 = includeTrans incl1 incl2

-- Every isomorphism gives an inclusion mapping
includeIso : Iso a b -> Inclusion a b
includeIso {a} {b} (MkIso to from toFrom fromTo) =
  Include to (\x => Just (from x)) ok1 ok2
    where ok1 : (x : a) -> (Just (from (to x)) = Just x)
          ok1 x = rewrite fromTo x in Refl -- workaround for de Bruijn index bug
          ok2 : (y : b) -> to (from y) = y
          ok2 y = rewrite toFrom y in Refl -- workaround for de Bruijn index bug

castUp : Inclusion a b -> a -> b
castUp (Include up _ _ _) = up

castDown : Inclusion a b -> b -> Maybe a
castDown (Include _ down _ _) = down
