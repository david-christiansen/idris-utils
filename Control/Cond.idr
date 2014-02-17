module Cond

%default total
%access abstract

{-
Usage example:

foo : Int -> String
foo x = cond $ do
  x == 5 ?: "five"
  x == 17 ?: "bigger"
  otherwise "fnord"

• An otherwise at the end is required.
• Note that (?:) is a low-precedence operator and will act as such: parentheses
  may be required in some cases. Note also that otherwise is a function, so ($)
  or parentheses are required for non-simple default expressions.
• The expression for a non-matched clause is not evaluated, so this construct
  can be used to check preconditions on partial functions (but please encode
  these in types instead to make the functions total, if feasible).
-}

infix 0 ?:

data Alt a = Unmatched | Matched a

data Res a = It a

(>>=) : Alt a -> (() -> Res a) -> Res a
(>>=) Unmatched f = f ()
(>>=) (Matched x) f = It x

(?:) : Bool -> |(expr : a) -> Alt a
(?:) False x = Unmatched
(?:) True x = Matched x

otherwise : a -> Res a
otherwise x = It x

cond : Res a -> a
cond (It x) = x

