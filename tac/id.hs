module Id where

import qualified Prelude

data Nat =
   O
 | S Nat

add :: Nat -> Nat -> Nat
add n m =
  case n of {
   O -> m;
   S p -> S (add p m)}

pplus :: Nat -> Nat -> Nat
pplus n m =
  add n m

