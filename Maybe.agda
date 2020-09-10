{-# OPTIONS --without-K #-}
module Maybe where
open import Type
open Vars

data ?? (A : Type ℓ) : Type ℓ where
  ?! : A → ?? A
  ?∅ : ?? A
