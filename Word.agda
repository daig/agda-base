{-# OPTIONS --without-K #-}
module Word where
open import Nat

postulate 𝕎 : Set
{-# BUILTIN WORD64 𝕎 #-}

module Prim where
    primitive
        primWord64ToNat : 𝕎 → ℕ
        primWord64FromNat : ℕ → 𝕎
open Prim public renaming
  (primWord64ToNat to toℕ
  ;primWord64FromNat to fromℕ)
