{-# OPTIONS --without-K #-}
module Decidable where
open import Type
open Vars
open import Bool
open import Empty
open import Sigma
open import Eq


data Decide (P : Type ℓ) : 𝔹 → Type ℓ where
  ofʸ : (p : P) → Decide P true
  ofⁿ : (¬p : ¬ P) → Decide P false 

record Dec (P : Type ℓ) : Type ℓ where
  constructor _because_
  field
    does : 𝔹
    proof : Decide P does

pattern yes p = true because ofʸ p
pattern no ¬p = false because ofⁿ ¬p

decide : (p : A → 𝔹) (a : A) → Dec (p a ≡ true)
decide p a with p a
... | false = no (λ ())
... | true = yes refl


-- record Dec (P : Type ℓ) : Type ℓ where
--   constructor _because_
--   field
--     does : 𝔹
--     proof : Decide P does

