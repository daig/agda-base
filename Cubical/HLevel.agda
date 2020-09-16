{-# OPTIONS --cubical #-}
module Cubical.HLevel where
open import Type
open import Cubical.Core
open import Nat

private variable ℓ ℓa ℓb : Level


-- Homotopy level
h? : ℕ → Type ℓ → Type ℓ
h? 0 A = ∃ \ (x : A) → ∀ y → x ≡ y
h? 1 A = (x y : A) → x ≡ y
h? (s (s n)) A = (x y : A) → h? (s n) (x ≡ y)

contractible? proposition? set? : Type ℓ → Type ℓ
contractible? = h? 0
proposition?  = h? 1
set?          = h? 2
