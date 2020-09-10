module Fin where
open import Nat
open import Type
open import Eq

data Fin : (n : ℕ) → Type where
  fz : ∀ {n} → Fin (s n)
  fs : ∀ {n} → Fin n → Fin (s n)

private
  cata : ∀ {n} → Fin n → ℕ
  cata fz =  s z
  cata (fs f) =  s (cata f)
  -- cata≡ : ∀ {n} → (f : Fin n) → cata f ≤ n
  -- cata≡ {.(s _)} fz = {!!}
  -- cata≡ {.(s _)} (fs f) = {!!}
