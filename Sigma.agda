{-# OPTIONS --cubical --safe --no-sized-types --no-guardedness --no-subtyping #-}
module Sigma where
open import Agda.Builtin.Sigma public renaming (fst to π₁; snd to π₂)
open import Type
open import Empty

-- record Σ (A : Type ℓa) (B′ : A → Type ℓb) : Type (ℓa ⊔ ℓb) where
--   constructor _,_
--   field
--     π₁ : A
--     π₂ : B′ π₁
-- open Σ public
-- {-# BUILTIN SIGMA Σ #-}
-- infixr 4 _,_

infixr 2 _×_ _⋊_
_⋊_ = Σ

∃ ∄ : (A → Type ℓb) → Type _
∃ {A = A} B′ = A ⋊ B′
∄ P = ¬ ∃ P

_×_ : (A : Type ℓa) (B : Type ℓb) → Type (ℓa ⊔ ℓb)
A × B = A ⋊ λ _ → B

module Sigma where
    swap : A × B → B × A
    swap (x , y) = (y , x)
