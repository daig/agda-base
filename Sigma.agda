{-# OPTIONS --cubical --safe --no-sized-types --no-guardedness --no-subtyping #-}
module Sigma where
open import Agda.Builtin.Sigma public renaming (fst to π₁; snd to π₂)
open import Type
open import Empty
open import Cubical.Core

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

∃ ∄ : (B′ : A → Type ℓb) → Type _
∃ {A = A} B′ = A ⋊ B′
∄ P = ¬ ∃ P

_×_ : (A : Type ℓa) (B : Type ℓb) → Type (ℓa ⊔ ℓb)
A × B = A ⋊ λ _ → B

∃! : {A : Type ℓa} (B : A → Type ℓb) → Type (ℓa ⊔ ℓb)
∃! B = ∃ \ a → B a × ∀ {x} → B x → a ≡ x 
∃₂ : {A : Type ℓa} {B : A → Type ℓb} (C : (x : A) → B x → Type ℓc) → Type _
∃₂ C = ∃ \ a → ∃ \ b → C a b

module Sigma where
    swap : A × B → B × A
    swap (x , y) = (y , x)
