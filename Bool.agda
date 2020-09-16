{-# OPTIONS --cubical --safe #-}
module Bool where
open import Cubical.Eq

data 𝔹 : Set where false true : 𝔹

{-# BUILTIN BOOL  𝔹  #-}
{-# BUILTIN FALSE false #-}
{-# BUILTIN TRUE  true  #-}

_∧_ _∨_ _⊕_ : 𝔹 → 𝔹 → 𝔹
false ∧ _ = false
true ∧ b = b
false ∨ b = b
true ∨ b = true
not : 𝔹 → 𝔹
not false = true
not true = false
true ⊕ b = not b
false ⊕ b = b

infixr 6 _∧_
infixr 5 _∨_ _⊕_

module IO where
  pattern O = false
  pattern I = true
open IO

-- module LE where
--     _≤_ : 𝔹 → 𝔹 → 𝔹
--     O ≤ _ = I
--     I ≤ b = b
--     ≤I : ∀ x → (x ≤ I) ≡ I
--     ≤I = λ { O → ✓ ; I → ✓ }
--     ≤∧I : ∀ x → ((I ∧ x) ≤ x) ≡ I
--     ≤∧I = λ { O → ✓ ; I → ✓}
--     ≤∨ : ∀ {a b x y} → (a ≤ x ≡ I) → (b ≤ y ≡ I) → ((a ∨ b) ≤ (x ∨ y)) ≡ I
--     ≤∨ {I} {x = I} _ _ = ✓
--     ≤∨ {O} {O} _ _ = ✓
--     ≤∨ {O} {I} {O} {I} _ _ = ✓
--     ≤∨ {O} {I} {I} _ _ = ✓
--     ≤Σ₁ : ∀ {a b} → a ≡ I → (a ∨ b ≡ I)
--     ≤Σ₁ {I} _ = ✓
--     ≤Σ₂ : ∀ {a b} → a ≡ I → (a ∨ b ≡ I)
--     ≤Σ₂ {I} {O} _ = ✓
--     ≤Σ₂ {I} {I} _ = ✓

--     ≤∧ : ∀ a b {x y} → (a ≤ x ≡ I) → (b ≤ y ≡ I) → ((a ∧ b) ≤ (x ∧ y)) ≡ I
--     ≤∧ O _ _ _ = ✓
--     ≤∧ I O _ _ = ✓
--     ≤∧ I I {I} {I} _ _ = ✓
--     ∧I : ∀ {a b} → a ≡ I → b ≡ I → a ∧ b ≡ I
--     ∧I {I} {I} _ _ = ✓

--     ≤π₁ : ∀ {a b} → a ∧ b ≡ I → a ≡ I
--     ≤π₁ {I} _ = ✓
--     ≤π₂ : ∀ {a b} → a ∧ b ≡ I → b ≡ I
--     ≤π₂ {I} {I} e = ✓


