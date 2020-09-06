{-# OPTIONS --without-K #-}
module Empty where

data ⊥ : Set where
absurd : ∀ {ℓ} {X : Set ℓ} → ⊥ → X
absurd ()

infix 3 ¬_

¬_ : ∀ {ℓ} → Set ℓ → Set ℓ
¬ P = P → ⊥
