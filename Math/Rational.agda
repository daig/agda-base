{-# OPTIONS --cubical #-}
module Math.Rational where
open import Eq 
open import Sigma
open import Math.Category
open import Cubical.Core

open import Int
open import Empty
-- open import Cubical.HLevel
open import Struct.Quotient

Q : Type
Q = Σ ℤ \ x → Σ ℤ \ y → ¬ (y ≡ pos 0)
_ℚ~_ : Q → Q → Type
(a , b , _) ℚ~ (x , y , _) = (a * y) ≡ (b * x)
ℚ : Type
ℚ = Q / _ℚ~_

-- swap-middle = λ (a x y b : ℤ) →
--     a * x *(y * b) ≡⟨ sym (*assoc (a * x) y b)    ⟩
--     a * x * y * b  ≡[ i ]⟨ *assoc a x y i * b ⟩
--     a *(x * y)* b  ≡[ i ]⟨ a * *comm x y i * b    ⟩
--     a *(y * x)* b  ≡[ i ]⟨ *assoc a y x (~ i) * b     ⟩
--     a * y * x * b  ≡⟨ *assoc (a * y) x b    ⟩
--     a * y *(x * b) ∎

-- -- module Int where
--   𝕫 = ℕ × ℕ
--   _𝕫∼_ : 𝕫 → 𝕫 → Type
--   (a⁺ , a⁻) 𝕫∼ (b⁺ , b⁻) = a⁺ + b⁻ ≡ b⁺ + a⁻
--   ℤ = 𝕫 / _𝕫∼_

--   _++_ : 𝕫 → 𝕫 → 𝕫
--   (a⁺ , a⁻) ++ (b⁺ , b⁻) = a⁺ + b⁺ , a⁻ + b⁻
--   ++∼ : (a b c d : 𝕫) → a 𝕫∼ b → c 𝕫∼ d → (a ++ c) 𝕫∼ (b ++ d)
--   ++∼ (a⁺ , a⁻) (b⁺ , b⁻) (c⁺ , c⁻) (d⁺ , d⁻) a∼b c∼d =
--     a⁺ + c⁺ + (b⁻ + d⁻) ≡⟨ swap-middle a⁺ c⁺ b⁻ d⁻ ⟩
--     a⁺ + b⁻ + (c⁺ + d⁻) ≡[ i ]⟨ a∼b i + c∼d i    ⟩
--     b⁺ + a⁻ + (d⁺ + c⁻) ≡⟨ swap-middle b⁺ a⁻ d⁺ c⁻ ⟩
--     b⁺ + d⁺ + (a⁻ + c⁻) ∎
--   _⊕_ : ℤ → ℤ → ℤ
--   _⊕_ = Quotient.rec2 set/
--     (λ x y → ⟦ x ++ y ⟧) -- ← actual implementation
--     (λ x₀ x₁ y x₀≡x₁ → ≡/ _ _ (++∼ x₀ x₁ y  y  x₀≡x₁ ✓))
--     (λ x y₀ y₁ y₀≡y₁ → ≡/ _ _ (++∼ x  x  y₀ y₁ ✓ y₀≡y₁))
