{-# OPTIONS --without-K #-}
module Fun.Partial where
open import Type
open Vars
open import Bool
open import Sigma
open import Eq
open import Maybe
open import Decidable

true? : (A → 𝔹) → A → Type
true? p a =  p a ≡ true

_?→_ : Type ℓa → Type ℓb → Type (ℓa ⊔ ℓb)
A ?→ B = (A → 𝔹) ⋊ \ p → (a : A) (e : p a ≡ true) → B
partial : A ?→ B → A → ?? B
partial (p , f ) a with decide p a
... | .true  because ofʸ  p₁ = ?! (f a p₁)
... | .false because ofⁿ ¬p  = ?∅

private -- example
    open import Nat
    ex : ℕ ?→ ℕ
    π₁ ex 0 = true
    π₁ ex 1 = true
    π₁ ex 2 = true
    π₁ ex _ = false
    π₂ ex 0 e = 2
    π₂ ex 1 e = 1
    π₂ ex 2 e = 0

    check : partial ex 3  ≡ ?∅
    check = refl
