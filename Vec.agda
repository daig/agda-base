{-# OPTIONS --without-K #-}
module Vec where
open import Nat public
open import Type
open Vars
open import Maybe
open import Bool
open import Sigma
open import Eq
open import Fun
open import Empty
open import Unit
open import Decidable

infixr 5 _:::_
data [[_]][_] {ℓ} (A : Set ℓ) : ℕ → Set ℓ where
  [[]] : [[ A ]][ z ]
  _:::_ : {n : ℕ} (x : A) (xs : [[ A ]][ n ]) → [[ A ]][ s n ]

len : ∀ {n} →  [[ A ]][ n ] → ℕ
len { n = n } _ = n

_?→_ : Type ℓa → Type ℓb → Type (ℓa ⊔ ℓb)
A ?→ B = (A → 𝔹) ⋊ \ p → (a : A) (e : p a ≡ true) → B
partial : A ?→ B → A → ?? B
partial (p , f ) a with decide p a
... | .true  because ofʸ  p₁ = ?! (f a p₁)
... | .false because ofⁿ ¬p  = ?∅

private -- example
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
