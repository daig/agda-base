{-# OPTIONS --without-K #-}
module Iso where
open import Type
open import Eq hiding (sym)
open Eq.Reasoning

private
  variable
    ℓa ℓb ℓc : Level
    A : Type ℓa
    B : Type ℓb
    C : Type ℓc


record _≃_ (A : Type ℓa) (B : Type ℓb) : Type (ℓa ⊔ ℓb) where
  field
      to : A → B
      from : B → A
      to∘from≡id : ∀ x → to (from x) ≡ x
      from∘to≡id : ∀ x → from (to x) ≡ x
open _≃_ public

id : A ≃ A
to id x = x
from id x = x
to∘from≡id id x = refl
from∘to≡id id x = refl

module ComposeIso (F : A ≃ B) (G : B ≃ C) where
    open _≃_ F renaming (to to f; from to f⁻¹)
    open _≃_ G renaming (to to g; from to g⁻¹)

    _▸_ : A ≃ C
    to _▸_ x = g (f x)
    from _▸_ x = f⁻¹ (g⁻¹ x)
    to∘from≡id _▸_ x
                                        = g (f (f⁻¹ (g⁻¹ x)))
        ≡⟨ cong g (to∘from≡id F (g⁻¹ x)) ⟩    g (g⁻¹ x)
        ≡⟨  to∘from≡id G x               ⟩       x ∎
    from∘to≡id _▸_ x
                                        =  f⁻¹ (g⁻¹ (g (f x)))
        ≡⟨ cong f⁻¹ (from∘to≡id G (f x)) ⟩     f⁻¹ (f x)
        ≡⟨ from∘to≡id F x                ⟩      x ∎
open ComposeIso public

sym : A ≃ B → B ≃ A
to (sym F) = from F
from (sym F) = to F
to∘from≡id (sym F) = from∘to≡id F
from∘to≡id (sym F) = to∘from≡id F
