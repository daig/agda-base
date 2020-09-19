{-# OPTIONS --cubical --safe #-}
module Iso where
open import Type
open import Eq hiding (sym)
open Eq.Reasoning

record _≅_ (A : Type ℓa) (B : Type ℓb) : Type (ℓa ⊔ ℓb) where
  constructor iso
  field
      to : A → B
      from : B → A
      to∘from : ∀ x → to (from x) ≡ x
      from∘to : ∀ x → from (to x) ≡ x
module Iso where
    open _≅_ public
    id : A ≅ A
    to id x = x
    from id x = x
    to∘from id x = ✓
    from∘to id x = ✓

    module ComposeIso (F : A ≅ B) (G : B ≅ C) where
        open _≅_ F renaming (to to f; from to f⁻¹)
        open _≅_ G renaming (to to g; from to g⁻¹)

        _▸_ : A ≅ C
        to _▸_ x = g (f x)
        from _▸_ x = f⁻¹ (g⁻¹ x)
        to∘from _▸_ x
                                         = g (f (f⁻¹ (g⁻¹ x)))
            ≡⟨ cong g (to∘from F (g⁻¹ x)) ⟩    g (g⁻¹ x)
            ≡⟨  to∘from G x               ⟩       x ∎
        from∘to _▸_ x
                                            =  f⁻¹ (g⁻¹ (g (f x)))
            ≡⟨ cong f⁻¹ (from∘to G (f x)) ⟩     f⁻¹ (f x)
            ≡⟨ from∘to F x                ⟩      x ∎
    open ComposeIso public

    sym : A ≅ B → B ≅ A
    to (sym F) = from F
    from (sym F) = to F
    to∘from (sym F) = from∘to F
    from∘to (sym F) = to∘from F
