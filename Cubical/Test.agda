{-# OPTIONS --cubical --prop --no-import-sorts #-}
module Cubical.Test where
open import Type
open import Agda.Builtin.Sigma public
open import Agda.Builtin.Cubical.Path

private
  variable
    ℓ ℓa  ℓb ℓc : Level
    A : Type ℓa
    B : Type ℓb


contractible : Type ℓ → Type ℓ
contractible A = Σ A \ x → (∀ y → x ≡ y)

module _ {A : Type ℓa} {B : Type ℓb} where

    fiber : (f : A → B) (y : B) → Type (ℓa ⊔ ℓb)
    fiber f y = Σ A \ x → f x ≡ y

    record equiv? (f : A → B) : Type (ℓa ⊔ ℓb) where
        field
          proof : (y : B) → contractible (fiber f y)
    --            : (y : B) → Σ (Σ A \ x → f x ≡ y) \ x↦y → (∀ x′↦y → x↦y ≡ x′↦y)

_≅_ : (A : Type ℓa) (B : Type ℓb) → Type (ℓa ⊔ ℓb)
A ≅ B = Σ (A → B) \ f → equiv? f
-- {-# BUILTIN EQUIV      _≅_        #-}

module Equiv where
  to : {A : Type ℓa} {B : Type ℓb} → A ≅ B → A → B
  to = fst
  -- Improved version of equivProof compared to Lemma 5 in CCHM. We put
  -- the (φ = i0) face in contr' making it be definitionally c in this
  -- case. This makes the computational behavior better, in particular
  -- for transp in Glue.
  equivProof : ∀ {la lt} (T : Type la) (A : Type lt) → (w : T ≅ A) → (a : A)
          → ∀ ψ → ([ ψ ↦ fiber (w .fst) a ] ) → fiber (w .fst) a
  equivProof A B w a ψ fb = contr' {A = fiber (w .fst) a} (w .snd .equiv-proof a) ψ fb
    where
      contr' : ∀ {ℓ} {A : Type ℓ} → isContr A → (φ : I) → (u : [ φ ↦ A ]) → A
      contr' {A = A} (c , p) φ u = hcomp (λ i → λ { (φ = i1) → p (u 1=1) i
                                                    ; (φ = i0) → c }) c
