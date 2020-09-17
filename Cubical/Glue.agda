{-# OPTIONS --cubical --safe #-}
module Cubical.Glue where
open import Cubical.Core
open import Cubical.Equiv
open import Sigma

module Prim where
    primitive
        primGlue    : ∀ {ℓ ℓ'} (A : Type ℓ) {φ : I}
            → (T : [ φ ⊢ Type ℓ' ] )
                (e : [ φ ⊩ (λ i → T i ≃ A) ] )
            → Type ℓ'
        prim^glue   : ∀ {ℓ ℓ'} {A : Type ℓ} {φ : I}
            → {T : [ φ ⊢ Type ℓ' ]}
                {e : [ φ ⊩ (λ o → T o ≃ A) ]}
                (t : [ φ ⊩ T ]) → (a : A)
            → primGlue A T e
        prim^unglue : ∀ {ℓ ℓ'} {A : Type ℓ} {φ : I}
            → {T : [ φ ⊢ Type ℓ' ]}
                {e : [ φ ⊩ (λ o → T o ≃ A) ]}
            → primGlue A T e → A


        -- Needed for transp in Glue.
        primFaceForall : (I → I) → I
    Glue : ∀ {ℓ ℓ'} (A : Type ℓ) {φ} → (Te : [ φ ⊢ (∃ \ T → T ≃ A) ]) → Type ℓ'
    Glue A Te = primGlue A (λ x → Te x .π₁) (λ x → Te x .π₂)
    unglue : ∀ {ℓ ℓ'} {A : Type ℓ}
            (φ : I) {T : [ φ ⊢ Type ℓ' ]}
            {e : [ φ ⊩ (λ o → T o ≃ A) ]} → primGlue A T e → A
    unglue φ {e = e} = prim^unglue {φ = φ}
open Prim public using (Glue ; unglue) renaming (prim^glue to glue)
