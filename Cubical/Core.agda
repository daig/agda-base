{-# OPTIONS --cubical --safe #-}
module Cubical.Core where
open import Type public
open import Agda.Builtin.Cubical.Path public renaming (PathP to infix 4 _[_≡_])
open import Agda.Builtin.Cubical.Sub public renaming
    ( Sub to infix 4 _[_↦_] ; inc to ↦_ ; primSubOut to _↦) 
open import Agda.Primitive.Cubical public renaming
    (primIMin to infixr 20 _∧_ ;primIMax to infixr 20 _∨_ ;primINeg to infixr 30  ~_
    ;isOneEmpty to empty ; IsOne to _=i1 ;itIsOne to 1=1
    ;primComp to comp ;primTransp to transp ;primHComp to hcomp 
    ;Partial to [_⊢_] ; PartialP to [_⊩_])
variable
    ℓ′ : I → Level
    φ ψ : I
    ⊢A : I → Type ℓa
    ⊢′A : (i : I) → Type (ℓ′ i)
    ⊢B : I → Type ℓb
    ⊢′B : (i : I) → Type (ℓ′ i)
    ⊢B′ : A → I → Type ℓb
    ⊢′B′ : A → (i : I) → Type (ℓ′ i)

-- Homogeneous filling
hfill : {φ : I} (u : I → [ φ ⊢ A ]) (u0 : A [ φ ↦ u i0 ])
  → u0 ↦ ≡ hcomp u (u0 ↦)
hfill {φ = φ} u u0 i =
  hcomp (λ j → λ { (φ = i1) → u (i ∧ j) 1=1
                 ; (i = i0) → u0 ↦ })
        (u0 ↦)

-- Heterogeneous filling defined using comp
fill : (A : ∀ i → Type (ℓ′ i))
       (u : ∀ i → [ φ ⊢ A i ])
       (u0 : A i0 [ φ ↦ u i0 ])
       (i : I) → A i
fill {φ = φ} A u u0 i = comp (λ j → A (i ∧ j))
                             (λ j → λ { (φ = i1) → u (i ∧ j) 1=1
                                      ; (i = i0) → u0 ↦})
                             (u0 ↦)
