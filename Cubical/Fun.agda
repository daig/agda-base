{-# OPTIONS --cubical --prop --no-import-sorts #-}
module Cubical.Fun where
open import Cubical.Core
open import Eq

private
  variable
    ℓ ℓa ℓb ℓc : Level
    A : Type ℓa
    B : Type ℓb

_∘_ : {A : Type ℓa} {B : {x : A} → Type ℓb} {C : {x : A} {y : B {x}} → Type ℓc}
      (g : {x : A} (y : B {x = x}) → C {x} {y})
      (f : (x : A) → B {x = x})
  →  (x : A) → C {x = x} {y = f x}
(g ∘ f) x = g (f x)

∘assoc : {A : Type ℓa} {B : {x : A} → Type ℓb}
         {C : {x : A} {y : B {x}} → Type ℓc}
         {D : {x : A} {y : B {x}} {z : C {x} {y}} → Type ℓc}
         (h : {x : A} {y : B {x = x}} (z : C {x = x} {y = y}) → D {x} {y} {z})
         (g : {x : A} (y : B {x = x}) → C {x} {y})
         (f : (x : A) → B {x = x})
         → h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f
∘assoc h g f = refl
