{-# OPTIONS --without-K --safe --no-sized-types --no-guardedness --no-subtyping #-}
module Either where
open import Type
open Vars


infixr 1 _||_
data _||_ (A : Type ℓa) (B : Type ℓb) : Type (ℓa ⊔ ℓb) where
  ˡ : A → A || B
  ʳ : B → A || B
