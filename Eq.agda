{-# OPTIONS --without-K #-}
module Eq where
open import Type

open import Agda.Builtin.Equality public

-- module TrustMe where
--     primitive primEraseEquality         : ∀ {ℓ} {A : Type ℓ} {x y : A} → x ≡ y → x ≡ y
--     private postulate unsafePrimTrustMe : ∀ {ℓ} {A : Type ℓ} {x y : A} → x ≡ y
--     primTrustMe                         : ∀ {ℓ} {A : Type ℓ} {x y : A} → x ≡ y
--     primTrustMe = primEraseEquality unsafePrimTrustMe
--     {-# DISPLAY primEraseEquality unsafePrimTrustMe = primTrustMe #-}

private
  variable
    ℓ ℓa ℓb ℓc : Level
    A : Type ℓa
    B : Type ℓb
    w x y z : A

-- infix 4 _≡_
-- data _≡_ {A : Type ℓ} (x : A) : A → Type ℓ where
--   instance refl : x ≡ x
-- {-# BUILTIN EQUALITY _≡_ #-}
pattern ✓ = refl

cong : ∀ (f : A → B) {x y} → x ≡ y → f x ≡ f y
cong f refl = refl

infix 5 _⟨&⟩_
_⟨&⟩_ : ∀ {x y} (e : x ≡ y) (f : A → B) → f x ≡ f y
e ⟨&⟩ f = cong f e

sym : x ≡ y → y ≡ x
sym refl = refl

subst : ∀ {x y} (P : A → Type ℓ) → x ≡ y → P x → P y
subst P ✓ px = px

subst′ : ∀ {x : Type ℓ} {y : Type ℓ} → x ≡ y → x → y
subst′ ✓ x = x

infixr 30 _∙_
_∙_ : x ≡ y → y ≡ z → x ≡ z
refl ∙ e = e

postulate funExt : {A : Type ℓa} {B : A → Type ℓb} {f g : (x : A) → B x}
                → (∀ x → f x ≡ g x) → f ≡ g
unfunExt : {A : Type ℓa} {B : A → Type ℓb} {f g : (x : A) → B x}
                → f ≡ g → (∀ x → f x ≡ g x)
unfunExt refl x = refl

un∀ : {A : Type ℓa} {B : Type ℓb} {f g : A → B} → (λ x → f x) ≡ (λ  x → g x) → A → f ≡ g
un∀ refl x = refl

uneta : {A : Type ℓa} {B : A → Type ℓb} (f : (x : A) → B x) → f ≡ (λ x → f x)
uneta f = refl

module Reasoning where

  infix  3 _∎
  infixr 2 _≡⟨⟩_ step-≡ step-≡˘
  infix  1 begin_

  begin_ : ∀{x y : A} → x ≡ y → x ≡ y
  begin_ x≡y = x≡y

  _≡⟨⟩_ : ∀ (x {y} : A) → x ≡ y → x ≡ y
  _ ≡⟨⟩ x≡y = x≡y

  step-≡ : ∀ (x {y z} : A) → y ≡ z → x ≡ y → x ≡ z
  step-≡ _ y≡z x≡y = x≡y ∙ y≡z

  step-≡˘ : ∀ (x {y z} : A) → y ≡ z → y ≡ x → x ≡ z
  step-≡˘ _ y≡z y≡x = sym y≡x ∙ y≡z

  _∎ : ∀ (x : A) → x ≡ x
  _∎ _ = refl

  syntax step-≡  x y≡z x≡y = x ≡⟨  x≡y ⟩ y≡z
  syntax step-≡˘ x y≡z y≡x = x ≡˘⟨ y≡x ⟩ y≡z
open Reasoning public
