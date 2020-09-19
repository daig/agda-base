{-# OPTIONS --cubical --safe #-}
module Fun where
open import Type

id : A → A
id x = x

flip : ((x : A) (y : B) → C′ x y) → ((y : B) (x : A) → C′ x y)
flip f = λ y x → f x y

infixr 0 _$_
_$_ : (∀ x → B′ x) → (a : A) → B′ a
f $ x = f x

_&_ : (a : A) → (∀ x → B′ x) → B′ a
_&_ = flip _$_

_⟨_⟩_ : A → (A → B → C) → B → C
x ⟨ f ⟩ y = f x y

-- _⋉_ : (B → B → C) → (A → B) → (A → A → C)
-- _*_ ⋉ f = λ x y → f x * f y

-- _-[_]-_ : (A → B → C) → (C → D → E) → (A → B → D) → (A → B → E)
-- f -[ _*_ ]- g = λ x y → f x y * g x y

_∋_ : (A : Type ℓ) → A → A
A ∋ x = x

typeOf : {A : Type ℓa} → A → Type ℓa
typeOf {A = A} _ = A


_∘_ : {A : Type ℓa} {B : {x : A} → Type ℓb} {C : {x : A} {y : B {x}} → Type ℓc}
      (g : {x : A} (y : B {x = x}) → C {x} {y})
      (f : (x : A) → B {x = x})
  →  (x : A) → C {x = x} {y = f x}
(g ∘ f) x = g (f x)

-- ∘assoc : {A : Type ℓa} {B : {x : A} → Type ℓb}
--          {C : {x : A} {y : B {x}} → Type ℓc}
--          {D : {x : A} {y : B {x}} {z : C {x} {y}} → Type ℓc}
--          (h : {x : A} {y : B {x = x}} (z : C {x = x} {y = y}) → D {x} {y} {z})
--          (g : {x : A} (y : B {x = x}) → C {x} {y})
--          (f : (x : A) → B {x = x})
--          → h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f
-- ∘assoc h g f = refl
