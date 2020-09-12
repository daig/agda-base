{-# OPTIONS --without-K #-}
module Fun where
open import Type
open Vars

ι : A → A
ι x = x


flip : ((x : A) (y : B) → C′ x y) → ((y : B) (x : A) → C′ x y)
flip f = λ y x → f x y

infixr 0 _$_
_$_ : ((x : A) → B′ x) → ((x : A) → B′ x)
f $ x = f x

_▸_ : (a : A) → (∀ a → B′ a) → B′ a
_▸_ = flip _$_

_⟨_⟩_ : A → (A → B → C) → B → C
x ⟨ f ⟩ y = f x y

_⋉_ : (B → B → C) → (A → B) → (A → A → C)
_*_ ⋉ f = λ x y → f x * f y


_-[_]-_ : (A → B → C) → (C → D → E) → (A → B → D) → (A → B → E)
f -[ _*_ ]- g = λ x y → f x y * g x y

_∋_ : (A : Type ℓa) → A → A
A ∋ x = x

typeOf : {A : Type ℓa} → A → Type ℓa
typeOf {A = A} _ = A

