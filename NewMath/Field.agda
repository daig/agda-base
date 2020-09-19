{-# OPTIONS --prop --cubical --without-K #-}
module Field where
open import Cubical.Eq
open import Empty

import Float

record Field : Set₁ where
  infixl 6 _+_
  infixl 7 _×_ _÷_
  infix 8 -_ 𝟙÷_
  field
    Elt : Set
    _+_ : Elt → Elt → Elt
    +assoc : ∀ x y z → x + y + z ≡ x + (y + z)
    +comm : ∀ x y → x + y ≡ y + x
    𝟘 : Elt
    𝟘+ : ∀ x → 𝟘  + x ≡ x 
  +𝟘 : ∀ x → x + 𝟘  ≡ x
  +𝟘 x = trans (+comm x 𝟘) (𝟘+ x)
  field
    -_ : Elt → Elt
    -inv : ∀ x → - x + x ≡ 𝟘
  inv- : ∀ x → x + - x ≡ 𝟘
  inv- x = trans (+comm x (- x)) (-inv x)
  _-_ : Elt → Elt → Elt
  x - y = x + - y
  field

    _×_ : Elt → Elt → Elt
    ×assoc : ∀ x y z → x × y × z ≡ x × (y × z)
    ×comm : ∀ x y → x × y ≡ y × x
    𝟙 : Elt
    𝟙× : ∀ x → 𝟙 × x ≡ x 
  ×𝟙 : ∀ x → x × 𝟙  ≡ x 
  ×𝟙 x = trans (×comm x 𝟙) (𝟙× x)

  field +×distrib : ∀ a b c → a × (b + c) ≡ a × b + a × c
  field _÷_ : (a b : Elt) → {nonzero : ¬ (b ≡ 𝟘)} → Elt
  𝟙÷_ : (b : Elt) → {nonzero : ¬ (b ≡ 𝟘)} → Elt
  (𝟙÷ b) {p} = (𝟙 ÷ b) {p}

open Field
