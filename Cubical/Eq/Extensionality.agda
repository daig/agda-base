{-# OPTIONS --cubical --safe #-}
module Cubical.Eq.Extensionality where
open import Cubical.Core
open import Cubical.Core public using (_≡_)

private
  variable
    ℓ ℓa ℓb ℓc : Level
    A : Type ℓa
    B : Type ℓb
    a b x y : A

-- subst : {A : Type ℓ} {x y : A} (P : A → Type ℓ) → x ≡ y → P x → P y 
-- subst {A = A} P x≡y p = transp (λ i → P (x≡y i)) i0 p

funExt : {B : A → I → Type ℓ} {f : (x : A) → B x i0} {g : (x : A) → B x i1}
      → (       (x : A) → (B x ) [ f x ≡ g x ] )
      → (λ i → (x : A) → B x i) [ f   ≡ g   ]
funExt fx≡gx i x = fx≡gx x i
