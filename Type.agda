{-# OPTIONS --cubical --safe #-}
-- https://hott-uf.github.io/2017/abstracts/twoleveltt.pdf
module Type where
open import Agda.Primitive public
  renaming (Set to Type; Setω to Typeω; SSet to SType
           ;lzero to ℓ0; lsuc to ℓs)
  using    (Level; _⊔_)

{- 
postulate Level : Set

-- MAlonzo compiles Level to (). This should be safe, because it is
-- not possible to pattern match on levels.

{-# BUILTIN LEVEL Level #-}

{-# BUILTIN LEVELZERO ℓ0  #-}
{-# BUILTIN LEVELSUC  ℓs  #-}
{-# BUILTIN LEVELMAX  _⊔_ #-}
infixl 6 _⊔_
-}

variable
    ℓ ℓa ℓb ℓc ℓd ℓe ℓf ℓh : Level
    A : Type ℓa
    B : Type ℓb
    B′ : A → Type ℓb
    C : Type ℓc
    C′ : (x : A) → B′ x → Type ℓc
    D : Type ℓd
    D′ : (x : A) → (y : B′ x) → C′ x y → Type ℓd
    E : Type ℓe
    E′ : (x : A) → (y : B′ x) → (z : C′ x y) → D′ x y z → Type ℓe
