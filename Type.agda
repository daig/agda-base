{-# OPTIONS --safe --without-K #-}
-- https://hott-uf.github.io/2017/abstracts/twoleveltt.pdf
module Type where
open import Agda.Primitive public
  renaming (Set to Type; Setω to Typeω
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

module Vars where
    variable
        ℓ ℓa ℓb ℓc ℓd ℓe ℓf ℓh : Level
        A : Type ℓa
        B : Type ℓb
        B′ : A → Type ℓb
        C : Type ℓc
        C′ : A → B → Type ℓc
        D : Type ℓd
        E : Type ℓe
