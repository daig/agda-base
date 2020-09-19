{-# OPTIONS --cubical #-}
module Int where

open import Nat
open import String using (𝕊)

infix 8 pos

data ℤ : Set where pos negsuc : (n : ℕ) → ℤ

{-# BUILTIN INTEGER       ℤ    #-}
{-# BUILTIN INTEGERPOS    pos    #-}
{-# BUILTIN INTEGERNEGSUC negsuc #-}

primitive primShowInteger : ℤ → 𝕊
