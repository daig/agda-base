{-# OPTIONS --without-K #-}
module Nat where
open import Bool

data ℕ : Set where z : ℕ; s : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}



infix  4 _==_ _<_
infixl 6 _+_ _-_
infixl 7 _*_

_+_ : ℕ → ℕ → ℕ
z  + m = m
s n + m = s (n + m)

{-# BUILTIN NATPLUS _+_ #-}

_-_ : ℕ → ℕ → ℕ
n     - z = n
z  - s m = z
s n - s m = n - m

{-# BUILTIN NATMINUS _-_ #-}

_*_ : ℕ → ℕ → ℕ
z  * m = z
s n * m = m + n * m

{-# BUILTIN NATTIMES _*_ #-}

_==_ : ℕ → ℕ → 𝔹
z  == z  = true
s n == s m = n == m
_     == _     = false

{-# BUILTIN NATEQUALS _==_ #-}

_<_ : ℕ → ℕ → 𝔹
_     < z  = false
z  < s _ = true
s n < s m = n < m

{-# BUILTIN NATLESS _<_ #-}
