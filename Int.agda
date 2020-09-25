{-# OPTIONS --cubical #-}
module Int where

open import Nat using (ℕ; s)
open import String using (𝕊)
open import Type

infix 8 pos

data ℤ : Set where pos negsuc : (n : ℕ) → ℤ

{-# BUILTIN INTEGER       ℤ    #-}
{-# BUILTIN INTEGERPOS    pos    #-}
{-# BUILTIN INTEGERNEGSUC negsuc #-}

primitive primShowInteger : ℤ → 𝕊

module Sign where
    data Sign : Type where
        + : Sign
        - : Sign
    op : Sign → Sign
    op = λ { + → -; - → +}
    _*_ : Sign → Sign → Sign
    + * x = x
    - * x = op x
open Sign using (Sign)
signed : Sign → ℕ → ℤ
signed _ 0 = pos 0
signed Sign.+ n = pos n
signed Sign.- (s n) = negsuc n

_+_ : ℤ → ℤ → ℤ
pos 0 + m = m
pos n + pos m = pos (n Nat.+ m)
pos (s n) + negsuc (s m) = pos n + negsuc m
pos (s n) + negsuc 0 = pos n
negsuc (s n) + pos (s m) = negsuc n + pos m
negsuc 0 + pos (s m) = pos m
negsuc n + pos 0 = negsuc n
negsuc n + negsuc m = negsuc (s (n Nat.+ m))

-- _-_ : ℕ → ℕ → ℕ
-- n     - 0 = n
-- 0  - s m = 0
-- s n - s m = n - m


∥_∥ : ℤ → ℕ
∥ pos n ∥ = n
∥ negsuc n ∥ = s n
sign : ℤ → Sign
sign (pos _) = Sign.+
sign (negsuc _) = Sign.-

_*_ : ℤ → ℤ → ℤ
n * m = signed (sign n Sign.* sign m ) (∥ n ∥ Nat.* ∥ m ∥)
