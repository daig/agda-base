{-# OPTIONS --cubical --safe #-}
module Nat where
open import Bool

data ℕ : Set where zero : ℕ; s : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}



infix  4 _==_ _<_
infixl 6 _+_ _-_
infixl 7 _*_

_+_ : ℕ → ℕ → ℕ
0  + m = m
s n + m = s (n + m)

{-# BUILTIN NATPLUS _+_ #-}

_-_ : ℕ → ℕ → ℕ
n     - 0 = n
0  - s m = 0
s n - s m = n - m

{-# BUILTIN NATMINUS _-_ #-}

_*_ : ℕ → ℕ → ℕ
0  * m = 0
s n * m = m + n * m

{-# BUILTIN NATTIMES _*_ #-}

_==_ : ℕ → ℕ → 𝔹
0  == 0  = true
s n == s m = n == m
_     == _     = false

{-# BUILTIN NATEQUALS _==_ #-}

_<_ : ℕ → ℕ → 𝔹
_     < 0  = false
0  < s _ = true
s n < s m = n < m

{-# BUILTIN NATLESS _<_ #-}

module Nat where
    module Reasoning where
      open import Eq
      +assoc : (a b c : ℕ) → (a + b) + c ≡ a + (b + c)
      +assoc 0 b c = ✓
      +assoc (s a) b c =  s ⟨$⟩ (+assoc a b c)
      +0 : (a : ℕ) → a + 0 ≡ a
      +0 0 = ✓
      +0 (s a) = s ⟨$⟩ +0 a
      +s : (a b : ℕ) → a + s b ≡ s (a + b)
      +s 0 b = ✓
      +s (s a) b = s ⟨$⟩ +s a b
      +comm : (a b : ℕ) → a + b ≡ b + a
      +comm 0 b = sym ( +0 b)
      +comm (s a) b = s a + b
        ≡⟨ s ⟨$⟩ +comm a b ⟩ s (b + a)
        ≡⟨ sym (+s b a) ⟩ b + s a ∎
