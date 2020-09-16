{-# OPTIONS --cubical --safe #-}
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

module Nat where
    module Reasoning where
      open import Cubical.Eq
      +assoc : (a b c : ℕ) → (a + b) + c ≡ a + (b + c)
      +assoc z b c = ✓
      +assoc (s a) b c =  s ⟨$⟩ (+assoc a b c)
      +0 : (a : ℕ) → a + z ≡ a
      +0 z = ✓
      +0 (s a) = s ⟨$⟩ +0 a
      +s : (a b : ℕ) → a + s b ≡ s (a + b)
      +s z b = ✓
      +s (s a) b = s ⟨$⟩ +s a b
      +comm : (a b : ℕ) → a + b ≡ b + a
      +comm z b = sym ( +0 b)
      +comm (s a) b = s a + b
        ≡⟨ s ⟨$⟩ +comm a b ⟩ s (b + a)
        ≡⟨ sym (+s b a) ⟩ b + s a ∎
