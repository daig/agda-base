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
    *distrL : ∀ a b c → (a + b) * c ≡ (a * c) + (b * c)
    *distrL 0 b c = ✓
    *distrL (s a) b c = ((_+_ c) ⟨$⟩ *distrL a b c)
                    ⋯ sym (+assoc c (a * c) (b * c) )
    *assoc : (a b c : ℕ) → (a * b) * c ≡ a * (b * c)
    *assoc 0 b c = ✓
    *assoc (s a) b c = *distrL b (a * b) c
                        ⋯ ((λ ∙ → b * c + ∙) ⟨$⟩ *assoc a b c )
    -- *assoc (s a) b c =
    *0 : ∀ a → a * 0 ≡ 0
    *0 0 = ✓
    *0 (s a) = *0 a
    *1 : ∀ a → a * 1 ≡ a
    *1 zero = ✓
    *1 (s a) = s ⟨$⟩ *1 a
    *s : (a b : ℕ) → a * s b ≡ a + a * b
    *s zero b = ✓
    *s (s a) b =
        s a * s b ≡⟨⟩
        s b + a * s b ≡⟨ (λ ∙ → s b + ∙) ⟨$⟩ *s a b ⟩
        s b + (a + a * b) ≡⟨ sym (+assoc (s b) a (a * b)) ⟩
        s (b + a + a * b ) ≡⟨ (λ ∙ → s (∙ + a * b)) ⟨$⟩ +comm b a ⟩
        s a + b + a * b ≡⟨ +assoc (s a) b (a * b) ⟩
        s a + s a * b ∎

    *comm : (a b : ℕ) → a * b ≡ b * a
    *comm 0 b = sym ( *0 b)
    *comm (s a) b = ((_+_ b) ⟨$⟩ *comm a b)
                    ⋯ sym (*s b a)
