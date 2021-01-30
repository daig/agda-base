{-# OPTIONS --cubical #-}
module Int where

open import Nat using (ℕ; s)
module Nats = Nat.Nat.Reasoning
open import String using (𝕊)
open import Type

infix 8 pos
-- infix  4 _==_ _<_
infixl 6 _+_ -- _-_
infixl 7 _*_

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


∥_∥ : ℤ → ℕ
∥ pos n ∥ = n
∥ negsuc n ∥ = s n
sign : ℤ → Sign
sign (pos _) = Sign.+
sign (negsuc _) = Sign.-

_*_ : ℤ → ℤ → ℤ
n * m = signed (sign n Sign.* sign m ) (∥ n ∥ Nat.* ∥ m ∥)

_+_ : ℤ → ℤ → ℤ
pos 0 + m = m
pos n + pos m = pos (n Nat.+ m)
pos (s n) + negsuc (s m) = pos n + negsuc m
pos (s n) + negsuc 0 = pos n
negsuc (s n) + pos (s m) = negsuc n + pos m
negsuc 0 + pos (s m) = pos m
negsuc n + pos 0 = negsuc n
negsuc n + negsuc m = negsuc (s (n Nat.+ m))

module Reasoning where
    open import Eq
    +assoc : (a b c : ℤ) → (a + b) + c ≡ a + (b + c)
    +assoc (pos 0) (pos b) (pos c) = ✓
    +assoc (pos (s a)) (pos b) (pos c) = {!!}

--     +assoc (s a) b c =  s ⟨$⟩ (+assoc a b c)
    -- +0 : (a : ℕ) → a + 0 ≡ a
    -- +0 0 = ✓
    -- +0 (s a) = s ⟨$⟩ +0 a
    -- +s : (a b : ℕ) → a + s b ≡ s (a + b)
    -- +s 0 b = ✓
    -- +s (s a) b = s ⟨$⟩ +s a b
    -- +comm : (a b : ℕ) → a + b ≡ b + a
    -- +comm 0 b = sym ( +0 b)
    -- +comm (s a) b = s a + b
    --     ≡⟨ s ⟨$⟩ +comm a b ⟩ s (b + a)
    --     ≡⟨ sym (+s b a) ⟩ b + s a ∎
    -- *distrL : ∀ a b c → (a + b) * c ≡ (a * c) + (b * c)
    -- *distrL 0 b c = ✓
    -- *distrL (s a) b c = ((_+_ c) ⟨$⟩ *distrL a b c)
    --                 ⋯ sym (+assoc c (a * c) (b * c) )
    -- *assoc : (a b c : ℕ) → (a * b) * c ≡ a * (b * c)
    -- *assoc 0 b c = ✓
    -- *assoc (s a) b c = *distrL b (a * b) c
    --                     ⋯ ((λ ∙ → b * c + ∙) ⟨$⟩ *assoc a b c )
    -- -- *assoc (s a) b c =
    -- *0 : ∀ a → a * 0 ≡ 0
    -- *0 0 = ✓
    -- *0 (s a) = *0 a
    -- *1 : ∀ a → a * 1 ≡ a
    -- *1 zero = ✓
    -- *1 (s a) = s ⟨$⟩ *1 a
    -- *s : (a b : ℕ) → a * s b ≡ a + a * b
    -- *s zero b = ✓
    -- *s (s a) b =
    --     s a * s b ≡⟨⟩
    --     s b + a * s b ≡⟨ (λ ∙ → s b + ∙) ⟨$⟩ *s a b ⟩
    --     s b + (a + a * b) ≡⟨ sym (+assoc (s b) a (a * b)) ⟩
    --     s (b + a + a * b ) ≡⟨ (λ ∙ → s (∙ + a * b)) ⟨$⟩ +comm b a ⟩
    --     s a + b + a * b ≡⟨ +assoc (s a) b (a * b) ⟩
    --     s a + s a * b ∎

    -- *comm : (a b : ℕ) → a * b ≡ b * a
    -- *comm 0 b = sym ( *0 b)
    -- *comm (s a) b = ((_+_ b) ⟨$⟩ *comm a b)
    --                 ⋯ sym (*s b a)

-- _-_ : ℕ → ℕ → ℕ
-- n     - 0 = n
-- 0  - s m = 0
-- s n - s m = n - m

