{-# OPTIONS --cubical --safe #-}
module Struct.Quotient where
open import Eq
open import Cubical.HLevel
open import Type
open import Nat using (ℕ; s)
open import Cubical.Core hiding (A; B; C)
open import Sigma

data _/_ (A : Type ℓa) (_∼_ : A → A → Type ℓb) : Type (ℓa ⊔ ℓb) where
  ⟦_⟧ : (a : A) → A / _∼_
  ≡/ : (a₀ a₁ : A) → (a∼ : a₀ ∼ a₁) → ⟦ a₀ ⟧ ≡ ⟦ a₁ ⟧
  set/ : set? (A / _∼_)

private
  variable
    _∼_ : A → A → Type ℓ
    B∼ : A / _∼_ → Type ℓ
    C∼ : A / _∼_ → A / _∼_ → Type ℓ
    D∼ : A / _∼_ → A / _∼_ → A / _∼_ → Type ℓ

module ≡ where
    elim : {A : Type ℓa} {B : A → Type ℓb}
            (Bprop : (x : A ) → prop? (B x))
            {a₁ a₂ : A } (a₁≡a₂ : a₁ ≡ a₂)
            (b₁ : B a₁) (b₂ : B a₂) → ((λ i → B (a₁≡a₂ i)) [ b₁ ≡ b₂ ])
    elim {B = B} Bprop {a₁ = a₁}
        = J (λ x a₁≡x → ∀ b₁ bₓ → (λ i → B (a₁≡x i)) [ b₁ ≡ bₓ ]) (Bprop a₁)

module Quotient where
  module Prop where
    elim : ((x : A / _∼_ ) → prop? (B∼ x))
            → ((a : A      ) → B∼ ( ⟦ a ⟧))
            → ( x : A / _∼_) → B∼     x
    elim {A = A} {_∼_ = _∼_} {B∼ = B∼} Bprop f = go where
      go : (x : A / _∼_) → B∼ x
      go ⟦ x ⟧ = f x
      go (≡/ a b ∼ i) = ≡.elim Bprop (≡/ a b ∼) (f a) (f b) i
      go (set/ x y p q i j) =
        h?→h?′ 2 (λ x → HLevel.suc 1 (Bprop x))
                 (g x) (g y) (cong g p) (cong g q)
                 (set/ x y p q) i j
        where g = elim Bprop f
    elim2 : ((x y : A / _∼_ ) → prop? (C∼ x y))
          → ((a b : A      ) → C∼ ⟦ a ⟧ ⟦ b ⟧)
          → ( x y : A / _∼_) → C∼   x     y
    elim2 Cprop f = elim (λ x → HProp.Π (Cprop x))
                         (λ x → elim (Cprop ⟦ x ⟧) (f x))
    elim3 : ((x y z : A / _∼_ ) → prop? (D∼ x y z))
          → ((a b c : A      ) → D∼ ⟦ a ⟧ ⟦ b ⟧ ⟦ c ⟧)
          → ( x y z : A / _∼_) → D∼   x     y     z
    elim3 Dprop f = elim2 (λ x y → HProp.Π (Dprop x y) )
                          λ x y → elim (Dprop ⟦ x ⟧ ⟦ y ⟧) (f x y)

  rec : (Bset : set? B)
        (f : A → B)
        (feq : (a₀ a₁ : A) (r : a₀ ∼ a₁) → f a₀ ≡ f a₁)
      → A / _∼_ → B
  rec Bset f feq ⟦ a ⟧ = f a
  rec Bset f feq (≡/ a₀ a₁ r i) = feq a₀ a₁ r i
  rec Bset f feq (set/ x y p q i j) = Bset (g x) (g y) (cong g p) (cong g q) i j
    where g = rec Bset f feq

  rec2 :  (Bset : set? B)
      (f : A → A → B) (fa~ : (a₀ a₁ b : A) (r : a₀ ∼ a₁) → f a₀ b ≡ f a₁ b)
                      (fb~ : (a b₀ b₁ : A) (r : b₀ ∼ b₁) → f a b₀ ≡ f a b₁)
      → A / _∼_ → A / _∼_ → B
  rec2 {A = A} {_∼_ = _∼_} Bset f fa~ fb~ = rec (HSet.Π (λ _ → Bset))
                              (λ a → rec Bset (f a) (fb~ a))
                              (λ a₀ a₁ r → Eq.Π (Prop.elim
                                                   (λ (x : A / _∼_) → Bset (rec Bset (f a₀) (fb~ a₀) x) (rec Bset (f a₁) (fb~ a₁) x)) 
                                                   (λ c → fa~ a₀ a₁ c r)))
  rec3 :  (Bset : set? B)
      (f : A → A → A → B) (feq1 : (a₀ a₁ b c : A) (r : a₀ ∼ a₁) → f a₀ b c ≡ f a₁ b c)
                          (feq2 : (a b₀ b₁ c : A) (r : b₀ ∼ b₁) → f a b₀ c ≡ f a b₁ c)
                          (feq3 : (a b c₀ c₁ : A) (r : c₀ ∼ c₁) → f a b c₀ ≡ f a b c₁)
      → A / _∼_ → A / _∼_ → A / _∼_ → B
  rec3 {B = B} {A = A} {_∼_ = _∼_} Bset f fa~ fb~ fc~ = rec2 (HSet.Π \ _ → Bset) (λ a b → rec Bset (f a b) (fc~ a b))
    (λ a₀ a₁ b r → Eq.Π (Prop.elim
                        (λ (x : A / _∼_) → Bset (rec Bset (f a₀ b) (fc~ a₀ b) x) (rec Bset (f a₁ b) (fc~ a₁ b) x)) 
                        (λ c → fa~ a₀ a₁ b c r)))
    (λ a b₀ b₁ r → Eq.Π (Prop.elim
                        (λ (x : A / _∼_) → Bset (rec Bset (f a b₀) (fc~ a b₀) x) (rec Bset (f a b₁) (fc~ a b₁) x)) 
                        (λ c → fb~ a b₀ b₁ c r)))


module Int where
  Z = ℕ × ℕ
  _Z∼_ : Z → Z → Type
  (a⁺ , a⁻) Z∼ (b⁺ , b⁻) = a⁺ Nat.+ b⁻ ≡ b⁺ Nat.+ a⁻
  ℤ = Z / _Z∼_

  module _  where
    open Nat
    open Nat.Reasoning
    swap-middle = λ (a x y b : ℕ) →
        a + x +(y + b) ≡[ i ]⟨ +assoc (a + x) y b (~ i)    ⟩
        a + x + y + b  ≡[ i ]⟨ +assoc a x y i + b ⟩
        a +(x + y)+ b  ≡[ i ]⟨ a + +comm x y i + b    ⟩
        a +(y + x)+ b  ≡[ i ]⟨ +assoc a y x (~ i) + b     ⟩
        a + y + x + b  ≡⟨ +assoc (a + y) x b    ⟩
        a + y +(x + b) ∎
    _⊕_ : Z → Z → Z
    (a⁺ , a⁻) ⊕ (b⁺ , b⁻) = a⁺ + b⁺ , a⁻ + b⁻
    +∼ : (a b c d : Z) → a Z∼ b → c Z∼ d → (a ⊕ c) Z∼ (b ⊕ d)
    +∼ (a⁺ , a⁻) (b⁺ , b⁻) (c⁺ , c⁻) (d⁺ , d⁻) a∼b c∼d =
        a⁺ + c⁺ + (b⁻ + d⁻) ≡⟨ swap-middle a⁺ c⁺ b⁻ d⁻ ⟩
        a⁺ + b⁻ + (c⁺ + d⁻) ≡[ i ]⟨ a∼b i + c∼d i    ⟩
        b⁺ + a⁻ + (d⁺ + c⁻) ≡⟨ swap-middle b⁺ a⁻ d⁺ c⁻ ⟩
        b⁺ + d⁺ + (a⁻ + c⁻) ∎
  _+_ : ℤ → ℤ → ℤ
  _+_ = Quotient.rec2 set/
    (λ x y → ⟦ x ⊕ y ⟧) -- ← actual implementation
    (λ x₀ x₁ y x₀≡x₁ → ≡/ _ _ (+∼ x₀ x₁ y  y  x₀≡x₁ ✓))
    (λ x y₀ y₁ y₀≡y₁ → ≡/ _ _ (+∼ x  x  y₀ y₁ ✓ y₀≡y₁))
  private
    zero zero' : ℤ
    zero = ⟦ 0 , 0 ⟧
    zero' = ⟦ 1 , 1 ⟧
    _ : zero ≡ zero'
    _ = ≡/ (0 , 0) (1 , 1) ✓
  +assoc : (a b c : ℤ) → (a + b) + c ≡ a + (b + c)
  +assoc a b c = {!!}
  -- +assoc (s a) b c =  s ⟨$⟩ (+assoc a b c)
  +0 : (a : ℤ) → a + zero ≡ a
  +0 n =
    n + ⟦ 0 , 0 ⟧ ≡⟨⟩
    {!!}
    ≡⟨ {!!} ⟩ n ∎
  -- -- +0 (s a) = s ⟨$⟩ +0 a
  -- +s : (a b : ℕ) → a + s b ≡ s (a + b)
  -- +s 0 b = ✓
  -- +s (s a) b = s ⟨$⟩ +s a b
  -- +comm : (a b : ℕ) → a + b ≡ b + a
  -- +comm 0 b = sym ( +0 b)
  -- +comm (s a) b = s a + b
  --     ≡⟨ s ⟨$⟩ +comm a b ⟩ s (b + a)
  --     ≡⟨ sym (+s b a) ⟩ b + s a ∎
  -- -- *distrL : ∀ a b c → (a + b) * c ≡ (a * c) + (b * c)
  -- -- *distrL 0 b c = ✓
  -- -- *distrL (s a) b c = ((_+_ c) ⟨$⟩ *distrL a b c)
  -- --                 ⋯ sym (+assoc c (a * c) (b * c) )
  -- -- *assoc : (a b c : ℕ) → (a * b) * c ≡ a * (b * c)
  -- -- *assoc 0 b c = ✓
  -- -- *assoc (s a) b c = *distrL b (a * b) c
  -- --                     ⋯ ((λ ∙ → b * c + ∙) ⟨$⟩ *assoc a b c )
  -- -- -- *assoc (s a) b c =
  -- -- *0 : ∀ a → a * 0 ≡ 0
  -- -- *0 0 = ✓
  -- -- *0 (s a) = *0 a
  -- -- *1 : ∀ a → a * 1 ≡ a
  -- -- *1 zero = ✓
  -- -- *1 (s a) = s ⟨$⟩ *1 a
  -- -- *s : (a b : ℕ) → a * s b ≡ a + a * b
  -- -- *s zero b = ✓
  -- -- *s (s a) b =
  -- --     s a * s b ≡⟨⟩
  -- --     s b + a * s b ≡⟨ (λ ∙ → s b + ∙) ⟨$⟩ *s a b ⟩
  -- --     s b + (a + a * b) ≡⟨ sym (+assoc (s b) a (a * b)) ⟩
  -- --     s (b + a + a * b ) ≡⟨ (λ ∙ → s (∙ + a * b)) ⟨$⟩ +comm b a ⟩
  -- --     s a + b + a * b ≡⟨ +assoc (s a) b (a * b) ⟩
  -- --     s a + s a * b ∎

  -- -- *comm : (a b : ℕ) → a * b ≡ b * a
  -- -- *comm 0 b = sym ( *0 b)
  -- -- *comm (s a) b = ((_+_ b) ⟨$⟩ *comm a b)
  -- --                 ⋯ sym (*s b a)
