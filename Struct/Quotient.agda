{-# OPTIONS --cubical --safe #-}
module Struct.Quotient where
open import Eq
open import Cubical.HLevel
open import Type
open import Nat
open Nat.Reasoning
open import Cubical.Core
open import Sigma

data _/_ (A : Type ℓa) (_∼_ : A → A → Type ℓb) : Type (ℓa ⊔ ℓb) where
  ⟦_⟧ : (a : A) → A / _∼_
  ≡/ : (a b : A) → (a∼b : a ∼ b) → ⟦ a ⟧ ≡ ⟦ b ⟧
  set/ : set? (A / _∼_)

private
  variable
    _∼_ : A → A → Type ℓ
    B∼ : A / _∼_ → Type ℓ
    C∼ : A / _∼_ → A / _∼_ → Type ℓ


module Quotient where
  module ≡ where
    elim : (Bprop : (x : A / _∼_ ) → prop? (B∼ x))
            {a₁ a₂ : A / _∼_ }
            (a₁≡a₂ : a₁ ≡ a₂)
            (b₁ : B∼ a₁)
            (b₂ : B∼ a₂) → ((λ i → B∼ (a₁≡a₂ i)) [ b₁ ≡ b₂ ])
    elim {B∼ = B∼} Bprop {a₁ = a₁}
      = J (λ x a₁≡x → ∀ b₁ bₓ → (λ i → B∼ (a₁≡x i)) [ b₁ ≡ bₓ ]) (Bprop a₁)
  module Prop where
    elim : ((x : A / _∼_ ) → prop? (B∼ x))
            → ((a : A      ) → B∼ ( ⟦ a ⟧))
            → ( x : A / _∼_) → B∼     x
    elim {A = A} {_∼_ = _∼_} {B∼ = B∼} Bprop f = go where
      go : (x : A / _∼_) → B∼ x
      go ⟦ x ⟧ = f x
      go (≡/ a b ∼ i) = ≡.elim {B∼ = B∼} Bprop (≡/ a b ∼) (f a) (f b) i
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

  rec : (Bset : set? B)
        (f : A → B)
        (feq : (a b : A) (r : a ∼ b) → f a ≡ f b)
      → A / _∼_ → B
  rec Bset f feq ⟦ a ⟧ = f a
  rec Bset f feq (≡/ a b r i) = feq a b r i
  rec Bset f feq (set/ x y p q i j) = Bset (g x) (g y) (cong g p) (cong g q) i j
    where g = rec Bset f feq

  rec2 :  (Bset : set? B)
      (f : A → A → B) (feql : (a b c : A) (r : a ∼ b) → f a c ≡ f b c)
                      (feqr : (a b c : A) (r : b ∼ c) → f a b ≡ f a c)
      → A / _∼_ → A / _∼_ → B
  rec2 {B = B} {A = A} {_∼_ = _∼_} Bset f feql feqr = rec {B = (x : A / _∼_) → B} (HSet.Π (λ _ → Bset))
                              (λ a → rec {B = B} Bset (f a) (feqr a))
                              (λ a b r → Eq.Π (Prop.elim {A = A}
                                                         {B∼ = λ x → rec Bset (f a) (feqr a) x
                                                                   ≡ rec Bset (f b) (feqr b) x}
                                                         (λ (x : A / _∼_) → Bset (rec Bset (f a) (feqr a) x) (rec Bset (f b) (feqr b) x)) 
                                              (λ c → feql a b c r)))

swap-middle = λ (a x y b : ℕ) →
    a + x +(y + b) ≡⟨ sym (+assoc (a + x) y b)    ⟩
    a + x + y + b  ≡[ i ]⟨ +assoc a x y i + b ⟩
    a +(x + y)+ b  ≡[ i ]⟨ a + +comm x y i + b    ⟩
    a +(y + x)+ b  ≡[ i ]⟨ +assoc a y x (~ i) + b     ⟩
    a + y + x + b  ≡⟨ +assoc (a + y) x b    ⟩
    a + y +(x + b) ∎

module Int where
  𝕫 = ℕ × ℕ
  _𝕫∼_ : 𝕫 → 𝕫 → Type
  (a⁺ , a⁻) 𝕫∼ (b⁺ , b⁻) = a⁺ + b⁻ ≡ b⁺ + a⁻
  ℤ = 𝕫 / _𝕫∼_

  _++_ : 𝕫 → 𝕫 → 𝕫
  (a⁺ , a⁻) ++ (b⁺ , b⁻) = a⁺ + b⁺ , a⁻ + b⁻
  ++∼ : (a b c d : 𝕫) → a 𝕫∼ b → c 𝕫∼ d → (a ++ c) 𝕫∼ (b ++ d)
  ++∼ (a⁺ , a⁻) (b⁺ , b⁻) (c⁺ , c⁻) (d⁺ , d⁻) a∼b c∼d =
    a⁺ + c⁺ + (b⁻ + d⁻) ≡⟨ swap-middle a⁺ c⁺ b⁻ d⁻ ⟩
    a⁺ + b⁻ + (c⁺ + d⁻) ≡[ i ]⟨ a∼b i + c∼d i    ⟩
    b⁺ + a⁻ + (d⁺ + c⁻) ≡⟨ swap-middle b⁺ a⁻ d⁺ c⁻ ⟩
    b⁺ + d⁺ + (a⁻ + c⁻) ∎
  _⊕_ : ℤ → ℤ → ℤ
  _⊕_ = Quotient.rec2 set/
    (λ x y → ⟦ x ++ y ⟧) -- ← actual implementation
    (λ x₀ x₁ y x₀≡x₁ → ≡/ _ _ (++∼ x₀ x₁ y  y  x₀≡x₁ ✓))
    (λ x y₀ y₁ y₀≡y₁ → ≡/ _ _ (++∼ x  x  y₀ y₁ ✓ y₀≡y₁))
