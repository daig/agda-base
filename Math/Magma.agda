{-# OPTIONS --cubical --safe #-}
module Math.Magma where
open import Eq
open import Cubical.HLevel
open import Type
open import Nat
open Nat.Reasoning
open import Cubical.Core
open import Fun.Extensionality


module Group (A : Type ℓ) (_∙_ : A → A → A) where
  record group? : Type ℓ where
    field
      assoc : (x y z : A) → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)
      unit : A
      inv : A → A
      inv∙ : (x : A) → inv x ∙ x ≡ unit
      ∙inv : (x : A) → x ∙ inv x ≡ unit
  
record group : Type (ℓs ℓ) where
  field
    El : Type ℓ
    x : El → El → El
    group? : Group.group? El x
open Group


data ℤ : Type where
  [_,_] : ℕ → ℕ → ℤ
  ℤ≡ : (a⁺ a⁻ b⁺ b⁻ : ℕ) → (a⁺ + b⁻ ≡ b⁺ + a⁻) → [ a⁺ , a⁻ ] ≡ [ b⁺ , b⁻ ]
  trunc : (a b : ℤ) (p q : a ≡ b) → p ≡ q

ℤelim : ((n : ℤ) → prop? (B′ n))
      → ((a⁺ a⁻ : ℕ) → B′ ([ a⁺ , a⁻ ]))
      → (n : ℤ) → B′ n
ℤelim Bprop f [ a⁺ , a⁻ ] = f a⁺ a⁻
ℤelim {B′ = B′} Bprop  f (ℤ≡ a⁺ a⁻ b⁺ b⁻ r i)
  = J (λ y n≡m → ∀ bn bm → (λ i → B′ (n≡m i)) [ bn ≡ bm ])
      (λ bn bm → Bprop [ a⁺ , a⁻ ] bn bm)
      (ℤ≡ a⁺ a⁻ b⁺ b⁻ r) (f a⁺ a⁻) (f b⁺ b⁻) i
ℤelim Bprop f (trunc n m p q i j)
  = h?→h?′ 2 (λ x → HLevel.suc 1 (Bprop x))
             (g n) (g m) (λ k → g (p k)) (λ k → g (q k))
             (trunc n m p q) i j
  where g = ℤelim Bprop f
ℤrec : (f : ℕ → ℕ → ℤ) (feq : (a⁺ a⁻ b⁺ b⁻ : ℕ)
                              (a≡b : a⁺ + b⁻ ≡ b⁺ + a⁻)
                            → f a⁺ a⁻ ≡ f b⁺ b⁻)
    → ℤ → ℤ
ℤrec f _ [ n⁺ , n⁻ ] = f n⁺ n⁻
ℤrec f feq (ℤ≡ a⁺ a⁻ b⁺ b⁻ a≡b i) =  feq a⁺ a⁻ b⁺ b⁻ a≡b i 
ℤrec f feq (trunc a b p q i j) = trunc (g a) (g b) (cong g p) (cong g q) i j where g = ℤrec f feq
-- rec2 : {A : Type ℓa} {B : Type ℓb} (Bset : (a b : B) (p q : a ≡ b) → p ≡ q)
--        (f : A → A → B) (feq1 : (a b c : A) (r : R a b) → f a c ≡ f b c)
--                        (feqr : (a b c : A) (r : R b c) → f a b ≡ f a c)
--     → A / R → A ‌/ R → B

-- contr? A = ∃ \ (x : A) → ∀ y → x ≡ y


ℤrec2 : {B : Type ℓb}
       (f : (x⁺ x⁻ y⁺ y⁻ : ℕ) → ℤ)
       (feq1 : (a⁺ a⁻ b⁺ b⁻ c⁺ c⁻ : ℕ)
               (a≡b : a⁺ + b⁻ ≡ b⁺ + a⁻)
            → f a⁺ a⁻ c⁺ c⁻ ≡ f b⁺ b⁻ c⁺ c⁻)
       (feqr : (a⁺ a⁻ b⁺ b⁻ c⁺ c⁻ : ℕ)
               (b≡c : b⁺ + c⁻ ≡ c⁺ + b⁻)
            → f a⁺ a⁻ b⁺ b⁻ ≡ f a⁺ a⁻ c⁺ c⁻)
    → _
ℤrec2 f feql feqr = ℤrec (λ a⁺ a⁻ → ℤrec (f a⁺ a⁻) (feqr a⁺ a⁻) ?)
                         {!!}
   where
     barb : (a⁺ a⁻ b⁺ b⁻ : ℕ) → (a≡b : a⁺ + b⁻ ≡ b⁺ + a⁻) → {!!}
     barb a⁺ a⁻ b⁺ b⁻ c⁺ c⁻ a≡b = {!!} where
        foob : {!!}
        foob = ℤelim (λ _ → trunc {!!} {!!}) (λ c⁺ c⁻ → feql a⁺ a⁻ b⁺ b⁻ c⁺ c⁻ a≡b)

-- {!rec (Set.Π (λ _ → trunc)) (λ a⁺ a⁻ → rec trunc (f a⁺ a⁻) (feqr a⁺ a⁻)) (λ a⁺ a⁻ b⁺ b⁻ r → fx≡gx→f≡g !}
       

+rel : (a⁺ a⁻ b⁺ b⁻ x⁺ x⁻ y⁺ y⁻ : ℕ) → (a⁺ + b⁻ ≡ b⁺ + a⁻) → (x⁺ + y⁻ ≡ y⁺ + x⁻) → (a⁺ + x⁺) + (b⁻ + y⁻) ≡ (b⁺ + y⁺) + (a⁻ + x⁻)
+rel a⁺ a⁻ b⁺ b⁻ x⁺ x⁻ y⁺ y⁻ a≡b x≡y
  = (a⁺ + x⁺) + (b⁻ + y⁻)
  ≡⟨ rearrange a⁺ x⁺ b⁻ y⁻ ⟩ a⁺ + b⁻ + (x⁺ + y⁻)
  ≡⟨ (λ ∙ → ∙ + (x⁺ + y⁻)) ⟨$⟩ a≡b ⟩ b⁺ + a⁻ + (x⁺ + y⁻)
  ≡⟨ (λ ∙ → (b⁺ + a⁻) + ∙) ⟨$⟩ x≡y ⟩ b⁺ + a⁻ + (y⁺ + x⁻)
  ≡⟨ rearrange b⁺ a⁻ y⁺ x⁻ ⟩ b⁺ + y⁺ + (a⁻ + x⁻) ∎
  where
    rearrange : (a b c d : ℕ) → (a + b) + (c + d) ≡ (a + c) + (b + d)
    rearrange a b c d
      = a + b + (c + d)
      ≡⟨ sym (+assoc (a + b) c d) ⟩ ((a + b) + c) + d
      ≡⟨ (λ ∙ → ∙ + d) ⟨$⟩ +assoc a b c ⟩ a + (b + c) + d
      ≡⟨ (λ ∙ → a + ∙ + d) ⟨$⟩ +comm b c ⟩ a + (c + b) + d
      ≡⟨ sym ((λ ∙ → ∙ + d) ⟨$⟩ +assoc a c b ) ⟩ ((a + c) + b) + d
      ≡⟨ +assoc (a + c) b d ⟩ (a + c) + (b + d) ∎

