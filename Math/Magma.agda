{-# OPTIONS --cubical #-}
module Math.Magma where
open import Cubical.Eq
open import Type
open import Nat
open Nat.Reasoning
open import Cubical.Core

_∙_ = trans


variable ℓ ℓa ℓb : Level

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

rec : (f : ℕ → ℕ → ℤ) (feq : (a⁺ a⁻ b⁺ b⁻ : ℕ)
                             (a≡b : a⁺ + b⁻ ≡ b⁺ + a⁻)
                           → f a⁺ a⁻ ≡ f b⁺ b⁻)
    → ℤ → ℤ
rec f feq [ n⁺ , n⁻ ] = f n⁺ n⁻
rec f feq (ℤ≡ a⁺ a⁻ b⁺ b⁻ a≡b i) =  feq a⁺ a⁻ b⁺ b⁻ a≡b i 
rec f feq (trunc a b p q i j) = trunc (g a) (g b) (cong g p) (cong g q) i j where g = rec f feq
-- rec2 : {A : Type ℓa} {B : Type ℓb} (Bset : (a b : B) (p q : a ≡ b) → p ≡ q)
--        (f : A → A → B) (feq1 : (a b c : A) (r : R a b) → f a c ≡ f b c)
--                        (feqr : (a b c : A) (r : R b c) → f a b ≡ f a c)
--     → A / R → A ‌/ R → B

funExtPath : {A : Type ℓa} {B : A → I → Type ℓb} {f : (x : A) → B x i0} {g : (x : A) → B x i1}
-- funExtPath : {A : Type ℓa} {B : A → I → Type ℓb} {f : (x : A) → B x i0} {g : (x : A) → B x i1}
          → (∀ x → B x [ f x ≡ g x ]) ≡ ((λ i → ∀ x → B x i) [ f ≡ g ])
funExtPath = {!!}

hlvlΠ : {A : Type ℓa} {B : A → Type ℓb}
      → ∀ n → ((x : A) → hlvl? n (B x))
            → hlvl? n ((x : A) → B x)
hlvlΠ 0 h = (λ x → π₁ (h x)) , λ f i a → π₂ (h a) (f a) i
hlvlΠ 1 h f g i x = h x (f x) (g x) i
hlvlΠ {A = A} (s (s n)) h f g = {!!} where
  go : hlvl? (s n) ((x : A) → f x ≡ g x)
  go = hlvlΠ (s n) \ x → h x (f x) (g x)
-- contr? A = ∃ \ (x : A) → ∀ y → x ≡ y


rec2 : {B : Type ℓb}
       (f : (x y z w : ℕ) → ℤ) (feq1 : (a⁺ a⁻ b⁺ b⁻ c⁺ c⁻ : ℕ) (a≡b : a⁺ + b⁻ ≡ b⁺ + a⁻) → f a⁺ a⁻ c⁺ c⁻ ≡ f b⁺ b⁻ c⁺ c⁻)
                               (feqr : (a⁺ a⁻ b⁺ b⁻ c⁺ c⁻ : ℕ) (b≡c : b⁺ + c⁻ ≡ c⁺ + b⁻) → f a⁺ a⁻ b⁺ b⁻ ≡ f a⁺ a⁻ c⁺ c⁻)
    → ℤ → ℤ → ℤ
rec2 f feq1 feqr = {!!}
       

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

-- _++_ : ℤ → ℤ → ℤ
-- [ a , b ] ++ [ x , y ] = [ a + x , b + y ]
-- ℤ≡ a⁺ a⁻ b⁺ b⁻ a≡b i ++ [ n⁺ , n⁻ ] = ℤ≡ (a⁺ + n⁺) (a⁻ + n⁻) (b⁺ + n⁺) (b⁻ + n⁻) (+rel a⁺ a⁻ b⁺ b⁻ n⁺ n⁻ n⁺ n⁻ a≡b ✓) i
-- [ n⁺ , n⁻ ] ++ ℤ≡ a⁺ a⁻ b⁺ b⁻ a≡b i = ℤ≡ (n⁺ + a⁺) (n⁻ + a⁻) (n⁺ + b⁺) (n⁻ + b⁻) (+rel n⁺ n⁻ n⁺ n⁻ a⁺ a⁻ b⁺ b⁻ ✓ a≡b) i
-- -- +rel : (a⁺ a⁻ b⁺ b⁻ x⁺ x⁻ y⁺ y⁻ : ℕ) → (a⁺ + b⁻ ≡ b⁺ + a⁻) → (x⁺ + y⁻ ≡ y⁺ + x⁻) → (a⁺ + x⁺) + (b⁻ + y⁻) ≡ (b⁺ + y⁺) + (a⁻ + x⁻)
-- -- ℤ≡ : (a⁺ a⁻ b⁺ b⁻ : ℕ) → (a⁺ + b⁻ ≡ b⁺ + a⁻) → [ a⁺ , a⁻ ] ≡ [ b⁺ , b⁻ ]
-- trunc a b p q i j ++ [ m , n ] = {!!} 
-- [ m , n ] ++ trunc a b p q i j = {!!}
-- trunc a b p q i j ++ trunc a' b' p' q' i' j' = {!!} 
     
-- i = i0 ⊢ ℤ≡ (a + a') (b + b') (a + x') (b + y')
--          (Math.Magma.go2 a b a' b' x' y' q j) j
-- i = i1 ⊢ ℤ≡ (x + a') (y + b') (x + x') (y + y')
--          (Math.Magma.go2 x y a' b' x' y' q j) j
-- j = i0 ⊢ ℤ≡ (a + a') (b + b') (x + a') (y + b')
--          (Math.Magma.go1 a b x y p i a' b') i
-- j = i1 ⊢ ℤ≡ (a + x') (b + y') (x + x') (y + y')
--          (Math.Magma.go1 a b x y p i x' y') i



  
module _ where
  open group?
  -- ℤgroup : group? ℤ _+_
  -- ℤgroup = ?

data Z : Type₀ where
  _⊝_ : ℕ → ℕ → Z
  cancel : ∀ x y → x ⊝ y ≡ s x ⊝ s y

infixl 6 _⊝_

question : ∀ x y i → cancel x y i ≡ cancel (s x) (s y) i
question x y i j =
  hcomp (λ k → λ{ (i = i0) → cancel x y j
                ; (i = i1) → cancel (s x) (s y) (j ∧ k)
                ; (j = i0) → cancel x y i
                ; (j = i1) → cancel (s x) (s y) (i ∧ k) })
        (cancel x y (i ∨ j))
-- (a + s b ≡ s a + b)
  -- ℤ≡ : (a b x y : ℕ) → (a + y ≡ x + b) → [ a , b ] ≡ [ x , y ]
-- q2 : ∀ a a' b b' x x' y y' p q i → ℤ≡ a b x y p i ≡ ℤ≡ (a + a') (b + b') (x + x') (y + y') q i
-- q2 a a' b b' x x' y y' p q i j = hcomp (λ k → λ { (i = i0) → ℤ≡ a b x y p j
--                                                 ; (i = i1) → ℤ≡ (a + a') (b + b') (x + x') (y + y') q (j ∧ k)
--                                                 ; (j = i0) → ℤ≡ a b x y p i
--                                                 ; (j = i1) → {!!}})
--                                        (ℤ≡ a b x y p (i ∨ j))

  -- ℤ≡ : (a b x y : ℕ) → (a + y ≡ x + b) → [ a , b ] ≡ [ x , y ]

cong₂ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : (x : A) → Type ℓ'} {x y} {C : (a : A) → (b : B a) → Type ℓ} →
        (f : (a : A) → (b : B a) → C a b) →
        (p : x ≡ y) →
        {u : B x} {v : B y} (q : (λ i → B (p i)) [ u ≡ v ] ) →
        (λ i → C (p i) (q i)) [ f x u ≡ f y v ]
cong₂ f p q i = f (p i) (q i)

lem₂ : ∀ a b c d i →
  cancel (a + s b) (c + s d) i ≡
  cancel (s a + b) (s c + d) i
lem₂ a b c d i j = cancel (+s a b j) (+s c d j) i

lem₁ : ∀ a b c d i → cancel (a + b) (c + d) i ≡ cancel (a + s b) (c + s d) i
lem₁ a b c d i = question (a + b) (c + d) i ∙ sym (lem₂ a b c d i)

_+ᶻ_ : Z → Z → Z
(x ⊝ x₁) +ᶻ (x₂ ⊝ x₃) = (x + x₂) ⊝ (x₁ + x₃)
cancel a c i +ᶻ (b ⊝ d) = lem₁ a b c d i i0
(a ⊝ c) +ᶻ cancel b d j = lem₁ a b c d i0 j
cancel a c i +ᶻ cancel b d j = lem₁ a b c d i j

infixl 6 _+ᶻ_

-- lem₃ : ∀ a b c d i j → lem₁ a b c d i j ≡ lem₁ b a d c j i
-- lem₃ a b c d i j k = {!!}

-- +ᶻ-comm : ∀ x y → x +ᶻ y ≡ y +ᶻ x
-- +ᶻ-comm (a ⊝ c) (b ⊝ d) = cong₂ _⊝_ (+comm a b) (+comm c d )
-- +ᶻ-comm (a ⊝ c) (cancel b d j) = lem₃ a b c d i0 j
-- +ᶻ-comm (cancel a c i) (b ⊝ d) = lem₃ a b c d i i0
-- +ᶻ-comm (cancel a c i) (cancel b d j) = lem₃ a b c d i j

