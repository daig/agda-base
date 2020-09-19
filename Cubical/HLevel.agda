{-# OPTIONS --no-import-sorts --cubical --safe #-}
module Cubical.HLevel where
open import Type
open import Eq 
open import Cubical.Core
open import Cubical.Equiv 
open import Nat
open import Sigma 
open import Fun.Extensionality 

-- Homotopy level
h? : ℕ → Type ℓ → Type ℓ
h? 0 A = ∃ \ (x : A) → ∀ y → x ≡ y
h? 1 A = (x y : A) → x ≡ y
h? (s (s n)) A = (x y : A) → h? (s n) (x ≡ y)

h?′ : ℕ → (B′ : A → Type ℓb) → Type _
h?′ {A = A} 0 B′ = {a : A} → Σ (B′ a) \ b → ({a' : A} → (b' : B′ a') (p : a ≡ a') → (λ i → B′ (p i)) [ b ≡ b' ])
h?′ {A = A} 1 B′ = {a₀ a₁ : A} (b₀ : B′ a₀) (b₁ : B′ a₁) (p : a₀ ≡ a₁) → (λ i → B′ (p i)) [ b₀ ≡ b₁ ]
h?′ {A = A} (s (s n)) B′ = {a₀ a₁ : A} (b₀ : B′ a₀) (b₁ : B′ a₁)
  → h?′ {A = a₀ ≡ a₁} (s n) (λ p → (λ i → B′ (p i)) [ b₀ ≡ b₁ ])

-- transport : A ≡ B → A → B
-- transport p a = transp (λ i → p i) i0 a

module _ {⊢A : I → Type ℓ} {x : ⊢A i0} {y : ⊢A i1} where
    open import Iso
    transp→≡ : transp ⊢A i0 x ≡ y → ⊢A [ x ≡ y ]
    transp→≡ p i = hcomp (λ {j (i = i0) → x
                       ;j (i = i1) → p j})
                    (transp (λ j → ⊢A (i ∧ j)) (~ i) x)
    ≡→transp : ⊢A [ x ≡ y ] → transp ⊢A i0 x ≡ y
    ≡→transp x≡y i = transp (λ j → ⊢A (i ∨ j)) i (x≡y i)
    -- ⊢≅≡ : (transp ⊢A i0 x ≡ y) ≅ (⊢A [ x ≡ y ])
    -- ⊢≅≡ = iso ⊢→≡ ≡→⊢ {!!} {!!} where


contr? prop? set? groupoid? 2groupoid? : Type ℓ → Type ℓ
contr?     = h? 0
prop?      = h? 1
set?       = h? 2
groupoid?  = h? 3
2groupoid? = h? 4

module HLevel where
    -- Equalities at all higher levels are also trivial
    suc : ∀ n → h? n A → h? (s n) A
    suc 0 (x , x≡) a b i = hcomp (λ j → λ {(i = i0) → x≡ a j
                                       ;(i = i1) → x≡ b j}) x
    suc 1 _≣_ a b p q j i = hcomp (λ k → λ {(i = i0) → (a ≣ a) k
                                       ;(i = i1) → (a ≣ b) k
                                       ;(j = i0) → (a ≣ p i) k
                                       ;(j = i1) → (a ≣ q i) k}) a
    suc (s (s n)) h a b = suc (s n) (h a b)

    plus : ∀ {n} m → h? n A → h? (m + n) A
    plus 0 h = h
    plus (s m) h = suc _ (plus m h)

    -- commutes with lambdas
    Π : ∀ n → ((x : A) → h? n (B′ x))
            → h? n ((x : A) → B′ x)
    Π 0 h = (λ x → π₁ (h x)) , λ f i y → π₂ (h y) (f y) i
    Π 1 h f g i x = (h x) (f x) (g x) i
    Π (s (s n)) h f g = subst (h? (s n)) fx≡gx≣f≡g (Π (s n) λ x → h x (f x) (g x))

    Π2 : ∀ n → (h : (x : A) (y : B′ x) → h? n (C′ x y))
            → h? n ((x : A) (y : B′ x) → C′ x y)
    Π2 n h = Π n \ x → Π n \ y → h x y

    Π3 : ∀ n → (h : (x : A) (y : B′ x) (z : C′ x y) → h? n (D′ x y z))
            → h? n ((x : A) (y : B′ x) → (z : C′ x y) → D′ x y z)
    Π3 n h = Π n \ x → Π n \ y → Π n \ z → h x y z

    Π4 : ∀ n → (h : (x : A) (y : B′ x) (z : C′ x y) → (w : D′ x y z) → h? n (E′ x y z w))
            → h? n ((x : A) (y : B′ x) → (z : C′ x y) → (w : D′ x y z) → E′ x y z w)
    Π4 n h = Π n \ x → Π n \ y → Π n \ z → Π n \ w → h x y z w


    Π⁻ : ∀ n → h? n (A → B) → (A → h? n B)
    Π⁻ 0 h x = π₁ h x , λ y →  f≡g→fx≡gx (π₂ h (λ _ → y)) x
    Π⁻ 1 h x y z = f≡g→fx≡gx (h (λ _ → y) (λ _ → z)) x
    Π⁻ (s (s n)) h x y z = Π⁻ (s n) (subst (h? (s n)) (sym fx≡gx≣f≡g) (h (λ _ → y) (λ _ → z))) x
    -- module _ where
    --     open import Iso
    --     Π≅ : ∀ n → (A → h? n B) ≅ h? n (A → B)
    --     Π≅ {A = A} {B = B} n = iso (Π n) (Π⁻ n) {!!} {!!} where
    prop : ∀ n → prop? (h? n A)
    prop 0 (_ , x≡) (y , y≡) j
      = (x≡ y j)
      , λ y' i → hcomp (λ k →
                             λ { (i = i0) → x≡ y j
                               ; (i = i1) → x≡ y' (j ∨ k)
                               ; (j = i0) → x≡ y' (i ∧ k)
                               ; (j = i1) → y≡ y' i
                               })
                       (x≡ (y≡ y' i) j)
    prop 1 f g i a b = suc 1 f a b (f a b) (g a b) i
    prop (s (s n)) f g i a b = prop (s n) (f a b) (g a b) i

module HProp where
    Π : ((x : A) → prop? (B′ x))
      → prop? ((x : A) → B′ x)
    Π = HLevel.Π 1
    ⦃Π⦄ : ((x : A) → prop? (B′ x))
        → prop? ({x : A} → B′ x)
    ⦃Π⦄ h f g i {x} = h x (f {x}) (g {x}) i
module HSet where
    Π : ((x : A) → set? (B′ x))
      → set? ((x : A) → B′ x)
    Π = HLevel.Π 2
    prop : prop? (set? A)
    prop = HLevel.prop 2

-- Essential consequences of isProp and isContr
⊢prop→≡ : ((i : I) → prop? (⊢B i))
       → (b0 : ⊢B i0) (b1 : ⊢B i1)
       → ⊢B [ b0 ≡ b1 ]
⊢prop→≡ {⊢B = ⊢B} ⊢h b0 b1 = transp→≡ (⊢h i1 (transp ⊢B i0 b0) b1)
                    

h?→h?′ : (n : ℕ) (h : (a : A) → h? n (B′ a)) → h?′ {A = A} n B′
h?→h?′ 0 h {a} = (π₁ (h a)) , λ b' p → ⊢prop→≡ (λ i → HLevel.suc 0 (h (p i))) (h a .π₁) b'
h?→h?′ 1 h = λ b₀ b₁ p → ⊢prop→≡ (λ i → h (p i)) b₀ b₁
h?→h?′ {A = A} {B′ = B′} (s (s n)) h {a₀} {a₁} b₀ b₁ = h?→h?′ (s n) (helper a₁ b₁)
  where helper : (a₁ : A) (b₁ : B′ a₁) (p : a₀ ≡ a₁ )
               → h? (s n) ((λ i → B′ (p i)) [ b₀ ≡ b₁ ])
        helper a₁ b₁ a₀≡a₁
          = J (λ a₁ a₀≡a₁ → ∀ b₁ → h? (s n) ((λ i → B′ (a₀≡a₁ i)) [ b₀ ≡ b₁ ]))
                        (λ _ → h _ _ _)  a₀≡a₁ b₁
hfun? : (n : ℕ) (f : A → B) → Type _
hfun? n f = ∀ b → h? n ([ f ]↣ b)
