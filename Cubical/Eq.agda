{-# OPTIONS --cubical --safe #-}
module Cubical.Eq where
open import Cubical.Core
open import Cubical.Core public using (_≡_)

private
  variable
    ℓ ℓa ℓb ℓc : Level
    A : Type ℓa
    B : Type ℓb
    a b x y : A

refl ✓ : x ≡ x
refl {x = x} _ = x
✓ = refl; {-# INLINE ✓ #-}

cong _⟨$⟩_ : (f : A → B) → x ≡ y → f x ≡ f y
cong f x≡y i = f (x≡y i)
_⟨$⟩_ = cong
_⟨&⟩_ : x ≡ y → (f : A → B) → f x ≡ f y
e ⟨&⟩ f = f ⟨$⟩ e
infix 5 _⟨&⟩_;  infixr 0 _⟨$⟩_
{-# INLINE cong #-} ; {-# INLINE _⟨$⟩_ #-} ; {-# INLINE _⟨&⟩_ #-}

sym : {P : I → Type ℓ} {x : P i0} {y : P i1}
  → P [ x ≡ y ] → (λ i → P (~ i)) [ y ≡ x ]
sym e i = e (~ i)



_∙∙_∙∙_ : a ≡ x → x ≡ y → y ≡ b → a ≡ b
-- (a≡x ∙∙ x≡y ∙∙ y≡b) i = hcomp (doubleComp-faces a≡x y≡b i) (x≡y i)
(a≡x ∙∙ x≡y ∙∙ y≡b) i = hcomp (λ{j (i = i0) → a≡x (~ j)
                                ;j (i = i1) → y≡b    j})
                        (x≡y i)
_≡⟨_⟩≡⟨_⟩_ : (a : A) → a ≡ x → x ≡ y → y ≡ b → a ≡ b
_ ≡⟨ a≡x ⟩≡⟨ x≡y ⟩ y≡b = a≡x ∙∙ x≡y ∙∙ y≡b

-- hfill : {A : Type ℓ} {φ : I} (u : ∀ i → [ φ ⊢ A ] ) (u0 : A [ φ ↦ u i0 ])
--         (i : I) → A
-- hfill {φ = φ} u u0 i =
--   hcomp (λ j → λ { (φ = i1) → u (i ∧ j) 1=1 ; (i = i0) → outS u0 }) (outS u0)

trans _⋯_ : a ≡ x → x ≡ b → a ≡ b
-- x≡y ∙ y≡z = refl ∙∙ x≡y ∙∙ y≡z
-- (x≡y ∙ y≡z) i = hcomp (doubleComp-faces refl y≡z i) (x≡y i)
trans {a = a} a≡x x≡b i = hcomp (λ{j (i = i0) → a ;j (i = i1) → x≡b j}) (a≡x i)
_⋯_ = trans; {-# INLINE _⋯_ #-} ; infixr 30 _⋯_

subst : {A : Type ℓ} {x y : A} (P : A → Type ℓ) → x ≡ y → P x → P y 
subst {A = A} P x≡y p = transp (λ i → P (x≡y i)) i0 p

-- https://homotopytypetheory.org/2011/04/10/just-kidding-understanding-identity-elimination-in-homotopy-type-theory/
J : {a : A} (P : (x : A) → a ≡ x → Type ℓ)
     (r : P a ✓)
     {b : A} (p : a ≡ b)
 → P b p
J P r a≡b = transp (λ i → P (a≡b i)  λ j → a≡b (j ∧ i)) i0 r


J′ : (C : (x y : A) → x ≡ y → Type ℓa)
     (r : (x : A) → C x x ✓)
     {a b : A} (p : a ≡ b)
  → C a b p
J′ C r {a = a} a≡b = J (C a) (r a) a≡b




module Reasoning where
    infix  3 _∎
    infixr 2 _≡⟨⟩_ _≡⟨_⟩_ _≡˘⟨_⟩_ _∴_ _∵_∴_
    infix  1 begin_
    begin_ : x ≡ y → x ≡ y
    begin_ x≡y = x≡y


    _≡⟨⟩_ _∴_ : ∀ x → x ≡ y → x ≡ y
    _ ≡⟨⟩ x≡y = x≡y
    _ ∴ x≡y = x≡y

    _≡⟨_⟩_ _∵_∴_ : (a : A) → a ≡ x → x ≡ b → a ≡ b
    _ ≡⟨ a≡x ⟩ x≡b = a≡x ⋯ x≡b
    _ ∵ a≡x ∴ x≡b = a≡x ⋯ x≡b
    _≡˘⟨_⟩_ : (a : A) → x ≡ b → x ≡ a → a ≡ b
    _ ≡˘⟨ x≡b ⟩ x≡a = sym x≡a ⋯ x≡b


    ≡⟨⟩-syntax : (a : A) → a ≡ x → x ≡ b → a ≡ b
    ≡⟨⟩-syntax = _≡⟨_⟩_
    infixr 2 ≡⟨⟩-syntax
    syntax ≡⟨⟩-syntax x (λ i → B) y = x ≡[ i ]⟨ B ⟩ y

    _∎ : (x : A) → x ≡ x
    _∎ _ = ✓
open Reasoning public

{- The most natural notion of homogenous path composition
    in a cubical setting is double composition:
       w ∙ ∙ ∙ > z
       ^         ^
 w≡x⁻¹ |         | y≡z      ^
       |         |        j |
       x — — — > y          ∙ — >
           x≡y                 i
   `w≡x ∙∙ x≡y ∙∙ y≡z` gives the line at the top,
   `doubleCompPath-filler w≡x x≡y y≡z` gives the whole square
-}

doubleComp-faces : {w x y z : A} (w≡x : w ≡ x) (y≡z : y ≡ z)
                 → (i j : I) → [ i ∨ ~ i ⊢ A ]
doubleComp-faces w≡x y≡z i j = λ{(i = i0) → w≡x (~ j)
                                ;(i = i1) → y≡z    j}

doubleCompPath-filler : (a≡x : a ≡ x) (x≡y : x ≡ y) (y≡b : y ≡ b)
                      → (λ j → a≡x (~ j) ≡ y≡b j) [ x≡y ≡ a≡x ∙∙ x≡y ∙∙ y≡b ]
doubleCompPath-filler w≡x x≡y y≡z j i
  = hfill (doubleComp-faces w≡x y≡z i) (↦ x≡y i) j
  -- = hfill (λ{k (i = i0) → w≡x (~ k)
  --           ;k (i = i1) → y≡z    k})
  --         (inS (x≡y i)) j
  -- = hcomp (λ k → λ { (i = i1) → y≡z (j ∧ k)
  --                   ; (j = i0) → x≡y i })
  --         (x≡y i)

{- For single homogenous path composition, we take `p = refl`:
     x ∙ ∙ ∙ > z
     ‖         ^
     ‖         | y≡z      ^
     ‖         |        j |
     x — — — > y          ∙ — >
        x≡y                 i
   `x≡y ∙ y≡z` gives the line at the top,
   `compPath-filler x≡y y≡z` gives the whole square
-}
