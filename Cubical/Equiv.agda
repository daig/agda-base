{-# OPTIONS --cubical --safe #-}
module Cubical.Equiv where
open import Type
open import Sigma
open import Eq
open import Cubical.Core
open import Iso


fiber [_]↣_ : {A : Type ℓa} {B : Type ℓb} (f : A → B) (y : B) → Type (ℓa ⊔ ℓb)
fiber {A = A} f y = Σ A λ x → f x ≡ y
[_]↣_ = fiber
contractible : Type ℓ → Type ℓ
contractible A = Σ A λ x → (y : A) → x ≡ y

private
  module Prim where
    record equiv {A : Type ℓa} {B : Type ℓb} (f : A → B) : Type (ℓa ⊔ ℓb) where
        field proof : ∀ y → contractible (fiber f y)
        -- field proof : ∀ y → Σ ([ f ]↣ y) λ x → ∀ x' → x ≡ x'
    infix 4 _≃_
    _≃_ : (A : Type ℓa) (B : Type ℓb) → Type (ℓa ⊔ ℓb)
    A ≃ B = Σ (A → B) λ f → equiv f
    --  A ≃ B = (f : A → B) , (y : B) → (x : A, f x ≡ y) , ∀ x' → x ≡ x'
    {-# BUILTIN EQUIV _≃_ #-}
    to : {A : Type ℓa} {B : Type ℓb} → A ≃ B → A → B
    to = π₁
    {-# BUILTIN EQUIVFUN to #-}
    proof : (A : Type ℓa) (B : Type ℓb) → (A≅B : A ≃ B) (let A→B = to A≅B)
        → (b : B) → ∀ φ → [ φ ⊢ [ A→B ]↣ b ] → [ A→B ]↣ b
    proof A B A≃B b φ u with A≃B .π₂ .equiv.proof b
    ... | c , p = hcomp (λ i → λ { (φ = i1) → p (u 1=1) i
                                ; (φ = i0) → c}) c
    {-# BUILTIN EQUIVPROOF proof #-}


module Equiv where
    open Prim public using (_≃_; to; proof)

    module id where
        equiv : (A : Type ℓ) → Prim.equiv (λ x → x)
        Prim.equiv.proof (equiv A) y = ( y , ✓ ) ,  contract where
            contract : (y⁻¹ : Σ A (λ x → x ≡ y)) → (y , ✓) ≡ y⁻¹
            contract (x , idx≡y ) i   = idx≡y (~ i) , λ j → idx≡y (~ i ∨ j)
    id : (A : Type ℓ) → A Prim.≃ A
    id A = (λ x → x) , id.equiv A
    open Prim public using (_≃_; equiv)

    toPathP : {A : I → Type ℓ} {x : A i0} {y : A i1}
            → transp (\ i → A i) i0 x ≡ y → A [ x ≡ y ]
    toPathP {A = A} {x = x} p i = hcomp (λ j → λ { (i = i0) → x
                                                    ; (i = i1) → p j })
                                        (transp (λ j → A (i ∧ j)) (~ i) x)
    -- Essential consequences of isProp and isContr
    isProp→PathP : ∀ {B : I → Type ℓ} → ((i : I) (x y : B i) → x ≡ y)
                → (b0 : B i0) (b1 : B i1)
                → B [ b0 ≡ b1 ]
    isProp→PathP hB b0 b1 = toPathP (hB _ _ _)
    isPropIsEquiv : {A B : Type ℓ} (f : A → B) (x y : equiv f) → x ≡ y
    equiv.proof (isPropIsEquiv f p q i) y =
        let p2 = p .equiv.proof y .π₂
            q2 = q .equiv.proof y .π₂
        in p2 (q .equiv.proof y .π₁) i
        , λ w j → hcomp (λ k → λ { (i = i0) → p2 w j
                                    ; (i = i1) → q2 w (j ∨ ~ k)
                                    ; (j = i0) → p2 (q2 w (~ k)) i
                                    ; (j = i1) → w })
                        (p2 w (i ∨ j))


    eq : {A B : Type ℓ} (e f : A ≃ B) → (h : e .π₁ ≡ f .π₁) → e ≡ f
    eq e f h = λ i → (h i) , isProp→PathP (λ i → isPropIsEquiv (h i)) (e .π₂) (f .π₂) i

    module _ {A : Type ℓa} {B : Type ℓb} (i : A ≅ B) where
        open _≅_ i renaming ( to to f; from to f⁻¹; to∘from to f∘f⁻¹; from∘to to f⁻¹∘f)
        ≅→≃ : equiv f
        ≅→≃ .equiv.proof y .π₁ = f⁻¹ y , f∘f⁻¹ y
        ≅→≃ .equiv.proof y .π₂ (x′ , fx′≡y) = lemIso where
            x = f⁻¹ y ; fx≡y = f∘f⁻¹ y
            ✓≡f⁻¹∘fx : (λ φ → f⁻¹ (fx≡y (~ φ)) ≡ hcomp (λ {j (φ = i0) → f⁻¹ y
                                                            ;j (φ = i1) → f⁻¹∘f x j})
                                                    (f⁻¹ (fx≡y (~ φ))))
                    [ ✓ {x = f⁻¹ y} ≡ f⁻¹∘f x ]
            ✓≡f⁻¹∘fx φ = hfill (λ k → λ { (φ = i0) → f⁻¹ y
                                        ; (φ = i1) → f⁻¹∘f x k})
                                (↦ f⁻¹ (fx≡y (~ φ)))
            -- ✓≡f⁻¹∘fx φ i = hcomp {φ = ~ i ∨ ~ φ ∨ φ}
            --                   (λ {j (i = i0) → f⁻¹ (fx≡y (~ φ))
            --                      ;j (φ = i0) → f⁻¹ y
            --                      ;j (φ = i1) → f⁻¹∘f x (i ∧ j)})
            --                   (f⁻¹ (fx≡y (~ φ)))
            f⁻¹y≡x  : f⁻¹ y ≡ x
            f⁻¹y≡x φ = ✓≡f⁻¹∘fx φ i1
            f⁻¹y≡f⁻¹fx : f⁻¹ y ≡ f⁻¹ (f x)
            f⁻¹y≡f⁻¹fx φ = ✓≡f⁻¹∘fx φ i0
            ✓≡f⁻¹∘fx′ : (λ φ → f⁻¹ (fx′≡y (~ φ)) ≡ hcomp (λ {j (φ = i0) → f⁻¹ y
                                                            ;j (φ = i1) → f⁻¹∘f x′ j})
                                                        (f⁻¹ (fx′≡y (~ φ))))
                    [ ✓ {x = f⁻¹ y} ≡ f⁻¹∘f x′ ]
            ✓≡f⁻¹∘fx′ zz i = hcomp {φ = ~ i ∨ ~ zz ∨ zz}
                                (λ {j (i = i0) → f⁻¹ (fx′≡y (~ zz))
                                    ;j (zz = i0) → f⁻¹ y
                                    ;j (zz = i1) → f⁻¹∘f x′ (i ∧ j)})
                                (f⁻¹ (fx′≡y (~ zz)))
            f⁻¹y≡x′ : f⁻¹ y ≡ x′
            f⁻¹y≡x′ φ = ✓≡f⁻¹∘fx′ φ i1
            f⁻¹y≡f⁻¹fx′ : f⁻¹ y ≡ f⁻¹ (f x′)
            f⁻¹y≡f⁻¹fx′ φ = ✓≡f⁻¹∘fx′ φ i0
            f⁻¹y≡x≣f⁻¹y≡x′ : (λ zz → f⁻¹ y ≡ hcomp (λ { j (zz = i0) → f⁻¹y≡x j
                                                        ; j (zz = i1) → f⁻¹y≡x′ j})
                                                    (f⁻¹ y))
                    [ f⁻¹y≡x ≡ f⁻¹y≡x′ ]                                        
            f⁻¹y≡x≣f⁻¹y≡x′ zz i = hcomp {φ = ~ i ∨ ~ zz ∨ zz}
                                (λ {j (i = i0) → f⁻¹ y
                                    ;j (zz = i0)
                                    → hcomp {φ = (i ∧ j) ∨ ~ i ∨ ~ j}
                                            (λ {k (i = i1) (j = i1) → f⁻¹∘f x k
                                                ;k (i = i0)          → f⁻¹ y
                                                ;k (j = i0)          → f⁻¹ y})
                                            (f⁻¹ (fx≡y (~ i ∨ ~ j)))
                                    ;j (zz = i1)
                                    → hcomp (λ {k (i = i1) (j = i1) → f⁻¹∘f x′ k
                                                ;k (i = i0)          → f⁻¹ y
                                                ;k (j = i0)          → f⁻¹ y})
                                            (f⁻¹ (fx′≡y (~ i ∨ ~ j))) })
                                (f⁻¹ y)

            x≡x′ : x ≡ x′
            x≡x′ i = f⁻¹y≡x≣f⁻¹y≡x′ i i1

            f⁻¹y≡f⁻¹fx≣f⁻¹y≡f⁻¹fx′ : (λ i → f⁻¹ y ≡  f⁻¹ (f (x≡x′ i)))
                                    [ f⁻¹y≡f⁻¹fx ≡ f⁻¹y≡f⁻¹fx′ ]
            f⁻¹y≡f⁻¹fx≣f⁻¹y≡f⁻¹fx′ i j = hcomp (λ k → λ { (i = i1) → ✓≡f⁻¹∘fx′ j (~ k)
                                    ; (i = i0) → ✓≡f⁻¹∘fx j (~ k)
                                    ; (j = i1) → f⁻¹∘f (x≡x′ i) (~ k)
                                    ; (j = i0) → f⁻¹ y })
                            (f⁻¹y≡x≣f⁻¹y≡x′ i j)

            fx≡y≣fx′≡y : (λ i → f (x≡x′ i) ≡ y)
                [ fx≡y ≡  fx′≡y  ]
            fx≡y≣fx′≡y i j = hcomp (λ k → λ { (i = i1) → f∘f⁻¹ (fx′≡y j) k
                                    ; (i = i0) → f∘f⁻¹ (fx≡y j) k
                                    ; (j = i0) → f∘f⁻¹ (f (x≡x′ i)) k
                                    ; (j = i1) → f∘f⁻¹ y k })
                            (f (f⁻¹y≡f⁻¹fx≣f⁻¹y≡f⁻¹fx′ i (~ j)))
            lemIso : (x , fx≡y) ≡ (x′ , fx′≡y)
            lemIso i .π₁ = x≡x′ i
            lemIso i .π₂ = fx≡y≣fx′≡y i

open Equiv public using (_≃_; equiv)

