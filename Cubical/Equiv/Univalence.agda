{-# OPTIONS --cubical --safe #-}
module Cubical.Equiv.Univalence where
open import Cubical.Core
open import Eq
open import Fun
open import Cubical.Equiv
open import Iso
open import Sigma
open import Cubical.Glue


≃→≡ : A ≃ B → A ≡ B
≃→≡ {A = A} {B = B} e i = Glue B (λ {(i = i0) → (A , e)
                                    ;(i = i1) → (B , Equiv.id B) })
                                   
-- isContr→isProp : {A : Type ℓ} → contractible A → (x y : A) → x ≡ y
-- isContr→isProp (x , p) a b i =
--     hcomp (λ j → λ { (i = i0) → p a j
--                     ; (i = i1) → p b j }) x

-- module _ {ℓ : I → Level} (P : (i : I) → Type (ℓ i)) where
--   private
--     ~P : (i : I) → Type (ℓ (~ i))
--     ~P i = P (~ i)

--     X = P i0; Y = P i1

--     f : X → Y
--     f x = transp P i0 x

--     f⁻¹ : Y → X
--     f⁻¹ y = transp ~P i0 y

--     u : ∀ i → X → P i
--     u i x = transp (λ j → P (i ∧ j)) (~ i) x

--     v : ∀ i → Y → P i
--     v i y = transp (λ j → ~P ( ~ i ∧ j)) i y

--     fiberPath : (y : Y) → (xβ0 xβ1 : [ f ]↣ y) → xβ0 ≡ xβ1
--     fiberPath y (x0 , β0) (x1 , β1) k = ω , λ j → δ (~ j) where
--       module _ (j : I) where
--         private
--           sys : X → ∀ i → [ (~ j ∨ j) ⊩ (λ _ → P (~ i)) ]
--           sys x i = λ { (j = i0) → v (~ i) y
--                       ; (j = i1) → u (~ i) x}
--         ω0 = comp ~P (sys x0) ((β0 (~ j)))
--         ω1 = comp ~P (sys x1) ((β1 (~ j)))
--         θ0 = fill ~P (sys x0) (↦ β0 (~ j))
--         θ1 = fill ~P (sys x1) (↦ β1 (~ j))
--       sys = λ {j (k = i0) → ω0 j ; j (k = i1) → ω1 j}
--       ω = hcomp sys (f⁻¹ y)
--       θ = hfill sys (↦ f⁻¹ y)
--       δ = λ (j : I) → comp P
--             (λ i → λ { (j = i0) → v i y ; (k = i0) → θ0 j (~ i)
--                      ; (j = i1) → u i ω ; (k = i1) → θ1 j (~ i) })
--              (θ j)

--     γ : (y : Y) → y ≡ f (f⁻¹ y)
--     γ y j = comp P (λ i → λ { (j = i0) → v i y
--                              ; (j = i1) → u i (f⁻¹ y) }) (f⁻¹ y)

--   ≡→equiv : equiv f
--   ≡→equiv .equiv.proof y = (f⁻¹ y , sym (γ y)) , fiberPath y _

--   ≡→≃' : X ≃ Y
--   ≡→≃' = f , ≡→equiv
-- ≡→≃ : {X Y : Type ℓ} → X ≡ Y → X ≃ Y
-- ≡→≃ e =  ≡→≃' (λ i → e i)

-- -- The identity equivalence
-- -- idIsEquiv : ∀ {ℓ} (A : Type ℓ) → equiv A
-- -- equiv.proof (idIsEquiv A) y =
-- --   ((y , ✓) , λ z i → z .π₂ (~ i) , λ j → z .π₂ (~ i ∨ j))

-- equivCtr : {A B : Type ℓ} (e : A ≃ B) (y : B) → [ Equiv.to e ]↣ y
-- equivCtr e y = e .π₂ .equiv.proof y .π₁


-- equivCtrPath : {A B : Type ℓ} (e : A ≃ B) (y : B) →
--   (v : fiber (Equiv.to e) y) → equivCtr e y ≡ v
-- equivCtrPath e y = e .π₂ .equiv.proof y .π₂

-- -- unglue is an equivalence
-- unglueIsEquiv : ∀ (A : Type ℓ) (φ : I)
--                 (f : [ φ ⊩ (λ o → Σ (Type ℓ) \ T →  T ≃ A) ] ) →
--                 equiv {A = Glue A f} (unglue φ)
-- equiv.proof (unglueIsEquiv A φ f) = λ (b : A) →
--   let u : I → [ φ ⊢ A ]
--       u i = λ{ (φ = i1) → equivCtr (f 1=1 .π₂) b .π₂ (~ i) }
--       ctr : fiber (unglue φ) b
--       ctr = ( glue (λ { (φ = i1) → equivCtr (f 1=1 .π₂) b .π₁ }) (hcomp u b)
--             , λ j → hfill u (↦ b) (~ j))
--   in ( ctr
--      , λ (v : fiber (unglue φ) b) i →
--          let u' : I → [ φ ∨ ~ i ∨ i ⊢ A ]
--              u' j = λ { (φ = i1) → equivCtrPath (f 1=1 .π₂) b v i .π₂ (~ j)
--                       ; (i = i0) → hfill u (↦ b) j
--                       ; (i = i1) → v .π₂ (~ j) }
--          in ( glue (λ { (φ = i1) → equivCtrPath (f 1=1 .π₂) b v i .π₁ }) (hcomp u' b)
--             , λ j → hfill u' (↦ b) (~ j)))
-- -- Any partial family of equivalences can be extended to a total one
-- -- from Glue [ φ ↦ (T,f) ] A to A
-- unglueEquiv : ∀ (A : Type ℓ) (φ : I)
--               (f : [ φ ⊩ (λ o → Σ (Type ℓ) \ T → T ≃ A) ] ) →
--               (Glue A f) ≃ A
-- unglueEquiv A φ f = ( unglue φ , unglueIsEquiv A φ f )

-- EquivContr : ∀ (A : Type ℓ) → contractible (Σ (Type ℓ) \ T → T ≃ A)
-- EquivContr {ℓ = ℓ} A =
--   ( (A , Equiv.id A)
--   , idEquiv≡ )
--  where
--   idEquiv≡ : (y : Σ (Type ℓ) (λ T → T ≃ A)) → (A , Equiv.id A) ≡ y
--   idEquiv≡ w = \ { i .π₁                   → Glue A (f i)
--                  ; i .π₂ .π₁              → unglueEquiv _ _ (f i) .π₁
--                  ; i .π₂ .π₂ .equiv.proof → unglueEquiv _ _ (f i) .π₂ .equiv.proof
--                  }
--     where
--       f : ∀ i → [ (~ i ∨ i) ⊩ (λ x → Σ (Type ℓ) \ T →  T ≃ A) ]
--       f i = λ { (i = i0) → A , Equiv.id A ; (i = i1) → w }



-- -- Univalence
-- contrSinglEquiv : {A B : Type ℓ} (e : A ≃ B) → (B , Equiv.id B) ≡ (A , e)
-- contrSinglEquiv {A = A} {B = B} e =
--     isContr→isProp (EquivContr B) (B , Equiv.id B) (A , e)

-- private variable ℓ' : Level
-- -- Equiv induction
-- -- EquivJ : {A B : Type ℓ} (P : (A : Type ℓ) → (e : A ≃ B) → Type ℓ')
-- --        → (r : P B (Equiv.id B)) → (e : A ≃ B) → P A e
-- -- EquivJ P r e = subst (λ x → P (x .π₁) (x .π₂)) (contrSinglEquiv e) r

-- pathToEquivRefl : {A : Type ℓ} → ≡→≃ ✓ ≡ Equiv.id A
-- pathToEquivRefl {A = A} = Equiv.eq _ _ (λ i x → transp (λ _ → A) i x)

-- -- ≃≅≡ : {A B : Type ℓ} → (A ≃ B) ≅ (A ≡ B)
-- -- ≃≅≡ {A = A} {B = B} = record { to = ≃→≡ ; from = ≡→≃ ; to∘from = ≃→≡∘≡→≃ ; from∘to = {!!} } where
-- --     uaIdEquiv : {A : Type ℓ} → ≃→≡ (Equiv.id A) ≡ ✓
-- --     uaIdEquiv {A = A} i j = Glue A {φ = i ∨ ~ j ∨ j} (λ _ → A , Equiv.id A)
-- --     ≃→≡∘≡→≃ : ∀ (A≡B : A ≡ B) → ≃→≡ (≡→≃ A≡B) ≡ A≡B
-- --     ≃→≡∘≡→≃ = J (λ _ p → ≃→≡ (≡→≃ p) ≡ p) (cong ≃→≡ pathToEquivRefl ⋯ uaIdEquiv)
-- --     -- Equiv induction
-- --     ≡→≃∘≃→≡ : ∀ (A≃B : A ≃ B) → ≡→≃ (≃→≡ A≃B) ≡ A≃B
-- --     ≡→≃∘≃→≡  = EquivJ (λ _ f → ≡→≃ (≃→≡ f) ≡ f)
-- --                          (subst (λ r → ≡→≃ r ≡ Equiv.id _) (sym uaIdEquiv) (pathToEquivRefl {B = B}))


    
-- -- module _ (i : iso A B) where
-- --   open iso i renaming ( to to f; from to f⁻¹; to∘from to f∘f⁻¹; from∘to to f⁻¹∘f)

-- --   private
-- --     module _ (y : B) (x x' : A) (fx≡y : f x ≡ y) (fx'≡y : f x' ≡ y) where
-- --       fill0 : I → I → A
-- --       fill0 i = hfill (λ k → λ { (i = i1) → f⁻¹∘f x k
-- --                                ; (i = i0) → f⁻¹ y })
-- --                       (inS (f⁻¹ (fx≡y (~ i))))

-- --       fill1 : I → I → A
-- --       fill1 i = hfill (λ k → λ { (i = i1) → f⁻¹∘f x' k
-- --                                ; (i = i0) → f⁻¹ y })
-- --                       (inS (f⁻¹ (fx'≡y (~ i))))

-- --       fill2 : I → I → A
-- --       fill2 i = hfill (λ k → λ { (i = i1) → fill1 k i1
-- --                                ; (i = i0) → fill0 k i1 })
-- --                       (inS (f⁻¹ y))

-- --       p : x ≡ x'
-- --       p i = fill2 i i1

-- --       sq : I → I → A
-- --       sq i j = hcomp (λ k → λ { (i = i1) → fill1 j (~ k)
-- --                               ; (i = i0) → fill0 j (~ k)
-- --                               ; (j = i1) → f⁻¹∘f (fill2 i i1) (~ k)
-- --                               ; (j = i0) → f⁻¹ y })
-- --                      (fill2 i j)

-- --       sq1 : I → I → B
-- --       sq1 i j = hcomp (λ k → λ { (i = i1) → f∘f⁻¹ (fx'≡y (~ j)) k
-- --                                ; (i = i0) → f∘f⁻¹ (fx≡y (~ j)) k
-- --                                ; (j = i1) → f∘f⁻¹ (f (p i)) k
-- --                                ; (j = i0) → f∘f⁻¹ y k })
-- --                       (f (sq i j))

-- --       lemIso : (x , fx≡y) ≡ (x' , fx'≡y)
-- --       lemIso i .π₁ = p i
-- --       lemIso i .π₂ = λ j → sq1 i (~ j)

-- --   isoToIsEquiv : equiv? f
-- --   isoToIsEquiv .equiv?.proof y .π₁ .π₁ = f⁻¹ y
-- --   isoToIsEquiv .equiv?.proof y .π₁ .π₂ = f∘f⁻¹ y
-- --   isoToIsEquiv .equiv?.proof y .π₂ (x' , fx'≡y) = lemIso y (f⁻¹ y) x' (f∘f⁻¹ y) fx'≡y


-- -- -- hcomp : {A : Type ℓ} {φ : I} (u : I → [ φ ⊢ A ] ) (a : A) → A
-- -- -- hhfill : {φ : I} (u : I → [ φ ⊢ A ]) (u0 : A [ φ ↦ u i0 ]) (i : I) → A
-- -- -- hhfill {φ = φ} u u0 i =
-- -- -- hcomp (λ j → λ { (φ = i1) → u (i ∧ j) 1=1 ; (i = i0) → outS u0 }) (outS u0)
-- -- -- -- comp : (A : ∀ i → Type (ℓ′ i))
-- -- --        {φ : I}
-- -- --        (u : ∀ i → [ φ ⊢ A i ] )
-- -- --        (u0 : A i0 [ φ ↦ u i0 ]) → A i1
