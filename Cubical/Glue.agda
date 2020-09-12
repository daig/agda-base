{-# OPTIONS --cubical --prop --no-import-sorts #-}
module Cubical.Glue where
open import Cubical.Core
open import Cubical.Eq
open import Fun

private _∙_ = trans

private
  variable
    ℓ ℓa ℓb ℓc : Level

fiber [_]↣_ : {A : Type ℓa} {B : Type ℓb} (f : A → B) (y : B) → Type (ℓa ⊔ ℓb)
fiber {A = A} f y = Σ A λ x → f x ≡ y
[_]↣_ = fiber
contractible : Type ℓ → Type ℓ
contractible A = Σ A λ x → (y : A) → x ≡ y

module Equiv where


    record equiv {A : Type ℓa} {B : Type ℓb} (f : A → B) : Type (ℓa ⊔ ℓb) where
        field proof : ∀ y → Σ ([ f ]↣ y) λ x → ∀ x' → x ≡ x'

    infix 4 _≃_
    _≃_ : (A : Type ℓa) (B : Type ℓb) → Type (ℓa ⊔ ℓb)
    A ≃ B = Σ (A → B) λ f → equiv f
    --  A ≃ B = (f : A → B) , (y : B) → (x : A, f x ≡ y) , ∀ x' → x ≡ x'
    {-# BUILTIN EQUIV _≃_ #-}
    ≃to : {A : Type ℓa} {B : Type ℓb} → A ≃ B → A → B
    ≃to = π₁
    {-# BUILTIN EQUIVFUN ≃to #-}
    ≃proof : (A : Type ℓa) (B : Type ℓb) → (A≅B : A ≃ B) (let A→B = ≃to A≅B)
        → (b : B) → ∀ φ → [ φ ⊢ [ A→B ]↣ b ] → [ A→B ]↣ b
    ≃proof A B A≃B b φ u with A≃B .π₂ .equiv.proof b
    ... | c , p = hcomp (λ i → λ { (φ = i1) → p (u 1=1) i
                                ; (φ = i0) → c}) c
    {-# BUILTIN EQUIVPROOF ≃proof #-}

    idIsEquiv : (A : Type ℓ) → equiv (λ x → x)
    equiv.proof (idIsEquiv A) y = ( y , ✓ ) ,  contract where
        contract : (y⁻¹ : Σ A (λ x → x ≡ y)) → (y , ✓) ≡ y⁻¹
        contract (x , idx≡y ) i   = idx≡y (~ i) , λ j → idx≡y (~ i ∨ j)
    id : (A : Type ℓ) → A ≃ A
    id A = (λ x → x) , idIsEquiv A

    toPathP : {A : I → Type ℓ} {x : A i0} {y : A i1}
            → transp (\ i → A i) i0 x ≡ y → A [ x ≡ y ]
    toPathP {A = A} {x = x} p i = hcomp (λ j → λ { (i = i0) → x
                                                  ; (i = i1) → p j })
                                        (transp (λ j → A (i ∧ j)) (~ i) x)
    -- Essential consequences of isProp and isContr
    isProp→PathP : ∀ {B : I → Type ℓ} → ((i : I) (x y : B i) → x ≡ y)
                → (b0 : B i0) (b1 : B i1)
                → (λ i → B i) [ b0 ≡ b1 ]
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

isContr→isProp : {A : Type ℓ} → contractible A → (x y : A) → x ≡ y
isContr→isProp (x , p) a b i =
    hcomp (λ j → λ { (i = i0) → p a j
                    ; (i = i1) → p b j }) x


open Equiv public using (_≃_; equiv)

module primGlue where
    primitive
        primGlue    : ∀ {ℓ ℓ'} (A : Type ℓ) {φ : I}
            → (T : [ φ ⊢ Type ℓ' ] )
               (e : [ φ ⊩ (λ i → T i ≃ A) ] )
            → Type ℓ'
        prim^glue   : ∀ {ℓ ℓ'} {A : Type ℓ} {φ : I}
            → {T : [ φ ⊢ Type ℓ' ]}
               {e : [ φ ⊩ (λ o → T o ≃ A) ]}
               (t : [ φ ⊩ T ]) → (a : A)
            → primGlue A T e
        prim^unglue : ∀ {ℓ ℓ'} {A : Type ℓ} {φ : I}
            → {T : [ φ ⊢ Type ℓ' ]}
               {e : [ φ ⊩ (λ o → T o ≃ A) ]}
            → primGlue A T e → A


        -- Needed for transp in Glue.
        primFaceForall : (I → I) → I
    Glue : ∀ {ℓ ℓ'} (A : Type ℓ) {φ} → (Te : [ φ ⊢ (∃ \ T → T ≃ A) ]) → Type ℓ'
    Glue A Te = primGlue A (λ x → Te x .π₁) (λ x → Te x .π₂)
    unglue : ∀ {ℓ ℓ'} {A : Type ℓ}
            (φ : I) {T : [ φ ⊢ Type ℓ' ]}
            {e : [ φ ⊩ (λ o → T o ≃ A) ]} → Glue A (λ i → T i , e i) → A
    unglue φ {e = e} = prim^unglue {φ = φ}
open primGlue public using (Glue ; unglue) renaming (prim^glue to glue)

module _ {ℓ : I → Level} (P : (i : I) → Type (ℓ i)) where
  private
    ~P : (i : I) → Type (ℓ (~ i))
    ~P i = P (~ i)

    A = P i0; B = P i1

    f : A → B
    f x = transp P i0 x

    f⁻¹ : B → A
    f⁻¹ y = transp ~P i0 y

    u : ∀ i → A → P i
    u i x = transp (λ j → P (i ∧ j)) (~ i) x

    v : ∀ i → B → P i
    v i y = transp (λ j → ~P ( ~ i ∧ j)) i y

    fiberPath : (y : B) → (xβ0 xβ1 : [ f ]↣ y) → xβ0 ≡ xβ1
    fiberPath y (x0 , β0) (x1 , β1) k = ω , λ j → δ (~ j) where
      module _ (j : I) where
        private
          sys : A → ∀ i → [ (~ j ∨ j) ⊩ (λ _ → P (~ i)) ]
          sys x i (j = i0) = v (~ i) y
          sys x i (j = i1) = u (~ i) x
        ω0 = comp ~P (sys x0) ((β0 (~ j)))
        ω1 = comp ~P (sys x1) ((β1 (~ j)))
        θ0 = fill ~P (sys x0) (↦ β0 (~ j))
        θ1 = fill ~P (sys x1) (↦ β1 (~ j))
      sys = λ {j (k = i0) → ω0 j ; j (k = i1) → ω1 j}
      ω = hcomp sys (f⁻¹ y)
      θ = hfill sys (↦ f⁻¹ y)
      δ = λ (j : I) → comp P
            (λ i → λ { (j = i0) → v i y ; (k = i0) → θ0 j (~ i)
                     ; (j = i1) → u i ω ; (k = i1) → θ1 j (~ i) })
             (θ j)

    γ : (y : B) → y ≡ f (f⁻¹ y)
    γ y j = comp P (λ i → λ { (j = i0) → v i y
                             ; (j = i1) → u i (f⁻¹ y) }) (f⁻¹ y)

  ≡→equiv : equiv f
  ≡→equiv .equiv.proof y = (f⁻¹ y , sym (γ y)) , fiberPath y _

  ≡→≃' : A ≃ B
  ≡→≃' = f , ≡→equiv
≡→≃ : {A B : Type ℓ} → A ≡ B → A ≃ B
≡→≃ e =  ≡→≃' (λ i → e i)

-- The identity equivalence
-- idIsEquiv : ∀ {ℓ} (A : Type ℓ) → equiv A
-- equiv.proof (idIsEquiv A) y =
--   ((y , ✓) , λ z i → z .π₂ (~ i) , λ j → z .π₂ (~ i ∨ j))

equivCtr : {A B : Type ℓ} (e : A ≃ B) (y : B) → fiber (Equiv.≃to e) y
equivCtr e y = e .π₂ .equiv.proof y .π₁


equivCtrPath : {A B : Type ℓ} (e : A ≃ B) (y : B) →
  (v : fiber (Equiv.≃to e) y) → Path _ (equivCtr e y) v
equivCtrPath e y = e .π₂ .equiv.proof y .π₂

-- unglue is an equivalence
unglueIsEquiv : ∀ (A : Type ℓ) (φ : I)
                (f : [ φ ⊩ (λ o → Σ (Type ℓ) \ T →  T ≃ A) ] ) →
                equiv {A = Glue A f} (unglue φ)
equiv.proof (unglueIsEquiv A φ f) = λ (b : A) →
  let u : I → [ φ ⊢ A ]
      u i = λ{ (φ = i1) → equivCtr (f 1=1 .π₂) b .π₂ (~ i) }
      ctr : fiber (unglue φ) b
      ctr = ( glue (λ { (φ = i1) → equivCtr (f 1=1 .π₂) b .π₁ }) (hcomp u b)
            , λ j → hfill u (↦ b) (~ j))
  in ( ctr
     , λ (v : fiber (unglue φ) b) i →
         let u' : I → [ φ ∨ ~ i ∨ i ⊢ A ]
             u' j = λ { (φ = i1) → equivCtrPath (f 1=1 .π₂) b v i .π₂ (~ j)
                      ; (i = i0) → hfill u (↦ b) j
                      ; (i = i1) → v .π₂ (~ j) }
         in ( glue (λ { (φ = i1) → equivCtrPath (f 1=1 .π₂) b v i .π₁ }) (hcomp u' b)
            , λ j → hfill u' (↦ b) (~ j)))
-- Any partial family of equivalences can be extended to a total one
-- from Glue [ φ ↦ (T,f) ] A to A
unglueEquiv : ∀ (A : Type ℓ) (φ : I)
              (f : [ φ ⊩ (λ o → Σ (Type ℓ) \ T → T ≃ A) ] ) →
              (Glue A f) ≃ A
unglueEquiv A φ f = ( unglue φ , unglueIsEquiv A φ f )

EquivContr : ∀ (A : Type ℓ) → contractible (Σ (Type ℓ) \ T → T ≃ A)
EquivContr {ℓ = ℓ} A =
  ( (A , Equiv.id A)
  , idEquiv≡ )
 where
  idEquiv≡ : (y : Σ (Type ℓ) (λ T → T ≃ A)) → (A , Equiv.id A) ≡ y
  idEquiv≡ w = \ { i .π₁                   → Glue A (f i)
                 ; i .π₂ .π₁              → unglueEquiv _ _ (f i) .π₁
                 ; i .π₂ .π₂ .equiv.proof → unglueEquiv _ _ (f i) .π₂ .equiv.proof
                 }
    where
      f : ∀ i → [ (~ i ∨ i) ⊩ (λ x → Σ (Type ℓ) \ T →  T ≃ A) ]
      f i = λ { (i = i0) → A , Equiv.id A ; (i = i1) → w }



≃→≡ : {A B : Type ℓ} → A ≃ B → A ≡ B
≃→≡ {A = A} {B = B} e i = Glue B (λ {(i = i0) → (A , e)
                                     ;(i = i1) → (B , Equiv.id B) })


record _≅_ (A : Type ℓa) (B : Type ℓb) : Type (ℓa ⊔ ℓb) where
  field
    to : A → B
    from : B → A
    to∘from : ∀ b → to (from b) ≡ b
    from∘to : ∀ a → from (to a) ≡ a
≃≅≡ : {A B : Type ℓ} → (A ≃ B) ≅ (A ≡ B)
≃≅≡ {A = A} {B = B} = record { to = ≃→≡ ; from = ≡→≃ ; to∘from = ≃→≡∘≡→≃ ; from∘to = {!!} } where
    pathToEquivRefl : {A : Type ℓ} → ≡→≃ ✓ ≡ Equiv.id A
    pathToEquivRefl {A = A} = Equiv.eq _ _ (λ i x → transp (λ _ → A) i x)
    uaIdEquiv : {A : Type ℓ} → ≃→≡ (Equiv.id A) ≡ ✓
    uaIdEquiv {A = A} i j = Glue A {φ = i ∨ ~ j ∨ j} (λ _ → A , Equiv.id A)
    ≃→≡∘≡→≃ : ∀ (A≡B : A ≡ B) → ≃→≡ (≡→≃ A≡B) ≡ A≡B
    ≃→≡∘≡→≃ = J (λ _ p → ≃→≡ (≡→≃ p) ≡ p) (cong ≃→≡ pathToEquivRefl ∙ uaIdEquiv)
    contrSinglEquiv : {A B : Type ℓ} (e : A ≃ B) → (B , Equiv.id B) ≡ (A , e)
    contrSinglEquiv {A = A} {B = B} e =
        isContr→isProp (EquivContr B) (B , Equiv.id B) (A , e)
    -- Equivalence induction
    EquivJ : {ℓ ℓ' : Level} {A B : Type ℓ} (P : (A : Type ℓ) → (e : A ≃ B) → Type ℓ')
        → (r : P B (Equiv.id B)) → (e : A ≃ B) → P A e
    EquivJ P r e = subst (λ x → P (x .π₁) (x .π₂)) (contrSinglEquiv e) r
    ≡→≃∘≃→≡ : ∀ (A≃B : A ≃ B) → ≡→≃ (≃→≡ A≃B) ≡ A≃B
    ≡→≃∘≃→≡ {B = B} = EquivJ (λ _ f → ≡→≃ (≃→≡ f) ≡ f)
                         (subst (λ r → ≡→≃ r ≡ Equiv.id _) (sym uaIdEquiv) (pathToEquivRefl {B = B}))


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

    
-- module _ (i : iso A B) where
--   open iso i renaming ( to to f; from to f⁻¹; to∘from to f∘f⁻¹; from∘to to f⁻¹∘f)

--   private
--     module _ (y : B) (x x' : A) (fx≡y : f x ≡ y) (fx'≡y : f x' ≡ y) where
--       fill0 : I → I → A
--       fill0 i = hfill (λ k → λ { (i = i1) → f⁻¹∘f x k
--                                ; (i = i0) → f⁻¹ y })
--                       (inS (f⁻¹ (fx≡y (~ i))))

--       fill1 : I → I → A
--       fill1 i = hfill (λ k → λ { (i = i1) → f⁻¹∘f x' k
--                                ; (i = i0) → f⁻¹ y })
--                       (inS (f⁻¹ (fx'≡y (~ i))))

--       fill2 : I → I → A
--       fill2 i = hfill (λ k → λ { (i = i1) → fill1 k i1
--                                ; (i = i0) → fill0 k i1 })
--                       (inS (f⁻¹ y))

--       p : x ≡ x'
--       p i = fill2 i i1

--       sq : I → I → A
--       sq i j = hcomp (λ k → λ { (i = i1) → fill1 j (~ k)
--                               ; (i = i0) → fill0 j (~ k)
--                               ; (j = i1) → f⁻¹∘f (fill2 i i1) (~ k)
--                               ; (j = i0) → f⁻¹ y })
--                      (fill2 i j)

--       sq1 : I → I → B
--       sq1 i j = hcomp (λ k → λ { (i = i1) → f∘f⁻¹ (fx'≡y (~ j)) k
--                                ; (i = i0) → f∘f⁻¹ (fx≡y (~ j)) k
--                                ; (j = i1) → f∘f⁻¹ (f (p i)) k
--                                ; (j = i0) → f∘f⁻¹ y k })
--                       (f (sq i j))

--       lemIso : (x , fx≡y) ≡ (x' , fx'≡y)
--       lemIso i .π₁ = p i
--       lemIso i .π₂ = λ j → sq1 i (~ j)

--   isoToIsEquiv : equiv? f
--   isoToIsEquiv .equiv?.proof y .π₁ .π₁ = f⁻¹ y
--   isoToIsEquiv .equiv?.proof y .π₁ .π₂ = f∘f⁻¹ y
--   isoToIsEquiv .equiv?.proof y .π₂ (x' , fx'≡y) = lemIso y (f⁻¹ y) x' (f∘f⁻¹ y) fx'≡y


-- -- hcomp : {A : Type ℓ} {φ : I} (u : I → [ φ ⊢ A ] ) (a : A) → A
-- -- hhfill : {φ : I} (u : I → [ φ ⊢ A ]) (u0 : A [ φ ↦ u i0 ]) (i : I) → A
-- -- hhfill {φ = φ} u u0 i =
-- -- hcomp (λ j → λ { (φ = i1) → u (i ∧ j) 1=1 ; (i = i0) → outS u0 }) (outS u0)
-- -- -- comp : (A : ∀ i → Type (ℓ′ i))
-- --        {φ : I}
-- --        (u : ∀ i → [ φ ⊢ A i ] )
-- --        (u0 : A i0 [ φ ↦ u i0 ]) → A i1
