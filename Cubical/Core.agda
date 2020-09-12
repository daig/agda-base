{-# OPTIONS --cubical --prop --no-import-sorts #-}
module Cubical.Core where

open import Type public
open import Sigma public
open import Agda.Builtin.Cubical.Path public renaming (PathP to infix 4 _[_≡_])
-- (λ i → A) [ x ≡ y ] gets printed as x ≡ y when A does not mention i.
--  _≡_ : ∀ {ℓ} {A : Type ℓ} → A → A → Type ℓ
--  _≡_ {A = A} = PathP (λ _ → A)
open import Agda.Builtin.Cubical.Sub public renaming
-- * There are cubical subtypes as in CCHM. Note that these are not fibrant (hence in SType)
-- "Systems"
-- _[_↦_] : ∀ (A : Type ℓ) (φ : I) (u : [ φ ⊢ A ] ) → SType ℓ
  ( Sub to infix 4 _[_↦_] 
-- Any element u : A can be seen as an element of A [ φ ↦ u ] which agrees with u on φ:
-- inS  : (u :       A)    → A [ φ ↦ (λ _ → u) ]
  ; inc to ↦_
-- One can also forget that an element agrees with u on φ:
-- outS : {u : [ φ ⊢ A ] } → A [ φ ↦         u ] → A
  ; primSubOut to _↦) 

open import Agda.Primitive.Cubical public renaming
-- * The Interval
-- data I : Typeω where i0 i1 : I
  (primIMin to _∧_ -- I → I → I
  ;primIMax to _∨_ -- I → I → I
  ;primINeg to ~_
-- empty : ∀ {ℓ} {A : [ i0 ⊢ Type ℓ ] } → [ i0 ⊩ A ]
  ;isOneEmpty to empty

-- * Composition operation according to [CCHM 18].
-- When calling "comp A φ u a" Agda makes sure that "a" agrees with "u i0" on "φ".
-- comp : ∀ {ℓ} (A : ∀ i → Type (ℓ i)) {φ} (u : ∀ i → [ φ ⊢ A i ] ) (a : A i0) → A i1
  ;primComp to comp 
-- Note: this is not recommended to use, instead use the CHM primitives! (below)
-- The reason is that these work with HITs and produce fewer empty systems.

--- Heterogeneous composition can defined as in CHM, however we use the
-- builtin one as it doesn't require u0 to be a cubical subtype. This reduces the number of inS's a lot.
-- comp : ∀ {ℓ′} (A : ∀ i → Type (ℓ′ i)) {φ} (u : ∀ i → [ φ ⊢ A i ] ) (u0 : A i0 [ φ ↦ u i0 ]) → A i1
-- comp A {φ = φ} u u0 =
--   hcomp (λ i → λ { (φ = i1) → transp (λ j → A (i ∨ j)) i (u _ 1=1) })
--         (transp A i0 (outS u0))

-- * Generalized transport and homogeneous composition [CHM 18].

  -- When calling "transp A φ a" Agda makes sure that "A" is constant on "φ".
-- transp : (A : I → Type ℓ) (φ : I) (a : A i0) → A i1
  ;primTransp to transp 

-- When calling "hcomp A φ u a" Agda makes sure that "a" agrees with "u i0" on "φ".
-- hcomp : {A : Type ℓ} {φ : I} (u : I → [ φ ⊢ A ] ) (a : A) → A
  ;primHComp to hcomp 

--   * @r =i1@ represents the constraint "r = i1".
-- Often we will use "φ" for elements of I, when we intend to use them  with _=i1 (or Partial[P]).
-- _=i1 : I → SType ℓ0
  ; IsOne to _=i1 
-- 1=1 : i1 =i1
  ;itIsOne to 1=1

-- * Types of partial elements, and their dependent version.

-- "[ φ ⊢ A ]" is a special version of "φ =i1 → A" with a more extensional judgmental equality.
-- [_⊢_] : ∀ {ℓ} → (φ : I) →       Type ℓ   → Typeω
  ;Partial to [_⊢_]
-- "[ φ ⊩ A ]" allows "A" to be defined only on "φ".
-- [_⊩_] : ∀ {ℓ} → (φ : I) → [ φ ⊢ Type ℓ ] → Typeω
  ; PartialP to [_⊩_])
-- Partial elements are introduced by pattern matching with (r = i0) or (r = i1) constraints, like so:

private -- Partial examples
  sys : ∀ i → [ i ∨ ~ i ⊢ Type₁ ]
  sys i (i = i0) = Type₀
  sys i (i = i1) = Type₀ → Type₀

  -- It also works with pattern matching lambdas:
  sys' : ∀ i → [ i ∨ ~ i ⊢ Type₁ ]
  sys' i = λ { (i = i0) → Type₀ ; (i = i1) → Type₀ → Type₀}


  

  -- When the cases overlap they must agree.
  sys2 : ∀ i j → [ i ∨ (i ∧ j) ⊢ Type₁ ]
  sys2 i j = λ { (i = i1) → Type₀ ; (i = i1) (j = i1) → Type₀}

  -- (i0 = i1) is actually absurd.
  sys3 : [ i0 ⊢ Type₁ ]
  sys3 () 

  sub1 : {A : Type} {x y : A} (e : x ≡ y) (i : I)
      →  A [ i ∨ ~ i ↦ ( λ{ (i = i0) → x
                            ; (i = i1) → y } ) ]
  sub1 e i = ↦ e i

  sub : {A : Type} {x : A} →  A [ i1 ↦ ( λ{ 1=1 → x } ) ]
  sub {x = x} = sub1 (λ _ → x) i0

  sub2 : {A : Type} {x y : A} (e : x ≡ y) (i : I)
      →  A [ ~ i ↦ ( λ{ (i = i0) → x } ) ]
  sub2 e i = ↦ (sub1 e i ↦)

private
  variable
    ℓ ℓa  ℓb ℓc : Level
    ℓ′ : I → Level
    φ : I
    A : Type ℓa

-- Homogeneous filling
hfill : {φ : I} (u : I → [ φ ⊢ A ]) (u0 : A [ φ ↦ u i0 ])
  → u0 ↦ ≡ hcomp u (u0 ↦)
hfill {φ = φ} u u0 i =
  hcomp (λ j → λ { (φ = i1) → u (i ∧ j) 1=1 ; (i = i0) → u0 ↦ }) (u0 ↦)




-- Heterogeneous composition can defined as in CHM, however we use the
-- builtin one as it doesn't require u0 to be a cubical subtype.
-- This reduces the number of inS's a lot.
-- comp : (A : ∀ i → Type (ℓ′ i))
--        {φ : I}
--        (u : ∀ i → [ φ ⊢ A i ] )
--        (u0 : A i0 [ φ ↦ u i0 ])
--      → ---------------------------
--        A i1
-- comp A {φ = φ} u u0 =
--   hcomp (λ i → λ { (φ = i1) → transp (λ j → A (i ∨ j)) i (u _ 1=1) })
--         (transp A i0 (outS u0))


-- Heterogeneous filling defined using comp
fill : (A : ∀ i → Type (ℓ′ i))
       (u : ∀ i → [ φ ⊢ A i ])
       (u0 : A i0 [ φ ↦ u i0 ])
       (i : I) → A i
fill {φ = φ} A u u0 i = comp (λ j → A (i ∧ j)) (λ j → λ { (φ = i1) → u (i ∧ j) 1=1 ; (i = i0) → u0 ↦}) (u0 ↦)

-- module CubicalEquiv where
--   open import Agda.Builtin.Cubical.Glue public renaming
-- -- contractible? A = Σ A \ x → (∀ y → x ≡ y)
-- -- record equiv? (f : A → B) : Set (ℓa ⊔ ℓb) where
-- --   field equiv-proof : (y : B) → contractible? (fiber f y)
-- --   ~                 : (y : B) → Σ (Σ A \ x → f x ≡ y) \ x↦y → (∀ x′↦y → x↦y ≡ x′↦y)
--     (_≃_ to _≃_
--     ;isEquiv to equiv?
--     ;equivFun to to
--     ;equivProof to proof)
-- -- fiber {A = A} f y = Σ A \ x → f x ≡ y
--   open Helpers public using (fiber) renaming (isContr to contractible?)
-- open CubicalEquiv using (_≃_; equiv? ; fiber ; contractible?)
-- proof' : ∀ (A : Type ℓa) (B : Type ℓb) (w : A ≃ B) (let f = CubicalEquiv.to w; f⁻¹ = fiber f)
--      → (y : B) → ∀ φ → ( [ φ ⊢ f⁻¹ y ] ) → f⁻¹ y
-- proof' A B (f , w ) y φ x↦y with CubicalEquiv.equiv-proof w y
-- ... | (x′↦y , p) = hcomp (λ i → λ { (φ = i1) → p (x↦y 1=1) i
--                                 ; (φ = i0) → x′↦y})
--                            x′↦y
--   -- contr (c , p) φ u = hcomp (λ i → λ { (φ = i1) → p (u 1=1) i
--   --                                     ; (φ = i0) → c })
--   --                           c

-- -- proof' A B w a ψ fb = contr' {A = fiber (w .fst) a} (w .snd .equiv-proof a) ψ fb
-- --   where
-- --     contr' : ∀ {ℓ} {A : Type ℓ} → contractible? A → (φ : I) → (u : [ φ ⊢ A ] ) → A
-- --     contr' {A = A} (c , p) φ u = hcomp (λ i → λ { (φ = i1) → p (u 1=1) i
-- --                                                 ; (φ = i0) → c }) c



-- -- infix 4 _≃_


-- -- _≃_ : ∀ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') → Set (ℓ ⊔ ℓ')
-- -- A ≃ B = Σ (A → B) \ f → equiv? f
-- -- {-# BUILTIN EQUIV      _≃_        #-}

-- -- -- Improved version of equivProof compared to Lemma 5 in CCHM. We put
-- -- -- the (φ = i0) face in contr' making it be definitionally c in this
-- -- -- case. This makes the computational behavior better, in particular
-- -- -- for transp in Glue.
-- -- equivProof : ∀ {ℓa ℓt} (T : Type ℓt) (A : Type ℓa) → (w : T ≃ A) → (a : A)
-- --            → ∀ ψ → [ ψ ⊢ fiber (w .fst) a ] → fiber (w .fst) a
-- -- equivProof A B w a ψ fb = contr' {A = fiber (w .fst) a} (w .snd .equiv-proof a) ψ fb
-- --   where
-- --     contr' : ∀ {ℓ} {A : Set ℓ} → isContr A → (φ : I) → (u : Partial φ A) → A
-- --     contr' {A = A} (c , p) φ u = hcomp (λ i → λ { (φ = i1) → p (u 1=1) i
-- --                                                 ; (φ = i0) → c }) c


-- -- {-# BUILTIN EQUIVFUN   equivFun   #-}
-- -- {-# BUILTIN EQUIVPROOF equivProof #-}

-- -- primitive
-- --     primGlue    : ∀ {ℓ ℓ'} (A : Set ℓ) {φ : I}
-- --       → (T : Partial φ (Set ℓ')) → (e : PartialP φ (λ o → T o ≃ A))
-- --       → Set ℓ'
-- --     prim^glue   : ∀ {ℓ ℓ'} {A : Set ℓ} {φ : I}
-- --       → {T : Partial φ (Set ℓ')} → {e : PartialP φ (λ o → T o ≃ A)}
-- --       → (t : PartialP φ T) → (a : A) → primGlue A T e
-- --     prim^unglue : ∀ {ℓ ℓ'} {A : Set ℓ} {φ : I}
-- --       → {T : Partial φ (Set ℓ')} → {e : PartialP φ (λ o → T o ≃ A)}
-- --       → primGlue A T e → A



-- -- module _ {ℓ : I → Level} (P : (i : I) → Set (ℓ i)) where
-- --   private
-- --     E : (i : I) → Set (ℓ i)
-- --     E  = λ i → P i
-- --     ~E : (i : I) → Set (ℓ (~ i))
-- --     ~E = λ i → P (~ i)

-- --     A = P i0
-- --     B = P i1

-- --     f : A → B
-- --     f x = transp E i0 x

-- --     g : B → A
-- --     g y = transp ~E i0 y

-- --     u : ∀ i → A → E i
-- --     u i x = transp (λ j → E (i ∧ j)) (~ i) x

-- --     v : ∀ i → B → E i
-- --     v i y = transp (λ j → ~E ( ~ i ∧ j)) i y

-- --     fiberPath : (y : B) → (xβ0 xβ1 : fiber f y) → xβ0 ≡ xβ1
-- --     fiberPath y (x0 , β0) (x1 , β1) k = ω , λ j → δ (~ j) where
-- --       module _ (j : I) where
-- --         private
-- --           sys : A → ∀ i → PartialP (~ j ∨ j) (λ _ → E (~ i))
-- --           sys x i (j = i0) = v (~ i) y
-- --           sys x i (j = i1) = u (~ i) x
-- --         ω0 = comp ~E (sys x0) ((β0 (~ j)))
-- --         ω1 = comp ~E (sys x1) ((β1 (~ j)))
-- --         θ0 = fill ~E (sys x0) (inc (β0 (~ j)))
-- --         θ1 = fill ~E (sys x1) (inc (β1 (~ j)))
-- --       sys = λ {j (k = i0) → ω0 j ; j (k = i1) → ω1 j}
-- --       ω = hcomp sys (g y)
-- --       θ = hfill sys (inc (g y))
-- --       δ = λ (j : I) → comp E
-- --             (λ i → λ { (j = i0) → v i y ; (k = i0) → θ0 j (~ i)
-- --                      ; (j = i1) → u i ω ; (k = i1) → θ1 j (~ i) })
-- --              (θ j)

-- --     γ : (y : B) → y ≡ f (g y)
-- --     γ y j = comp E (λ i → λ { (j = i0) → v i y
-- --                             ; (j = i1) → u i (g y) }) (g y)

-- --   pathToisEquiv : isEquiv f
-- --   pathToisEquiv .equiv-proof y .fst .fst = g y
-- --   pathToisEquiv .equiv-proof y .fst .snd = sym (γ y)
-- --   pathToisEquiv .equiv-proof y .snd = fiberPath y _

-- --   pathToEquiv : A ≃ B
-- --   pathToEquiv .fst = f
-- --   pathToEquiv .snd = pathToisEquiv



Path : ∀ {ℓ} (A : Type ℓ) → A → A → Type ℓ
Path A a b = (λ _ → A) [ a ≡ b ]
