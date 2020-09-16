{-# OPTIONS --cubical #-}
module Cubical.Documentation where
open import Type
open import Cubical.Core as Export using (φ ; ℓ′)

module Paths where
  postulate -- * The Interval
    I : SType
    i0 i1 : I
    _∧_ _∨_ : I → I → I
    ~_ : I → I

    _[_≡_] : {ℓ : Level} (A′ : I → Type ℓ) → A′ i0 → A′ i1 → Type ℓ
-- (λ i → A) [ x ≡ y ] gets printed as x ≡ y when A does not mention i.
  _≡_ : ∀ {ℓ} {A : Type ℓ} → A → A → Type ℓ
  _≡_ {A = A} x y = (λ _ → A) [ x ≡ y ]
module Partial where -- Types of partial elements ("Systems"), and their dependent version.
  open Export using (I; i0; i1)
  postulate
    _=i1 : I → SType -- @r =i1@ represents the constraint "r = i1".
    1=1 : i1 =i1
  -- "[ φ ⊢ A ]" is a special version of "φ =i1 → A" with a more extensional judgmental equality.
  [_⊢_]   : ∀ {ℓ} → (φ : I) →       Type ℓ   → SType ℓ
  [ φ ⊢ A ] = φ =i1 → A
  postulate -- "[ φ ⊩ A ]" allows "A" to be defined only on "φ".
    [_⊩_] : ∀ {ℓ} → (φ : I) → [ φ ⊢ Type ℓ ] → SType ℓ
    empty : ∀ {ℓ} {A : [ i0 ⊢ Type ℓ ]} → [ i0 ⊩ A ]
module Partial-Examples where
-- Partial elements are introduced by pattern matching
-- with (r = i0) or (r = i1) constraints
  open Export using ([_⊢_]; [_⊩_]; _∧_; _∨_; ~_; i0 ; i1; empty; 1=1)
  module _ (X Y : Type) where
    sys : ∀ i → [ i ∨ ~ i ⊢ Type ]
    sys i (i = i0) = X
    sys i (i = i1) = Y
    sysX sysY : Type
    sysX = sys i0 1=1
    sysY = sys i1 1=1

  -- It also works with pattern matching lambdas:
  sys' : ∀ i → [ i ∨ ~ i ⊢ Type₁ ]
  sys' i = λ { (i = i0) → Type₀ ; (i = i1) → Type₀ → Type₀}

  -- When the cases overlap they must agree.
  sys2 : ∀ i j → [ i ∨ (i ∧ j) ⊢ Type₁ ]
  sys2 i j = λ { (i = i1) → Type₀ ; (i = i1) (j = i1) → Type₀}

  -- (i0 = i1) is actually absurd.
  sys3 : [ i0 ⊢ Type₁ ]
  sys3 () 
  sys4 : [ i0 ⊩ sys3 ]
  sys4 = empty {A = sys3}
module Sub where -- * There are cubcal subtypes as in CCHM.
-- Note that these are not fibrant (hence in SType)
  open Export using (I; [_⊢_])

  postulate
    _[_↦_] : ∀ (A : Type ℓ) (φ : I) (u : [ φ ⊢ A ] ) → SType ℓ
 -- Any element u : A can be seen as an element of A [ φ ↦ u ] which agrees with u on φ:
    ↦_ : (u  :       A   ) → A [ φ ↦ (λ _ → u) ]
-- One can also forget that an element agrees with u on φ:
    _↦ : {u′ : [ φ ⊢ A ] } → A [ φ ↦        u′ ] → A

module Sub-Examples where
  open Export using (I; i0; i1; _∨_; ~_; _≡_; _[_↦_]; _↦; ↦_)
  sub1 : ∀ {x y} (e : x ≡ y) (i : I)
      →  A [ i ∨ ~ i ↦ ( λ{ (i = i0) → x
                          ; (i = i1) → y } ) ]
  sub1 e i = ↦ e i

  sub : ∀ {x} →  A [ i1 ↦ ( λ{ 1=1 → x } ) ]
  sub {x = x} = sub1 (λ _ → x) i0

  sub2 : ∀ {x y} (e : x ≡ y) (i : I)
      →  A [ ~ i ↦ ( λ{ (i = i0) → x } ) ]
  sub2 e i = ↦ (sub1 e i ↦)

module Kan where
  open Export using (I; i0; i1; _∨_; _∧_; 1=1; [_⊢_]; _[_↦_]; _↦; ↦_) 
-- When calling "hcomp A φ u a" Agda makes sure that "a" agrees with "u i0" on "φ".
  postulate
  -- When calling "hcomp A φ u a" Agda makes sure that "a" agrees with "u i0" on "φ".
    hcomp : (u : I → [ φ ⊢ A ] ) (a : A) → A
  -- When calling "transp A φ a" Agda makes sure that "A" is constant on "φ".
  -- Effectively this means @transp A i1 ≡ id@
    transp : (A : (i : I) → Type (ℓ′ i)) (φ : I) (a : A i0) → A i1
-- Heterogeneous composition can defined as in CHM, however we use the
-- builtin one as it doesn't require u0 to be a cubical subtype.
-- This reduces the number of inS's a lot.
  comp : (A′ : ∀ i → Type (ℓ′ i))
         {φ : I}
         (u : ∀ i →  [ φ ⊢ A′ i ] ) 
         (u0 : A′ i0 [ φ ↦ u i0 ]) -- actually just A′ i0 - coercion is automatic
      → A′ i1
  comp A′ {φ = φ} u u0 =
      hcomp (λ { i (φ = i1) → transp (λ j → A′ (i ∨ j)) i (u i 1=1) })
            (transp A′ i0 (u0 ↦))

  

-- * Composition operation according to [CCHM 18].
-- When calling "comp A φ u a" Agda makes sure that "a" agrees with "u i0" on "φ".
-- comp : ∀ {ℓ} (A : ∀ i → Type (ℓ i)) {φ} (u : ∀ i → [ φ ⊢ A i ] ) (a : A i0) → A i1
-- Note: this is not recommended to use, instead use the CHM primitives! (below)
-- The reason is that these work with HITs and produce fewer empty systems.
