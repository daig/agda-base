module Chu where
open import Eq
open Reasoning
open import Agda.Primitive using (Level; _⊔_) renaming (Set to Type; lsuc to ℓs; lzero to ℓ0)
open import Sigma
open import Fun
open import Fun.Partial
open import Bool
open import Fin
open import Nat
open import Unit
open import Empty
open import Either
open import Iso

open Bool.IO



variable ℓ ℓa ℓb ℓc : Level

record chu  (alphabet : Type ℓa) : Type (ℓs (ℓa ⊔ ℓb ⊔ ℓc)) where
  field
     carrier : Type ℓb
     state : Type ℓc
     matrix : (a : carrier) (x : state) → alphabet

normal : {α : Type ℓa} (A : Type ℓb) (p : (A → α) → Type) → chu α
chu.carrier (normal A _ ) =  A
chu.state (normal A p ) = ∃ p
chu.matrix (normal A p) a (x , _) = x a

normal? : {α : Type ℓa} (𝒞 : chu {ℓa} {ℓb} {ℓa ⊔ ℓb} α)
  → Type (ℓs (ℓa ⊔ ℓb))
normal? {α = α} record { carrier = A ; state = X ; matrix = Ω }
  =  Σ ((A → α) → Type) \ p → Σ (X ≡ ∃ p) \ X≡∃p → (∀ a x → Ω a x ≡ π₁ (subst′ X≡∃p x) a)

record injective? {A : Type ℓa} {B : Type ℓb} (f : A → B) : Type (ℓa ⊔ ℓb) where
  field proof : (x y : A) (e : f x ≡ f y) → x ≡ y

fiber : {A : Type ℓa} {B : Type ℓb} (f : A → B) (y : B) → Type (ℓa ⊔ ℓb)
fiber f y = ∃ \ x → f x ≡ y

module props {α : Type _} (c : chu {ℓa} {ℓb} {ℓc} α) where
    open chu c public renaming (matrix to Ω; carrier to A; state to X)
    Ω˘ = flip Ω; Ω⁻¹ = fiber Ω; Ω˘⁻¹ = fiber Ω˘
    row    = X → α -- coexisting entities / conjunctive space
    column = A → α -- predicates or states / alternative qualities / disjunctive space
    separable? = injective? Ω
    extensional? = injective? Ω˘
    biextensional? = separable? × extensional?

    biext-collapse _⊥ : chu α
    chu.carrier biext-collapse = Σ row    Ω⁻¹
    chu.state   biext-collapse = Σ column Ω˘⁻¹
    chu.matrix biext-collapse (_ , a , _) = λ (_ , x , _) → Ω a x

    chu.carrier _⊥ = X
    chu.state _⊥ = A
    chu.matrix _⊥ = Ω˘
open props using (row; column)

liftA2 : {α : Type ℓa} {B : Type ℓb} → (α → α → α) → (B → α) → (B → α) → B → α
liftA2 _⊕_ x y b = x b ⊕ y b

_|∧|_ _|∨|_ : {A : Type ℓa} → (A → 𝔹) → (A → 𝔹) → A → 𝔹
_|∧|_ = liftA2 _∧_
_|∨|_ = liftA2 _∨_

module collapse {α : Type _} (c : chu {ℓa} {ℓb} {ℓc} α) where
    open chu c renaming (matrix to Ω; carrier to A; state to X)
    open props c


    -- this doesn't seem true ???
    -- collapse-biext : props.biextensional? (props.biext-collapse c)
    -- injective?.proof (π₁ collapse-biext) (f , x , refl) (g , y , refl) e = {!lemma e!} where
    --         lemma : (e : chu.matrix (props.biext-collapse c) (Ω x , x , refl) ≡
    --                      chu.matrix (props.biext-collapse c) (Ω y , y , refl)) →
    --                 (Ω x , x , refl) ≡ (Ω y , y , refl)
    --         lemma = {!!}
    -- injective?.proof (π₂ collapse-biext) = {!!}


module example where
  pattern a = fz
  pattern b = fs fz
  pattern c = fs (fs fz)
  
  -- a | 01010101
  -- b | 00110011
  -- c | 00001111
  e1 e2 : chu 𝔹
  e1 = normal (Fin 3) \ _ → ⊤
  -- a | 01111
  -- b | 00101
  -- c | 00011
  e2p e2ap e3p : (Fin 3 → 𝔹) → Type
  e2p p
     = p a ≡ O × p b ≡ O × p c ≡ O
    || p a ≡ I × p b ≡ O × p c ≡ O
    || p a ≡ I × p b ≡ I × p c ≡ O
    || p a ≡ I × p b ≡ O × p c ≡ I
    || p a ≡ I × p b ≡ I × p c ≡ I

  e2 = normal (Fin 3) e2p
  e2' : 𝔹
  e2' = chu.matrix e2 a ( (λ { a → O ; b →  O; c → O}) , ˡ (✓ , ✓ , ✓))
  e2'' : e2' ≡ O
  e2'' = ✓
  open Bool.LE using (_≤_ ; ≤I)
  e2ap p = ((p b ≤ p a) ∧ (p c ≤ p a)) ≡ true
  -- e2 with a more compact description
  e2a = normal (Fin 3) e2ap
  e2a' = chu.matrix e2a a ( (λ { a → I ; b →  O; c → O}) , ✓)
  -- states in e2 are closed under bitwise meets and joins
  open LE
  e2-join : {c1 c2 : props.column e2a} → e2ap c1 → e2ap c2 → e2ap (c1 |∨| c2)
  e2-join {c1} {c2} b≤a∧¹c≤a b≤a∧²c≤a
    with  ≤π₁ {c1 b ≤ c1 a} b≤a∧¹c≤a
        | ≤π₂ {c1 b ≤ c1 a} b≤a∧¹c≤a
        | ≤π₁ {c2 b ≤ c2 a} b≤a∧²c≤a
        | ≤π₂ {c2 b ≤ c2 a} b≤a∧²c≤a
  ... | b≤¹a | c≤¹a | b≤²a | c≤²a with ≤∨ {c1 b} {c2 b} b≤¹a b≤²a | ≤∨ {c1 c} {c2 c} c≤¹a c≤²a
  ... | b¹∨b²≤a¹∨a² | c¹∨c²≤a¹∨a² = ∧I b¹∨b²≤a¹∨a² c¹∨c²≤a¹∨a²
  e2-meet : {c1 c2 : props.column e2a} → e2ap c1 → e2ap c2 → e2ap (c1 |∧| c2)
  e2-meet {c1} {c2} b≤a∧¹c≤a b≤a∧²c≤a
    with  ≤π₁ {c1 b ≤ c1 a} b≤a∧¹c≤a
        | ≤π₂ {c1 b ≤ c1 a} b≤a∧¹c≤a
        | ≤π₁ {c2 b ≤ c2 a} b≤a∧²c≤a
        | ≤π₂ {c2 b ≤ c2 a} b≤a∧²c≤a
  ... | b≤¹a | c≤¹a | b≤²a | c≤²a with ≤∧ (c1 b) (c2 b) b≤¹a b≤²a | ≤∧ (c1 c) (c2 c) c≤¹a c≤²a
  ... | b¹∧b²≤a¹∧a² | c¹∧c²≤a¹∧a² = ∧I b¹∧b²≤a¹∧a² c¹∧c²≤a¹∧a²



  b0c0→e2ap : ∀ p → p a ≡ I → e2ap p
  b0c0→e2ap p a1 
    = (p b ≤ p a) ∧ (p c ≤ p a)
    ≡⟨ a1 ⟨&⟩ ( λ xx → (p b ≤ xx) ∧ (p c ≤ xx)) ⟩ (p b ≤ I) ∧ (p c ≤ I)
    ≡⟨ ≤I (p b) ⟨&⟩ (λ xx → xx ∧ (p c ≤ I)) ⟩ I ∧ (p c ≤ I)
    ≡⟨⟩ p c ≤ I
    ≡⟨  ≤I (p c)  ⟩ true ∎

  e2p→e2ap : ∀ p → e2p p → e2ap p
  e2p→e2ap p = go where
    go : e2p p → e2ap p
    go (ˡ (a0 , b0 , c0 )) 
        = (p b ≤ p a) ∧ (p c ≤ p a)
        ≡⟨ a0 ⟨&⟩ ( λ xx → (p b ≤ xx) ∧ (p c ≤ xx)) ⟩ (p b ≤ O) ∧ (p c ≤ O)
        ≡⟨ b0 ⟨&⟩ ( λ xx → (xx  ≤ O ) ∧ (p c ≤ O )) ⟩ (O   ≤ O) ∧ (p c ≤ O)
        ≡⟨ c0 ⟨&⟩ ( λ xx → (O   ≤ O ) ∧ (xx  ≤ O )) ⟩ (O   ≤ O) ∧ (O   ≤ O)
        ≡⟨⟩ true ∎
    go (ʳ (ˡ (a1 , _)))       = b0c0→e2ap p a1
    go (ʳ (ʳ (ˡ (a1 , _))))    = b0c0→e2ap p a1
    go (ʳ (ʳ (ʳ (ˡ (a1 , _))))) = b0c0→e2ap p a1
    go (ʳ (ʳ (ʳ (ʳ (a1 , _))))) = b0c0→e2ap p a1

  -- a | 0111
  -- b | 0101
  -- c | 0011
  -- semilattice - rows closed under join
  e3p p = p a ≡ (p b ∨ p c)
  e3 = normal (Fin 3) e3p 

  I≢O : ¬ I ≡ O
  I≢O ()

  -- columns no longer closed under meets
  ¬e3-meet : ¬ ({c1 c2 : props.column e3} → e3p c1 → e3p c2 → e3p (c1 |∧| c2))
  ¬e3-meet k =  I≢O (k {λ{ a → I; b → I; c → O}} {λ{ a → I; b → O; c → I}} ✓ ✓)

module props2 {α : Type ℓa} (𝒞 : chu {ℓa} {ℓb} {ℓc} α) where
    open props 𝒞
    constants-agree : (β θ : α) (a : A) (aconst : ∀ x′ → Ω a  x′ ≡ β)
                                (x : X) (xconst : ∀ a′ → Ω a′  x ≡ θ)
                   → β ≡ θ
    constants-agree β θ a aconst x xconst with aconst x | xconst a
    ... | ✓ | ✓ = ✓
    constants-preclude : (β : α) (a : A) (aconst : ∀ x′ → Ω a x′ ≡ β)
                         (θ : α) (b : A) (bconst : ∀ x′ → Ω b x′ ≡ θ)
                         (β≢θ : ¬ β ≡ θ)
                         → (δ : α) (x : X) → ¬ (∀ a′ → Ω a′ x ≡ δ)
    constants-preclude β a aconst θ b bconst β≢θ δ x xconst with aconst x | bconst x | xconst a | xconst b
    ... | ✓ | ✓ | aΩx≡bΩx | ✓ = β≢θ aΩx≡bΩx

proper : {α : Type ℓa} {A : Type ℓb} (_∙_ : (A → α) → (A → α) → A → α)
         (x y : A → α) → Type (ℓa ⊔ ℓb)
proper _∙_ x y = ¬ (x ∙ y ≡ x) × ¬ (x ∙ y ≡ y)
proper∧ proper∨ : {A : Type ℓ} (x y : A → 𝔹) → Type _
proper∧ = proper _|∧|_
proper∨ = proper _|∨|_

module props3 (𝒞 : chu {ℓ0} {ℓb} {ℓb} 𝔹) (n : normal? 𝒞) where
    open props 𝒞
    open Σ n renaming (π₁ to p; π₂ to nn)
    open Σ nn renaming (π₁ to X≡∃p ; π₂ to Ω≡$ )
    p12-lemma : {a b : A} → proper∨ (Ω a) (Ω b) → Σ X \ x → Σ X \ y
      → Ω a x ≡ I
       × Ω b y ≡ I
       × Ω a y ≡ O
       × Ω b x ≡ O
    p12-lemma (a∨b≢a , a∨b≢b) = {! !} , {!!} , {!!} , {!!} , {!!} , {!!}
    -- proper-excludes : proper∧ a b → ¬ (proper 
    prop-12 : {a b : A} → proper∨ (Ω a) (Ω b)
           → ¬ ({x y : X} → proper∧ (Ω˘ x) (Ω˘ y))
    prop-12 {a} {b} p {- @(a∨b≢a , a∨b≢b) -} zz with p12-lemma {a} {b} p
    ... | x , y , Ωax≡I , Ωby≡I , Ωay≡O , Ωbx≡O with zz {x} {y}
    ... | x∧y≢x , x∧y≢y = x∧y≢x (funExt {!ff!})
        where
            ff : (a′ : A) → Ω a′ x ∧ Ω a′ y ≡ Ω a′ x
            ff a′ = {!!}


    

  -- =  Σ ((A → α) → Type) \ p → X ≡ ∃ p
