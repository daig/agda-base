{-# OPTIONS --type-in-type --cubical #-}
module Math.Category where
open import Eq
open import Type
open import Sigma
open import Cubical.Core hiding (A;B;C)

record Cat : Type where
  constructor Obj:_⇒:_𝒾:_▸:_▸𝒾:_𝒾▸:_assoc:_
  field
    Obj : Type
    Hom : Obj → Obj → Type
  private _⇒_ = Hom
  field
    id : (x : Obj) → x ⇒ x
    c : {x y z : Obj} → x ⇒ y → y ⇒ z → x ⇒ z
  private _▸_ = c
  field
    ▸𝒾 : {x y : Obj} (f : Hom x y) → f ▸ id y ≡ f
    𝒾▸ : {x y : Obj} (f : Hom x y) → id x ▸ f ≡ f
    assoc : {a b c d : Obj} (f : a ⇒ b) (g : b ⇒ c) (h : c ⇒ d)
      → f ▸ (g ▸ h) ≡ (f ▸ g) ▸ h
  record _≅_ (x y : Obj) : Type where
    constructor iso
    field
      to : x ⇒ y
      from : y ⇒ x
      from▸to : from ▸ to ≡ id y
      to▸from : to ▸ from ≡ id x
  ι : (x : Obj) → x ≅ x
  ι x = iso (id x) (id x) (𝒾▸ (id x)) (▸𝒾 (id x))
  ≡→≅ : (a b : Obj) → a ≡ b → a ≅ b
  ≡→≅ a b a≡b = subst (λ x → a ≅ x) a≡b (ι a)

module Product (𝒜 : Cat) (ℬ : Cat) where
    open Cat 𝒜 renaming (Obj to A; Hom to 𝒜[_,_]; id to 𝒾; c to _▸_; 𝒾▸ to 𝒾▸; ▸𝒾 to ▸𝒾;assoc to ▸assoc)
    open Cat ℬ renaming (Obj to B; Hom to ℬ[_,_]; id to 𝒿; c to _▹_; 𝒾▸ to 𝒿▹; ▸𝒾 to ▹𝒿;assoc to ▹assoc)
    _⊗_ : Cat
    _⊗_ = Obj: A × B
            ⇒: (λ (a , b) (a' , b')
              → 𝒜[ a , a' ] × ℬ[ b , b' ])
            𝒾: (λ (a , b)
              → 𝒾 a , 𝒿 b)
            ▸: (λ (f , f') (g , g')
              → (f ▸ g) , (f' ▹ g'))
            ▸𝒾: (λ{(f₁ , f₂) i
              → ▸𝒾 f₁ i , ▹𝒿 f₂ i})
            𝒾▸: (λ{(f₁ , f₂) i
              → 𝒾▸ f₁ i , 𝒿▹ f₂ i})
            assoc: (λ{(f , f') (g , g') (h , h') i
              → ▸assoc f g h i , ▹assoc f' g' h' i})
