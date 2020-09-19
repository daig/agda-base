module functor where
open import Eq hiding (_∙_)
open import Type
open Vars using (ℓ; ℓa; ℓb; ℓc)
open import Sigma
open import category

open import Int

module _ (𝒞 : Cat ℓa) (𝒟 : Cat ℓb) where
    open Cat 𝒞 renaming (Obj to C; Hom to _↝_; id to 𝒾; o to _∘_) 
    open Cat 𝒟 renaming (Obj to D; Hom to _⇒_; id to 𝒿; o to infix 9 _◂_; assoc to ◂assoc; idL to 𝒿◂; idR to ◂𝒿) 
    record Functor : Set (ℓa ⊔ ℓb) where
        field
            to : C → D
            map : {x y : C} → x ↝ y → to x ⇒ to y
            map𝒾 : (x : C) → map (𝒾 x) ≡ 𝒿 (to x)
            map∘ : {x y z : C} (f : y ↝ z) (g : x ↝ y) → map (f ∘ g) ≡ map f ◂ map g
module _ (𝒞 : Cat ℓ) where
    open Cat 𝒞 renaming (Obj to C; Hom to _⇒_; id to 𝒾; o to _∘_) 
    module id where
      to : C → C
      to z = z
      map : {x y : C} → x ⇒ y → x ⇒ y 
      map z = z
      map𝒾 : (x : C) → map (𝒾 x) ≡ 𝒾 x
      map𝒾 x = ✓
      map∘ : {x y z : C} (f : y ⇒ z) (g : x ⇒ y) → map (f ∘  g) ≡ map f ∘ map g
      map∘ f g = ✓
    id : Functor 𝒞 𝒞
    id = record {id}

module _ {𝒞 : Cat ℓa} {𝒟 : Cat ℓb} {ℰ : Cat ℓc} (𝒢 : Functor 𝒟 ℰ) (ℱ : Functor 𝒞 𝒟) where
    open Cat 𝒞 renaming (Obj to C; Hom to _↝_; id to 𝒾; o to _∘_) 
    open Cat 𝒟 renaming (Obj to D; Hom to _⇒_; id to 𝒿; o to infix 9 _◂_; assoc to ◂assoc; idL to 𝒿◂; idR to ◂𝒿) 
    open Cat ℰ renaming (Obj to E; Hom to _⇛_; id to 𝓀; o to infix 9 _∙_; assoc to ∙assoc; idL to 𝓀∙; idR to ∙𝓀) 
    open Functor ℱ renaming (to to F₀; map to F₁; map𝒾 to F𝒾; map∘ to F∘) 
    open Functor 𝒢 renaming (to to G₀; map to G₁; map𝒾 to G𝒿; map∘ to G◂)
    module o where
        to : C → E
        to x =  G₀ (F₀ x)
        map : {x y : C} → x ↝ y → to x ⇛ to y
        map x = G₁ (F₁ x)
        map𝒾 : (x : C) → map (𝒾 x) ≡ 𝓀 (to x)
        map𝒾 x   rewrite F𝒾 x   | G𝒿 (F₀ x)        = ✓
        map∘ : {x y z : C} (f : y ↝ z) (g : x ↝ y) → map (f ∘ g) ≡ map f ∙ map g
        map∘ f g rewrite F∘ f g | G◂ (F₁ f) (F₁ g) = ✓
    o : Functor 𝒞 ℰ
    o = record {o}
module o-laws {𝒞 𝒟 : Cat ℓ} (ℱ : Functor 𝒞 𝒟) where
    open Cat 𝒞 renaming (Obj to C; Hom to _↝_; id to 𝒾; o to _∘_; idL to 𝒾∘; idR to ∘𝒾) 
    open Cat 𝒟 renaming (Obj to D; Hom to _⇒_; id to 𝒿; o to infix 9 _◂_; assoc to ◂assoc; idL to 𝒿◂; idR to ◂𝒿) 
    open Functor ℱ renaming (to to F₀; map to F₁; map𝒾 to F𝒾; map∘ to F∘) 
    idL-to : Functor.to (o (id 𝒟) ℱ) ≡ F₀
    idL-to = ✓
    idL-map : ∀ {x y} → o.map (id 𝒟) ℱ {x} {y} ≡ F₁
    idL-map = ✓
    idL-map𝒾 : o.map𝒾 (id 𝒟) ℱ ≡ F𝒾
    idL-map𝒾 = funExt go where
        go : ∀ x → o.map𝒾 (id 𝒟) ℱ x ≡ F𝒾 x
        go x rewrite F𝒾 x = ✓

    -- o.map𝒾 (id 𝒟) ℱ x
               -- ≡⟨ {!!} ⟩ F𝒾 x ∎
idL : {𝒞 𝒟 : Cat ℓ} (ℱ : Functor 𝒞 𝒟) → o (id 𝒟) ℱ ≡ ℱ
