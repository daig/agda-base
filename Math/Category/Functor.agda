{-# OPTIONS --cubical #-}
module Math.Category.Functor where
open import Eq 
open import Sigma
open import Math.Category
open import Cubical.Core hiding (A; B; C; D; E)

open import Int

private
  variable
    ℓa' ℓb' ℓc' : Level
    𝒞 : Cat ℓa ℓa'
    𝒟 : Cat ℓb ℓb'

module _ (𝒞 : Cat ℓa ℓa') (𝒟 : Cat ℓb ℓb') where
    open Cat 𝒞 renaming (Obj to C; Hom to _⟿_; id to 𝒾; o to _∘_) 
    open Cat 𝒟 renaming (Obj to D; Hom to _⇒_; id to 𝒿; o to infix 9 _◂_; assoc to ◂assoc; idL to 𝒿◂; idR to ◂𝒿) 
    record Functor : Type (ℓa ⊔ ℓb ⊔ ℓa' ⊔ ℓb') where
        field
            to : C → D
            map : {x y : C} → x ⟿ y → to x ⇒ to y
            map𝒾 : (x : C) → map {x} 𝒾 ≡ 𝒿
            map∘ : {x y z : C} (f : y ⟿ z) (g : x ⟿ y) → map (f ∘ g) ≡ map f ◂ map g
module _ (𝒞 : Cat ℓ ℓ') where
    open Cat 𝒞 renaming (Obj to C; Hom to _⇒_; id to 𝒾; o to _∘_) 
    module id where
      to : C → C
      to z = z
      map : {x y : C} → x ⇒ y → x ⇒ y 
      map z = z
      map𝒾 : (x : C) → map {x} 𝒾 ≡ 𝒾
      map𝒾 x = ✓
      map∘ : {x y z : C} (f : y ⇒ z) (g : x ⇒ y) → map (f ∘  g) ≡ map f ∘ map g
      map∘ f g = ✓
    id : Functor 𝒞 𝒞
    id = record {id}

module _ {𝒞 : Cat ℓa ℓa'} {𝒟 : Cat ℓb ℓb'} {ℰ : Cat ℓc ℓc'} (𝒢 : Functor 𝒟 ℰ) (ℱ : Functor 𝒞 𝒟) where
    open Cat 𝒞 renaming (Obj to C; Hom to _⟿_; id to 𝒾; o to _∘_) 
    open Cat 𝒟 renaming (Obj to D; Hom to _⇒_; id to 𝒿; o to infix 9 _◂_; assoc to ◂assoc; idL to 𝒿◂; idR to ◂𝒿) 
    open Cat ℰ renaming (Obj to E; Hom to _⇛_; id to 𝓀; o to infix 9 _∙_; assoc to ∙assoc; idL to 𝓀∙; idR to ∙𝓀) 
    open Functor ℱ renaming (to to F₀; map to F₁; map𝒾 to F𝒾; map∘ to F∘) 
    open Functor 𝒢 renaming (to to G₀; map to G₁; map𝒾 to G𝒿; map∘ to G◂)
    module o where
        to : C → E
        to x =  G₀ (F₀ x)
        map : {x y : C} → x ⟿ y → to x ⇛ to y
        map f = G₁ (F₁ f)
        map𝒾 : (x : C) → map {x} 𝒾 ≡ 𝓀
        map𝒾 x = (G₁ ⟨$⟩ F𝒾 x) ⋯ G𝒿 (F₀ x)
        map∘ : {x y z : C} (f : y ⟿ z) (g : x ⟿ y) → map (f ∘ g) ≡ map f ∙ map g
        map∘ f g = (G₁ ⟨$⟩ F∘ f g) ⋯ G◂ (F₁ f) (F₁ g)
    o : Functor 𝒞 ℰ
    o = record {o}
module o-laws {ℓa ℓa' ℓb ℓb' : Level} {𝒞 : Cat ℓa ℓa'} {𝒟 : Cat ℓb ℓb'} (ℱ : Functor 𝒞 𝒟) where
    open Cat 𝒞 renaming (Obj to C; Hom to _⟿_; id to 𝒾; o to _∘_; idL to 𝒾∘; idR to ∘𝒾) 
    open Cat 𝒟 renaming (Obj to D; Hom to _⇒_; id to 𝒿; o to infix 9 _◂_; assoc to ◂assoc; idL to 𝒿◂; idR to ◂𝒿) 
    open Functor ℱ renaming (to to F₀; map to F₁; map𝒾 to F𝒾; map∘ to F∘) 
    open Functor (id 𝒟) renaming (to to ι₀; map to ι₁; map𝒾 to ι𝒿; map∘ to ι∘) 
    open Functor (o (id 𝒟) ℱ) renaming (to to ι∘F₀; map to ι∘F₁; map𝒾 to ι∘F𝒾; map∘ to ι∘F∘)
    idL-to : ι∘F₀ ≡ F₀
    idL-to = ✓
    idL-map : ∀ {x y} → ι∘F₁ {x} {y} ≡ F₁
    idL-map = ✓
    -- idL-map𝒾 : ι∘F𝒾 ≡ F𝒾
    -- idL-map𝒾 = Eq.Π go where
    --     go : ∀ x → ι∘F𝒾 x ≡ F𝒾 x
    --     go x i j = {!!} -- hcomp (λ {k (i = i0) → ι∘F𝒾 x (k ∧ j); k (i = i1) → F𝒾 x (k ∧ j)}) (F₁ 𝒾)
    --            -- (ι₁ ⟨$⟩ F𝒾 x) ⋯ ι𝒿 (F₀ x) ≡⟨⟩ (λ i → hcomp (λ{j (i = i0) → F₁ 𝒾; j (i = i1) → ι𝒿 (F₀ x) j}) ((ι₁ ⟨$⟩ F𝒾 x) i)) ≡⟨⟩ F𝒾 x ∎
        -- rewrite F𝒾 x = ✓
-- x≡y ∙ y≡z = refl ∙∙ x≡y ∙∙ y≡z
-- (x≡y ∙ y≡z) i = hcomp (doubleComp-faces refl y≡z i) (x≡y i)
-- trans {a = a} a≡x x≡b i = hcomp (λ{j (i = i0) → a ;j (i = i1) → x≡b j}) (a≡x i)

--     o.map𝒾 (id 𝒟) ℱ x
--                ≡⟨ {!!} ⟩ F𝒾 x ∎
-- idL : {𝒞 𝒟 : Cat} (ℱ : Functor 𝒞 𝒟) → o (id 𝒟) ℱ ≡ ℱ
