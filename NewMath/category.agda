{-# OPTIONS --without-K #-}
module Math.category where
open import Eq hiding (_∙_)
open import Type
open Vars using (ℓ; ℓa; ℓb)
open import Sigma

open import Int


record Cat ℓ : Set (ℓs ℓ) where
  field
    Obj : Set ℓ
    Hom : Obj → Obj → Set ℓ
  private _⇒_ = Hom
  field
    id : (x : Obj) → x ⇒ x
    o : {x y z : Obj} → y ⇒ z → x ⇒ y → x ⇒ z
  private _∘_ = o
  field
    idL : {x y : Obj} (f : Hom x y) → id y ∘ f ≡ f
    idR : {x y : Obj} (f : Hom x y) → f ∘ id x ≡ f
    assoc : {a b c d : Obj} (f : a ⇒ b) (g : b ⇒ c) (h : c ⇒ d)
      → h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f
open Cat using (Obj; Hom)

-- module Cats (𝒞 : Cat ℓa) (𝒟 : Cat ℓb) where





-- -- module Product (𝒞 : Cat ℓ1) (𝒟 : Cat ℓ2) where
-- --     ⊗Obj = Obj 𝒞 × Obj 𝒟
-- --     ⊗Hom : ⊗Obj → ⊗Obj → _
-- --     ⊗Hom (x , a) (y , b) = Hom 𝒞 x y × Hom 𝒟 a b
-- --     ⊗id : ((x , a) : ⊗Obj) → _
-- --     ⊗id (x , a) = id 𝒞 x , id 𝒟 a
-- --     ⊗o : {xa yb zc : Obj 𝒞 × Obj 𝒟} → ⊗Hom yb zc → ⊗Hom xa yb → ⊗Hom xa zc
-- --     ⊗o (f , f') (g , g') = o 𝒞 f g , o 𝒟 f' g'
-- --     ⊗id∘ : {xa yb : ⊗Obj} (f : ⊗Hom xa yb ) → ⊗o (⊗id yb) f ≡ f
-- --     ⊗id∘ {xa @ (x , a) } {yb @ (y , b)} (f @ (f₁ , f₂))
-- --                                                       = ⊗o (⊗id yb) f
-- --                                                      ≡⟨⟩ o 𝒞 (id 𝒞 y) f₁ , o 𝒟 (id 𝒟 b) f₂
-- --       ≡⟨ cong ( λ a → o 𝒞 (id 𝒞 y) f₁ , a ) (id∘ 𝒟 f₂) ⟩ o 𝒞 (id 𝒞 y) f₁ , f₂
-- --       ≡⟨ cong ( λ a → a               , f₂) (id∘ 𝒞 f₁) ⟩ f₁              , f₂
-- --                                                      ≡⟨⟩ f ∎
-- --     -- ⊗id∘ (f , f') rewrite id∘ 𝒞 f | id∘ 𝒟 f' = refl
-- --     ⊗∘id : {xa yb : ⊗Obj} (f : ⊗Hom xa yb ) → ⊗o f (⊗id xa) ≡ f
-- --     ⊗∘id (f , f') = {!!}
-- --     -- ⊗∘id (f , f') rewrite ∘id 𝒞 f | ∘id 𝒟 f' = refl
-- --     ⊗∘assoc : {xa yb zc qd : Obj 𝒞 × Obj 𝒟}
-- --             (f : ⊗Hom xa yb) (g : ⊗Hom yb zc) (h : ⊗Hom zc qd)
-- --             → ⊗o h (⊗o g f) ≡ ⊗o (⊗o h g) f
-- --     ⊗∘assoc (f , f') (g , g') (h , h') = {!!}
-- -- --     ⊗∘assoc (f , f') (g , g') (h , h') rewrite 𝒞 .∘assoc f  g  h
-- -- --                                              | 𝒟 .∘assoc f' g' h' = refl
-- -- _⊗_ : Cat ℓ1 → Cat ℓ2 → Cat (ℓ1 ⊔ ℓ2)
-- -- 𝒞 ⊗ 𝒟 = record { Product 𝒞 𝒟 renaming (⊗Obj to Obj; ⊗Hom to Hom; ⊗id to id; ⊗o to o
-- --                                         ; ⊗id∘ to id∘; ⊗∘id to ∘id; ⊗∘assoc to ∘assoc)}
