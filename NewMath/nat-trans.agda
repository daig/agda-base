{-# OPTIONS --without-K #-}
module nat-trans where
open import Eq hiding (_∙_)
open import Type
open Vars using (ℓ; ℓa; ℓb; ℓc)
open import Sigma

open import Int

open import category
open import functor using (Functor)

module _ {𝒞 : Cat ℓa} {𝒟 : Cat ℓb} (ℱ 𝒢 : Functor 𝒞 𝒟) where
      open Cat 𝒞 renaming (Obj to C; Hom to _↝_; id to 𝒾; o to infix 9 _∘_
                           ;assoc to ∘assoc; idL to 𝒾∘; idR to ∘𝒾) 
      open Cat 𝒟 renaming (Obj to D; Hom to _⇒_; id to 𝒿; o to infix 9 _◂_
                           ;assoc to ◂assoc; idL to 𝒿◂; idR to ◂𝒿) 
      open Functor ℱ renaming (to to F₀; map to F₁; map𝒾 to F𝒾) 
      open Functor 𝒢 renaming (to to G₀; map to G₁)
      record Nat : Set (ℓa ⊔ ℓb) where
          field
              to : (x : C) → F₀ x ⇒ G₀ x
              comm : {x y : C} (f : x ↝ y) → to y ◂ F₁ f ≡ G₁ f ◂ to x

module _ {𝒞 : Cat ℓa} {𝒟 : Cat ℓb} where
    open Cat 𝒞 renaming (Obj to C; Hom to _↝_; id to 𝒾; o to infix 9 _∘_
                         ;assoc to ∘assoc; idL to 𝒾∘; idR to ∘𝒾) 
    open Cat 𝒟 renaming (Obj to D; Hom to _⇒_; id to 𝒿; o to infix 9 _◂_
                         ;assoc to ◂assoc; idL to 𝒿◂; idR to ◂𝒿) 
    module _ (ℱ : Functor 𝒞 𝒟) where
        open Functor ℱ renaming (to to F₀; map to F₁; map𝒾 to F𝒾) 
        module id where
            to : (x : C) → F₀ x ⇒ F₀ x
            to x = F₁ (𝒾 x)
            comm : {x y : C} (f : x ↝ y) → to y ◂ F₁ f ≡ F₁ f ◂ to x
            comm {x} {y} f 
                    =                                    to y ◂ F₁ f
                    ≡⟨⟩                              F₁ (𝒾 y) ◂ F₁ f
                    ≡⟨  F𝒾 y ⟨&⟩ (λ a → a ◂ F₁ f) ⟩ 𝒿 (F₀ y) ◂ F₁ f
                    ≡⟨ 𝒿◂ (F₁ f) ⟩                             F₁ f
                    ≡˘⟨ ◂𝒿 (F₁ f) ⟩                     F₁ f ◂ 𝒿 (F₀ x)
                    ≡˘⟨  F𝒾 x ⟨&⟩ (λ a → F₁ f ◂ a) ⟩    F₁ f ◂ F₁ (𝒾 x)
                    ≡⟨⟩                                 F₁ f ◂ to x ∎
        id : Nat ℱ ℱ
        id = record {id}
    module _ {ℱ 𝒢 ℋ : Functor 𝒞 𝒟} (n : Nat 𝒢 ℋ) (m : Nat ℱ 𝒢) where
        open Functor ℱ renaming (to to F₀; map to F₁; map𝒾 to F𝒾) 
        open Functor 𝒢 renaming (to to G₀; map to G₁)
        open Functor ℋ renaming (to to H₀; map to H₁)
        open Nat n      renaming (to to α; comm to αcomm)
        open Nat m      renaming (to to β; comm to βcomm)

        module o where
          to : (x : C) → F₀ x ⇒ H₀ x
          to x = α x ◂ β x

          comm : {x y : C} (f : x ↝ y) → to y ◂ F₁ f ≡ H₁ f ◂ to x
          comm {x} {y} f
                      = to y ◂ F₁ f
                      ≡⟨⟩ (α y ◂ β y) ◂ F₁ f
                      ≡˘⟨ ◂assoc (F₁ f) (β y) (α y) ⟩   α y  ◂ (β  y  ◂ F₁ f)
                      ≡⟨ βcomm f ⟨&⟩ (λ q → α y ◂ q) ⟩  α y  ◂ (G₁ f  ◂ β  x)
                      ≡⟨ ◂assoc (β x) (G₁ f) (α y) ⟩   (α y  ◂  G₁ f) ◂ β  x
                      ≡⟨ αcomm f ⟨&⟩ (λ a → a ◂ β x) ⟩ (H₁ f ◂  α  x) ◂ β  x
                      ≡˘⟨ ◂assoc (β x) (α x) (H₁ f) ⟩   H₁ f ◂ (α  x  ◂ β  x)
                                                      ≡⟨⟩ H₁ f ◂ to x ∎
        o : Nat ℱ ℋ
        o = record {o}
        -- to o x = α x ◂ β x
    -- open Nat⊚
      
--     module Nat-ι-laws {ℱ 𝒢 : Functor} (n : Nat ℱ 𝒢) where
--         open Functor ℱ renaming (to to F₀; map to F₁; map𝒾 to F𝒾) 
--         open Functor 𝒢 renaming (to to G₀; map to G₁; map𝒾 to G𝒾)
--         open Nat n renaming (to to α; comm to αcomm)

--         module _ where
--           open Nat-ι 𝒢
--           ι◂ : (x : C) → (ια x ◂ α x) ≡ α x
--           ι◂ x = G₁ (𝒾 x) ◂ α x
--               ≡⟨ G𝒾 x ⟨&⟩ (λ q → q ◂ α x) ⟩ 𝒿 (G₀ x) ◂ α x
--               ≡⟨ 𝒿◂ (α x) ⟩ α x ∎
--         module _ where
--           open Nat-ι ℱ
--           ◂ι : (x : C) → (α x ◂ ια x) ≡ α x
--           ◂ι x = α x ◂ F₁ (𝒾 x)
--               ≡⟨ F𝒾 x ⟨&⟩ (λ q → α x ◂ q) ⟩ α x ◂ 𝒿 (F₀ x)
--               ≡⟨ ◂𝒿 (α x) ⟩ α x ∎

--     module Nat⊚ {ℱ 𝒢 ℋ : Functor} (n : Nat 𝒢 ℋ) (m : Nat ℱ 𝒢) where
--         open Functor ℱ renaming (to to F₀; map to F₁; map𝒾 to F𝒾) 
--         open Functor 𝒢 renaming (map to G₁)
--         open Functor ℋ renaming (to to H₀; map to H₁)
--         open Nat n      renaming (to to α; comm to αcomm)
--         open Nat m      renaming (to to β; comm to βcomm)

--         _⊚_ : Nat ℱ ℋ
--         to _⊚_ x = α x ◂ β x
--         comm _⊚_ {x} {y} f
--                     = γ y ◂ F₁ f
--                     ≡⟨⟩ (α y ◂ β y) ◂ F₁ f
--                     ≡˘⟨ ◂assoc (F₁ f) (β y) (α y) ⟩   α y  ◂ (β  y  ◂ F₁ f)
--                     ≡⟨ βcomm f ⟨&⟩ (λ q → α y ◂ q) ⟩  α y  ◂ (G₁ f  ◂ β  x)
--                     ≡⟨ ◂assoc (β x) (G₁ f) (α y) ⟩   (α y  ◂  G₁ f) ◂ β  x
--                     ≡⟨ αcomm f ⟨&⟩ (λ a → a ◂ β x) ⟩ (H₁ f ◂  α  x) ◂ β  x
--                     ≡˘⟨ ◂assoc (β x) (α x) (H₁ f) ⟩   H₁ f ◂ (α  x  ◂ β  x)
--                                                     ≡⟨⟩ H₁ f ◂ γ x ∎
--             where γ = to _⊚_
--     open Nat⊚
--     [_,_] : Cat (ℓa ⊔ ℓb)
--     Obj [_,_] = Functor
--     Hom [_,_] =  Nat
--     Cat.id [_,_] = Nat-ι.ι
--     Cat.o [_,_] =  _⊚_
--     -- Cat.idL [_,_] {ℱ} {𝒢} n with Nat-ι-laws.ι◂ n | Nat-ι.ι 𝒢 ⊚ n
--     -- Cat.idL [_,_] {ℱ} {𝒢} record { to = α ; comm = αcomm } | ff | record { to = α′ ; comm = αcomm′ } with funExt {! !}
--     -- ... | xx = {!!}
--     -- --     where
--     --       open Functor ℱ renaming (to to F₀; map to F₁; map𝒾 to F𝒾)
--     --       open Functor 𝒢 renaming (to to G₀; map to G₁; map𝒾 to G𝒾)
--     -- -- Cat.idR [_,_] = {!!}
--     -- Cat.assoc [_,_] = {!!}
--               -- { Obj = FObj 𝒞 𝒟
--               -- ; Hom = FHom 𝒞 𝒟
--               -- ; id = Fi 𝒞 𝒟
--               -- ; o = Fo 𝒞 𝒟
--               -- ; id∘ = {! Fio!}
--               -- ; ∘id = {!!}
--               -- ; ∘assoc = {!!}
--               -- }

-- --     Fioα : {ℱ 𝒢 : FObj} (n : Nat ℱ 𝒢) → Nat.to (ι 𝒢 ⊚ n) ≡ Nat.to n
-- --     Fioα = {!!}
-- -- --   -- β   (Foa (Fi G) n) ≡ α n
-- --   -- β   (λ x → o 𝒟 (α (Fi G) x) (α n x)) ≡ α n
-- --   -- β   (λ x → o 𝒟 (Fiα G x) (α n x)) ≡ α n
-- --   -- β   (λ x → o 𝒟 (F₁ G (id 𝒞 x)) (α n x)) ≡ α n
-- --   -- Fid  (λ x → o 𝒟 (id 𝒟 (F₀ G x)) (α n x)) ≡ α n
-- --   -- id∘  (λ x → α n x) ≡ α n
-- --   --    α n ≡ α n
-- --   Fioα {F} {G} n
-- -- --    rewrite ExtFid
-- --     = {!!}



-- --   Fio : {F G : FObj} (n : Nat F G) → Fo (Fi G) n ≡ n
-- --   Fio {F} {G} n with Fi G | Fo (Fi G) n
-- --   ... | record { α = α₁ ; αcomm = αcomm₁ } | record { α = α ; αcomm = αcomm } = {!!}


-- -- open FunctorCat
