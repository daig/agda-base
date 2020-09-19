{-# OPTIONS --cubical --safe #-}
module Fun.Extensionality where
open import Cubical.Equiv.Univalence using ( ≃→≡ )
open import Cubical.Core
open import Cubical.Core public using (_≡_)
open import Cubical.Equiv as Equiv hiding (equiv)
open import Sigma
open import Cubical.Glue
open import Iso
open import Eq

-- Function extensionality is an equivalence
module _ {A : Type ℓa} {B : A → I → Type ℓb} {f : (x : A) → B x i0} {g : (x : A) → B x i1} where

  fx≡gx→f≡g : (       (x : A) → (B x ) [ f x ≡ g x ] )
      → (λ i → (x : A) → B x i) [ f   ≡ g   ]
  fx≡gx→f≡g = Eq.Π
  {-# INLINE fx≡gx→f≡g #-}

  -- called `happly` and defined by path induction
  -- in the HoTT book (see function 2.9.2 in section 2.9)
  f≡g→fx≡gx : (λ i → (x : A) → B x i) [ f ≡ g ]
    → ((x : A) → B x [ f x ≡ g x ])
  f≡g→fx≡gx f≡g x i = f≡g i x

  fx≡gx≅f≡g : (∀ x → B x [ f x ≡ g x ]) ≅ ((λ i → ∀ x → B x i) [ f ≡ g ])
  fx≡gx≅f≡g = iso fx≡gx→f≡g f≡g→fx≡gx (λ x _ → x) (λ x _ → x)

  module FunExt where
    private
        fib : (p : (λ i → ∀ x → B x i) [ f ≡ g ]) → [ fx≡gx→f≡g ]↣ p
        fib p = f≡g→fx≡gx p , (λ _ → fx≡gx→f≡g (f≡g→fx≡gx p))

        contract : ∀ p → (fi : [ fx≡gx→f≡g ]↣ p) → fib p ≡ fi
        contract p (h , eq) i = (f≡g→fx≡gx (eq (~ i)) , λ j → eq (~ i ∨ j))

    equiv : Equiv.equiv fx≡gx→f≡g
    Equiv.equiv.proof equiv p = (fib p , contract p)

  fx≡gx≃f≡g : (∀ x → B x [ f x ≡ g x ]) ≃ ((λ i → ∀ x → B x i) [ f ≡ g ])
  fx≡gx≃f≡g = fx≡gx→f≡g , FunExt.equiv

  fx≡gx≣f≡g : (∀ x → B x [ f x ≡ g x ]) ≡ ((λ i → ∀ x → B x i) [ f ≡ g ])
  fx≡gx≣f≡g = ≃→≡ fx≡gx≃f≡g
