{-# OPTIONS --prop --cubical --without-K #-}
module VectorSpace where
open import Cubical.Eq
open import Field
open import Level


module _ (K : Field) (let open Field.Field K) where
    record VectorSpace  : Set₁ where
        infixl 6 _|+|_
        infixl 7 _×|_ 
        infix 8 ~_
        --  𝟙÷_
        field Vec : Set
        field vplus : (v w : Vec) → Vec
        private _|+|_ = vplus
        field |+|assoc : ∀ a b c → a |+| b |+| c ≡ a |+| (b |+| c)
        field |+|comm : ∀ a b → a |+| b ≡ b |+| a
        field ε : Vec
        field ε|+| : ∀ x → ε  |+| x ≡ x 
        |+|ε : ∀ x → x |+| ε  ≡ x
        |+|ε x = trans (|+|comm x ε) (ε|+| x)

        field ~_ : Vec → Vec
        field ~inv : ∀ x → ~ x |+| x ≡ ε
        inv~ : ∀ x → x |+| ~ x ≡ ε
        inv~ x = trans (|+|comm x (~ x)) (~inv x)
        _|-|_ : Vec → Vec → Vec
        v |-| w = v |+| ~ w

        field _×|_ : (k : Elt) (v : Vec) → Vec
        field ×|assoc : (c k : Elt) (v : Vec) → (c × k) ×| v ≡ c ×| (k ×| v) 
        field 𝟙×| : ∀ v → 𝟙 ×| v ≡ v 
        field ×|+|distrib : ∀ k v w → k ×| (v |+| w) ≡ k ×| v |+| k ×| w
        field +×|distrib : ∀ c k v → (c + k) ×| v ≡ c ×| v |+| k ×| v
open VectorSpace


module LinearMap {ℓ : Level } {K : Field} (V W : VectorSpace K)  where
    open VectorSpace V renaming (vplus to _+v_)
    open VectorSpace W renaming (vplus to _+w_)
    record _⊸_ : Set ℓ where
        field to : Vec V → Vec W
        field to+ : (u v : Vec V) → to (u +v v) ≡ to u +w to v
