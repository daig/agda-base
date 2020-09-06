{-# OPTIONS --without-K #-}
module List where

infixr 5 _::_
data [_] {ℓ} (A : Set ℓ) : Set ℓ where
  [] : [ A ]
  _::_ : (x : A) (xs : [ A ]) → [ A ]

{-# BUILTIN LIST [_] #-}
