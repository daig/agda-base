{-# OPTIONS --without-K #-}
module Bool where

data 𝔹 : Set where false true : 𝔹

{-# BUILTIN BOOL  𝔹  #-}
{-# BUILTIN FALSE false #-}
{-# BUILTIN TRUE  true  #-}
