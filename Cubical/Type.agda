{-# OPTIONS --without-K --two-level --prop --no-import-sorts #-}
-- https://hott-uf.github.io/2017/abstracts/twoleveltt.pdf
module Type where
open import Agda.Primitive public using (Prop)
open import Agda.Primitive public
  renaming (Set to Type; Setω to Typeω; SSet to SType; SSetω to STypeω)

{-
{-# BUILTIN TYPE Type #-} -- : SType₁
-- https://agda.readthedocs.io/en/v2.6.1/language/prop.html
{-# BUILTIN PROP Prop #-} -- : SType₁
{-# BUILTIN SETOMEGA Typeω #-} -- : SType₁
{-# BUILTIN STRICTSET      SType  #-} -- : SType₁
{-# BUILTIN STRICTSETOMEGA STypeω #-} -- : STypeω₁
-}
