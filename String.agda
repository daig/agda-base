{-# OPTIONS --without-K #-}
module String where

open import Bool
open import List
open import Char
open import Nat using (ℕ)

postulate 𝕊 : Set
{-# BUILTIN STRING 𝕊 #-}

module PrimString where
    primitive
        primStringToList   : 𝕊 → [ Char ]
        primStringFromList : [ Char ] → 𝕊
        primStringAppend   : 𝕊 → 𝕊 → 𝕊
        primStringEquality : 𝕊 → 𝕊 → 𝔹
        primShowChar       : Char → 𝕊
        primShowString     : 𝕊 → 𝕊
        -- primShowNat        : ℕ → 𝕊
open PrimString public renaming
    (primStringToList   to toList
    ;primStringFromList to fromList
    ;primStringAppend   to _++_
    ;primStringEquality to eq?
    ;primShowChar       to showChar
    ;primShowString     to showString)
