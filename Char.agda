{-# OPTIONS --cubical #-}
module Char where
open import Nat
open import Bool

postulate Char : Set
{-# BUILTIN CHAR Char #-}


module PrimChar where
    primitive
        primIsLower primIsDigit primIsAlpha primIsSpace primIsAscii
            primIsLatin1 primIsPrint primIsHexDigit : Char → 𝔹
        primToUpper primToLower : Char → Char
        primCharToNat : Char → ℕ
        primNatToChar : ℕ → Char
        primCharEquality : Char → Char → 𝔹
open PrimChar public renaming
    (primIsLower to lower?
    ;primIsDigit to digit?
    ;primIsAlpha to alpha?
    ;primIsSpace to space?
    ;primIsAscii to ascii?
    ;primIsLatin1 to latin1?
    ;primIsPrint to print?
    ;primIsHexDigit to hex?
    ;primToUpper to upper
    ;primToLower to lower
    ;primCharToNat to toℕ
    ;primNatToChar to fromℕ
    ;primCharEquality to eq?)
