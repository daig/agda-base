{-# OPTIONS --without-K #-}
module Float where
open import Bool
open import Nat
open import Int
open import String
open import Word


postulate ℝ : Set
{-# BUILTIN FLOAT ℝ #-}

module PrimFloat where
    primitive 
    -- primFloatToWord64 : ℝ → 𝕎
        primFloatEquality : ℝ → ℝ → 𝔹
        primFloatLess     : ℝ → ℝ → 𝔹
        primFloatNumericalEquality : ℝ → ℝ → 𝔹
        primFloatNumericalLess     : ℝ → ℝ → 𝔹
        primNatToFloat    : ℕ → ℝ
        primFloatPlus     : ℝ → ℝ → ℝ
        primFloatMinus    : ℝ → ℝ → ℝ
        primFloatTimes    : ℝ → ℝ → ℝ
        primFloatNegate   : ℝ → ℝ
        primFloatDiv      : ℝ → ℝ → ℝ
        primFloatSqrt     : ℝ → ℝ
        primRound         : ℝ → ℤ
        primFloor         : ℝ → ℤ
        primCeiling       : ℝ → ℤ
        primExp           : ℝ → ℝ
        primLog           : ℝ → ℝ
        primSin           : ℝ → ℝ
        primCos           : ℝ → ℝ
        primTan           : ℝ → ℝ
        primASin          : ℝ → ℝ
        primACos          : ℝ → ℝ
        primATan          : ℝ → ℝ
        primATan2         : ℝ → ℝ → ℝ
        primShowFloat     : ℝ → 𝕊
open PrimFloat public renaming
        (primFloatEquality to eq?
        ;primFloatLess     to le?
        ;primFloatNumericalEquality to eq~?
        ;primFloatNumericalLess     to le~?
        ;primNatToFloat    to fromℕ
        ;primFloatPlus     to _+_
        ;primFloatMinus    to _-_
        ;primFloatTimes    to _*_
        ;primFloatNegate   to -_
        ;primFloatDiv      to _÷_
        ;primFloatSqrt     to sqrt
        ;primRound         to round
        ;primFloor         to ⌊_⌋
        ;primCeiling       to ⌈_⌉
        ;primExp           to e^_
        ;primLog           to log
        ;primSin           to sin
        ;primCos          to cos
        ;primTan           to tan
        ;primASin          to asin
        ;primACos          to acos
        ;primATan          to atan
        ;primATan2         to atan2
        ;primShowFloat     to showFloat)
