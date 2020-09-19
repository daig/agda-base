module FloatField where
open import Field using (Field)
import Float


module FloatImpl where
  Elt = Float.ℝ
  _+_ = Float._+_
  𝟘 = 0.0
  _×_ = Float._*_
  𝟙 = 1.0


ℝ : Field
ℝ = record
      { FloatImpl
      ; +assoc = {!!}
      ; +comm = {!!}
      ; 𝟘+ = {!!}
      ; -_ = {!!}
      ; -inv = {!!}
      ; ×assoc = {!!}
      ; ×comm = {!!}
      ; 𝟙× = {!!}
      ; +×distrib = {!!}
      ; 𝟙÷_ = {!!}
      }
