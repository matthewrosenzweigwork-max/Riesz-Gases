import HRS.MS.Mov63HAux2

/-!
# S6.3: the tie `mov_nonlinear_proof`

`HRS.MS.Mov63.mov_nonlinear_proof : type_of% @HRS.Whole.mov_nonlinear` (frozen statement of `HRS/Whole/Moving.lean`, with the uniqueness
conjunct at exponent `0`).  Proved in `Mov63HAux2` (`mnh_nonlinear`) from N1-N8 (`Mov63Aux*`, `Mov63BAux*`, ..., `Mov63GAux*`).
-/

noncomputable section

namespace HRS.MS.Mov63

theorem mov_nonlinear_proof : type_of% @HRS.Whole.mov_nonlinear := @mnh_nonlinear

end HRS.MS.Mov63

end
