import HRS.MS.MovSchAux5

/-!
# S6.4: the tie `mov_schwartz_proof`

`HRS.MS.MovSch.mov_schwartz_proof : type_of% @HRS.Whole.mov_schwartz` (frozen statement of `HRS/Whole/Moving.lean`).  Proved in
`MovSchAux5` (`s64_schwartz`) from S6.3 (`mov63_decay_f0`, `mov_nl_unique_conjunct`, `mne_hasDeriv`) and the weighted Leibniz bounds
of `MovSchAux1`-`MovSchAux4`.
-/

noncomputable section

namespace HRS.MS.MovSch

theorem mov_schwartz_proof : type_of% @HRS.Whole.mov_schwartz := @s64_schwartz

end HRS.MS.MovSch

end
