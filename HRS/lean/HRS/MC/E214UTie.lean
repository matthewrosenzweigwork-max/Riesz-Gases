import HRS.MC.E214U
import HRS.Main.HeadlineEdgeworth

/-!
# E214UTie

Checks that `HRS.MC.E214U.stationary_tensor_relaxation_proof` has exactly the type of the frozen
`HRS.Main.stationary_tensor_relaxation` (unproved there, in `HRS/Main/HeadlineEdgeworth.lean`; the warning is expected).
-/

noncomputable section

example := (@HRS.MC.E214U.stationary_tensor_relaxation_proof : type_of% @HRS.Main.stationary_tensor_relaxation)

end
