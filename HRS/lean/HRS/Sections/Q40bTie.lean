import HRS.Sections.Q40bAux12
import HRS.Sections.Q40bAux15

/-!
# Proposition 5.14: exact-statement ties (packet Q40b)

`HRS.criterion_comparison` and `HRS.criterion_stationary` (Sec5.lean) keep their frozen `sorry`: their proofs need
infrastructure that imports Sec5.lean.  The proofs are `criterion_comparison_proof_aem` (Q40bAux12.lean; the statement of
the repaired `criterion_comparison`, with `AEMeasurable G`, ISSUES §I "5.14 G") and `criterion_stationary_proof`
(Q40bAux15.lean).
-/

namespace HRS

example := (@criterion_comparison_proof_aem : type_of% @HRS.criterion_comparison)
example := (@criterion_stationary_proof : type_of% @HRS.criterion_stationary)

end HRS
