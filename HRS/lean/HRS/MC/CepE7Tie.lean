import HRS.MC.CepE7
import HRS.MC.CepaSpec

/-!
Tie for packet CEPE7.  The verbatim statement `HRS.MC.Cepa.cep_E7_existence` (and the third conjunct of the frozen
`HRS.cepa_log_flow`) is FALSE for a nondegenerate initial law: `IsFilteredSolution.progressive` contains
`Adapted ℱ (ofNNRealTime X)`, hence `Measurable[ℱ t] (X 0)` for every negative `t`, which `Measurable[ℱ 0] X₀` does not give
(take `ℱ t` = null-set algebra for `t < 0`).  The proof `HRS.MC.CepE7.cep_E7_existence_repaired_proof` is for the
statement with `Measurable[ℱ 0] X₀` replaced by `∀ t : ℝ, Measurable[ℱ t] X₀`; the first two conjuncts are verbatim.
The spec `cep_E7_existence` now carries that repaired hypothesis (ISSUES `MC: request CEPA-LOG-FLOW`); the tie below checks it.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

example := (@HRS.MC.CepE7.cep_E7_existence_repaired_proof : type_of% @HRS.MC.Cepa.cep_E7_existence)
