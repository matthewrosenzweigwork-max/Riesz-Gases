import HRS.MS.SA16Y4Nc4
import HRS.MS.SA16Y4Nc3
import HRS.MS.SA16SNl3

/-!
# S.A.16 (SA16Y4) Nc5: limit of the nonlocal pairing along coefficients converging pointwise with a common decay bound

`sa16y4_nl_tendsto`: if `a_j → μ` pointwise, `|a_j|, |μ| ≤ W (1+‖x‖)^{-(d+3)}`, `T0_j` (resp. `Tμ`) the nonlocal operators of `a_j`
(resp. `μ`) on `W^{m,p}`, `m ≥ 1`, and `g_j ⇀ G` boundedly, then `ℓ_ψ(T0_j g_j) → ℓ_ψ(Tμ G)`.
No derivative of the coefficients enters.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Nc5
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

lemma sa16y4_memLp_pow {h : EuclideanSpace ℝ (Fin d) → ℝ} (hc : Continuous h) {K r : ℝ} (hK : 0 ≤ K)
    (hr : (d : ℝ) < r) (hb : ∀ x, |h x| ≤ K * (1 + ‖x‖) ^ (-r)) {q : ℝ≥0∞} (hq1 : 1 ≤ q) (hq : q ≠ ⊤) :
    MemLp h q volume := by
  refine sa16so_memLp_decay hc (K := K) hr (fun x => (hb x).trans ?_) hq1 hq
  refine mul_le_mul_of_nonneg_left ?_ hK
  have hr0 : 0 < r := lt_of_le_of_lt (Nat.cast_nonneg d) hr
  have hjb : 0 < jbracket x := by unfold jbracket; positivity
  have hle : jbracket x ≤ 1 + ‖x‖ := by
    unfold jbracket
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    nlinarith [norm_nonneg x]
  exact Real.rpow_le_rpow_of_nonpos hjb hle (by linarith)

end Nc5

end HRS.Whole.AppendixA.Phase2SA16R
