import HRS.MS.SA16Y3S5c

/-!
# S.A.16 (SA16Y3) C1: strong continuity in time of the transport operator from sup-norm continuity of the coefficients

`sa16y3_B_continuousOn`: if `r ↦ b_r` is continuous in the `C^k_b` sense on `[0,T]` (for every `ε > 0` and `r0` there is `δ > 0`
with `SA16BddCoef k ε (b_r - b_{r0})` for `|r - r0| < δ`), then `r ↦ sa16so_B (b_r) y` is continuous on `[0,T]` for every `y`.
This is the transport half of `hKc` of `sa16r_fixedn_mild` for the truncated mollified drifts (the coefficient hypothesis is the
concrete input still to be verified).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section C1
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

lemma sa16y3_cB_linear (d k : ℕ) (ε : ℝ) : sa16so_cB d k ε = ε * sa16so_cB d k 1 := by
  unfold sa16so_cB; ring

theorem sa16y3_B_continuousOn {k : ℕ} {T : ℝ} (bcf : ℝ → Fin d → Euc d → ℝ)
    (hb : ∀ r ∈ Icc (0 : ℝ) T, ∃ B, SA16BddCoef k B (bcf r))
    (hc : ∀ r0 ∈ Icc (0 : ℝ) T, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ r ∈ Icc (0 : ℝ) T, |r - r0| < δ →
      SA16BddCoef k ε (fun i x => bcf r i x - bcf r0 i x))
    (y : WmpSpace d (k + 1) p) :
    ContinuousOn (fun r => sa16so_B d k p (bcf r) y) (Icc (0 : ℝ) T) := by
  intro r0 hr0
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  set c1 : ℝ := sa16so_cB d k 1 with hc1
  have hc10 : 0 ≤ c1 := sa16so_cB_nonneg d k zero_le_one
  set ε' : ℝ := ε / (2 * (c1 * ‖y‖ + 1)) with hε'
  have hε'0 : 0 < ε' := by positivity
  obtain ⟨δ, hδ, hδc⟩ := hc r0 hr0 ε' hε'0
  refine ⟨δ, hδ, fun r hr hrd => ?_⟩
  have hd := hδc r hr (by simpa [Real.dist_eq] using hrd)
  obtain ⟨B0, hB0⟩ := hb r0 hr0
  obtain ⟨B1, hB1⟩ := hb r hr
  have hsub := sa16so_B_sub (p := p) hB1 hB0
  have hnorm := sa16so_B_norm (p := p) hd
  have hdiff : sa16so_B d k p (bcf r) y - sa16so_B d k p (bcf r0) y =
      sa16so_B d k p (fun i x => bcf r i x - bcf r0 i x) y := by
    rw [hsub]; rfl
  rw [dist_eq_norm, hdiff]
  refine lt_of_le_of_lt ((sa16so_B d k p _).le_opNorm y) ?_
  calc ‖sa16so_B d k p (fun i x => bcf r i x - bcf r0 i x)‖ * ‖y‖ ≤ sa16so_cB d k ε' * ‖y‖ :=
        mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
    _ = ε' * (c1 * ‖y‖) := by rw [sa16y3_cB_linear]; ring
    _ < ε := by
        rw [hε', div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith [mul_nonneg hc10 (norm_nonneg y)]

end C1

end HRS.Whole.AppendixA.Phase2SA16R
