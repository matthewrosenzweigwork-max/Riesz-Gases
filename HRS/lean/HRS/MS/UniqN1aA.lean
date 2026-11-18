import HRS.MS.UniqN0b

/-!
# N1a of `UniqPlan.md`, part (a): smooth cutoff around the origin

`n1aΦ ε z = 1 - b (ε⁻¹ z)` with `b` a fixed `ContDiffBump` (`= 1` on `B̄(0,1)`, `= 0` off `B(0,2)`):
`n1aΦ ε = 0` on `B̄(0,ε)`, `= 1` off `B(0,2ε)`, `0 ≤ n1aΦ ε ≤ 1`, `‖∇ n1aΦ ε‖ ≤ L ε⁻¹`, and
`∇ n1aΦ ε` vanishes outside the annulus `ε ≤ ‖z‖ ≤ 2ε`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace HRS.MS.UniqN1a

open HRS HRS.Whole HRS.Whole.AppendixALemmas HRS.MS.UniqT3

variable {d : ℕ}

/-- The fixed bump. -/
def n1aBump (d : ℕ) : ContDiffBump (0 : Euc d) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The cutoff vanishing near `0`. -/
def n1aΦ (ε : ℝ) (z : Euc d) : ℝ := 1 - n1aBump d (ε⁻¹ • z)

theorem n1aΦ_contDiff (ε : ℝ) : ContDiff ℝ ∞ (n1aΦ (d := d) ε) := by
  unfold n1aΦ
  exact contDiff_const.sub ((n1aBump d).contDiff.comp (contDiff_const_smul _))

theorem n1aΦ_zero {ε : ℝ} (hε : 0 < ε) {z : Euc d} (hz : ‖z‖ ≤ ε) : n1aΦ ε z = 0 := by
  unfold n1aΦ
  rw [(n1aBump d).one_of_mem_closedBall, sub_self]
  rw [mem_closedBall_zero_iff, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hε]
  show ε⁻¹ * ‖z‖ ≤ 1
  rw [inv_mul_le_iff₀ hε]; linarith

theorem n1aΦ_one {ε : ℝ} (hε : 0 < ε) {z : Euc d} (hz : 2 * ε ≤ ‖z‖) : n1aΦ ε z = 1 := by
  unfold n1aΦ
  rw [(n1aBump d).zero_of_le_dist, sub_zero]
  rw [dist_zero_right, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hε]
  show 2 ≤ ε⁻¹ * ‖z‖
  rw [le_inv_mul_iff₀ hε]; linarith

theorem n1aΦ_nonneg (ε : ℝ) (z : Euc d) : 0 ≤ n1aΦ ε z := by
  unfold n1aΦ; linarith [(n1aBump d).le_one (x := ε⁻¹ • z)]

theorem n1aΦ_le_one (ε : ℝ) (z : Euc d) : n1aΦ ε z ≤ 1 := by
  unfold n1aΦ; linarith [(n1aBump d).nonneg (x := ε⁻¹ • z)]

/-- Uniform bound for the derivative of the bump. -/
theorem n1a_bump_fderiv_bound : ∃ L : ℝ, 0 ≤ L ∧ ∀ w : Euc d, ‖fderiv ℝ (n1aBump d) w‖ ≤ L := by
  have hc : Continuous (fderiv ℝ (n1aBump d)) := ((n1aBump d).contDiff (n := 1)).continuous_fderiv one_ne_zero
  have hs : HasCompactSupport (fderiv ℝ (n1aBump d)) := (n1aBump d).hasCompactSupport.fderiv (𝕜 := ℝ)
  obtain ⟨L, hL⟩ := hc.bounded_above_of_compact_support hs
  exact ⟨max L 0, le_max_right _ _, fun w => (hL w).trans (le_max_left _ _)⟩

theorem n1aΦ_fderiv_eq (ε : ℝ) (z : Euc d) :
    fderiv ℝ (n1aΦ (d := d) ε) z = -((fderiv ℝ (n1aBump d) (ε⁻¹ • z)).comp (ε⁻¹ • ContinuousLinearMap.id ℝ (Euc d))) := by
  have h1 : HasFDerivAt (fun z : Euc d => ε⁻¹ • z) (ε⁻¹ • ContinuousLinearMap.id ℝ (Euc d)) z :=
    (hasFDerivAt_id z).const_smul ε⁻¹
  have h2 : HasFDerivAt (n1aBump d) (fderiv ℝ (n1aBump d) (ε⁻¹ • z)) (ε⁻¹ • z) :=
    (((n1aBump d).contDiff (n := 1)).differentiable one_ne_zero _).hasFDerivAt
  have h3 := (h2.comp z h1).const_sub 1
  have : n1aΦ (d := d) ε = fun z => 1 - n1aBump d (ε⁻¹ • z) := rfl
  rw [this]; exact h3.fderiv

theorem n1aΦ_fderiv_bound {L : ℝ} (hL : ∀ w : Euc d, ‖fderiv ℝ (n1aBump d) w‖ ≤ L) {ε : ℝ} (hε : 0 < ε)
    (z : Euc d) : ‖fderiv ℝ (n1aΦ (d := d) ε) z‖ ≤ L * ε⁻¹ := by
  rw [n1aΦ_fderiv_eq, norm_neg]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  have : ‖ε⁻¹ • ContinuousLinearMap.id ℝ (Euc d)‖ ≤ ε⁻¹ := by
    refine (norm_smul_le ε⁻¹ (ContinuousLinearMap.id ℝ (Euc d))).trans ?_
    rw [norm_inv, Real.norm_eq_abs, abs_of_pos hε]
    exact mul_le_of_le_one_right (inv_nonneg.2 hε.le) ContinuousLinearMap.norm_id_le
  exact mul_le_mul (hL _) this (norm_nonneg _) ((norm_nonneg _).trans (hL 0))

/-- The derivative of the cutoff vanishes inside `B(0,ε)`. -/
theorem n1aΦ_fderiv_zero_in {ε : ℝ} (hε : 0 < ε) {z : Euc d} (hz : ‖z‖ < ε) :
    fderiv ℝ (n1aΦ (d := d) ε) z = 0 := by
  have hev : n1aΦ (d := d) ε =ᶠ[𝓝 z] fun _ => 0 := by
    filter_upwards [isOpen_lt continuous_norm continuous_const |>.mem_nhds hz] with w hw
    exact n1aΦ_zero hε (le_of_lt hw)
  rw [hev.fderiv_eq]; simp

/-- The derivative of the cutoff vanishes outside `B̄(0,2ε)`. -/
theorem n1aΦ_fderiv_zero_out {ε : ℝ} (hε : 0 < ε) {z : Euc d} (hz : 2 * ε < ‖z‖) :
    fderiv ℝ (n1aΦ (d := d) ε) z = 0 := by
  have hev : n1aΦ (d := d) ε =ᶠ[𝓝 z] fun _ => 1 := by
    filter_upwards [isOpen_lt continuous_const continuous_norm |>.mem_nhds hz] with w hw
    exact n1aΦ_one hε (le_of_lt hw)
  rw [hev.fderiv_eq]; simp

end HRS.MS.UniqN1a
