import HRS.MS.SA16Y3Sk1
import HRS.MS.MovDecAux1

/-!
# S.A.16 (SA16Y3) Hk1: skew-adjointness of `Q^i f = ∂_i (g ⋆ f)` on `C_c^∞` (packet P7, Hilbert corner)

`sa16y3_Q_skew`: `∫ f Q^i h = -∫ (Q^i f) h` for `f, h ∈ C_c^∞`, `0 ≤ s < d` (integration by parts and the symmetry of the
Riesz pairing).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.MS.MovDec

section Hk1
variable {d : ℕ} {s : ℝ}

lemma sa16y3_gb {f : Euc d → ℝ} (hf : IsCcInfty f) : Mov2eGB f := by
  refine ⟨hf.1.continuous, ?_⟩
  obtain ⟨R, hR⟩ := hf.2.isCompact.isBounded.subset_closedBall (0 : Euc d)
  obtain ⟨M, hM⟩ := hf.1.continuous.bounded_above_of_compact_support hf.2
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  refine ⟨M * Real.exp (R ^ 2), 1, by positivity, one_pos, fun x => ?_⟩
  by_cases hx : ‖x‖ ≤ R
  · have h1 : |f x| ≤ M := by simpa [Real.norm_eq_abs] using hM x
    have h2 : 1 ≤ Real.exp (R ^ 2 - ‖x‖ ^ 2) := by
      apply Real.one_le_exp
      have : 0 ≤ ‖x‖ := norm_nonneg _
      nlinarith
    calc |f x| ≤ M := h1
      _ ≤ M * Real.exp (R ^ 2 - ‖x‖ ^ 2) := le_mul_of_one_le_right hM0 h2
      _ = M * Real.exp (R ^ 2) * Real.exp (-1 * ‖x‖ ^ 2) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  · have : f x = 0 := by
      by_contra hne
      exact hx (by simpa using hR (subset_tsupport f (Function.mem_support.2 hne)))
    rw [this]; simp only [abs_zero]; positivity

theorem sa16y3_Q_skew (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {f h : Euc d → ℝ} (hf : IsCcInfty f)
    (hh : IsCcInfty h) (i : Fin d) :
    ∫ x, f x * sa16y3_Q s i h x = -∫ x, sa16y3_Q s i f x * h x := by
  have hG := sa16z_conv_smooth hs0 hsd hh
  have hf' : IsCcInfty (fun y => fderiv ℝ f y (sa16z_e i)) := sa16s_cc_fderiv hf _
  have hGd : ContDiff ℝ ∞ (fun x => fderiv ℝ (convFun (rieszKernel d s) h) x (sa16z_e i)) :=
    sa16so_dir_smooth hG _
  have e1 : ∫ x, f x * fderiv ℝ (convFun (rieszKernel d s) h) x (sa16z_e i) =
      -∫ x, fderiv ℝ f x (sa16z_e i) * convFun (rieszKernel d s) h x := by
    refine integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable ?_ ?_ ?_
      (fun x _ => hf.1.differentiable (by simp) x) (fun x _ => hG.differentiable (by simp) x)
    · exact (hf'.1.continuous.mul (hG.continuous)).integrable_of_hasCompactSupport hf'.2.mul_right
    · exact (hf.1.continuous.mul hGd.continuous).integrable_of_hasCompactSupport hf.2.mul_right
    · exact (hf.1.continuous.mul hG.continuous).integrable_of_hasCompactSupport hf.2.mul_right
  have e2 : ∫ x, fderiv ℝ f x (sa16z_e i) * convFun (rieszKernel d s) h x =
      ∫ x, h x * convFun (rieszKernel d s) (fun y => fderiv ℝ f y (sa16z_e i)) x := by
    rw [← mov2ePairF_eq_iter hd hs0 hsd (sa16y3_gb hf') (sa16y3_gb hh), mov2ePairF_symm,
      mov2ePairF_eq_iter hd hs0 hsd (sa16y3_gb hh) (sa16y3_gb hf')]
  unfold sa16y3_Q
  rw [e1, e2]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [sa16z_conv_fderiv hs0 hsd hf]
  ring

end Hk1

end HRS.Whole.AppendixA.Phase2SA16R
