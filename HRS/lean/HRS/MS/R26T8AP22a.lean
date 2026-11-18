import HRS.MS.CritForceLead4
import HRS.MS.R26T8AP14

/-!
# S8.2 local Newton layer, packet T8A.P22 (part a): the leading inverse as a function of `B`
Linearity in `B`, smoothness away from `0`, homogeneity under `z |-> lambda z`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ContDiff
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82N

namespace HRS.MS.R26T8A

variable {d : ℕ}

theorem r26t8a_p22_L_add (nu : ℝ) (B1 B2 : Euc d →L[ℝ] Euc d →L[ℝ] ℝ) (z : Euc d) :
    s82n_leadingInverse nu (B1 + B2) z = s82n_leadingInverse nu B1 z + s82n_leadingInverse nu B2 z := by
  unfold s82n_leadingInverse
  simp only [ContinuousLinearMap.add_apply, Finset.sum_add_distrib, add_div]
  split_ifs <;> ring

theorem r26t8a_p22_L_smul (nu c : ℝ) (B : Euc d →L[ℝ] Euc d →L[ℝ] ℝ) (z : Euc d) :
    s82n_leadingInverse nu (c • B) z = c * s82n_leadingInverse nu B z := by
  unfold s82n_leadingInverse
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  split_ifs <;> ring

theorem r26t8a_p22_L_contDiffAt (nu : ℝ) (B : Euc d →L[ℝ] Euc d →L[ℝ] ℝ) {z : Euc d} (hz : z ≠ 0) :
    ContDiffAt ℝ ∞ (s82n_leadingInverse nu B) z := by
  have hn : ContDiffAt ℝ ∞ (fun x : Euc d => ‖x‖) z := contDiffAt_norm ℝ hz
  have hn0 : ‖z‖ ≠ 0 := (norm_pos_iff.2 hz).ne'
  have hrp : ∀ p : ℝ, ContDiffAt ℝ ∞ (fun x : Euc d => ‖x‖ ^ p) z := fun p => hn.rpow_const_of_ne hn0
  have hlog : ContDiffAt ℝ ∞ (fun x : Euc d => Real.log ‖x‖) z := hn.log hn0
  have hom : ContDiffAt ℝ ∞ (fun x : Euc d => ‖x‖⁻¹ • x) z := (hn.inv hn0).smul contDiffAt_id
  have hq : ContDiffAt ℝ ∞ (fun x : Euc d => B (‖x‖⁻¹ • x) (‖x‖⁻¹ • x)) z :=
    ((B.contDiff.contDiffAt).comp z hom).clm_apply hom
  unfold s82n_leadingInverse
  simp only
  split_ifs
  · exact ((contDiffAt_const.mul hlog).div_const _).sub (((hq.sub contDiffAt_const).mul (hrp _)).div_const _)
  · exact ((contDiffAt_const.mul (hrp _)).div_const _).sub (((hq.sub contDiffAt_const).mul (hrp _)).div_const _)

theorem r26t8a_p22_omega_smul {z : Euc d} (hz : z ≠ 0) {t : ℝ} (ht : 0 < t) :
    ‖t • z‖⁻¹ • (t • z) = ‖z‖⁻¹ • z := by
  have hzn : ‖z‖ ≠ 0 := (norm_pos_iff.2 hz).ne'
  rw [norm_smul, Real.norm_of_nonneg ht.le, smul_smul]
  congr 1
  field_simp

theorem r26t8a_p22_L_hom_ne (nu : ℝ) (B : Euc d →L[ℝ] Euc d →L[ℝ] ℝ) (hd4 : d ≠ 4) {z : Euc d} (hz : z ≠ 0)
    {t : ℝ} (ht : 0 < t) :
    s82n_leadingInverse nu B (t • z) = t ^ (2 - s82n_critS d) * s82n_leadingInverse nu B z := by
  have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz
  unfold s82n_leadingInverse
  simp only [r26t8a_p22_omega_smul hz ht]
  simp only [norm_smul, Real.norm_of_nonneg ht.le, Real.mul_rpow ht.le hzn.le, if_neg hd4]
  ring

theorem r26t8a_p22_L_hom_four (nu : ℝ) (B : Euc d →L[ℝ] Euc d →L[ℝ] ℝ) (hd4 : d = 4) {z : Euc d} (hz : z ≠ 0)
    {t : ℝ} (ht : 0 < t) :
    s82n_leadingInverse nu B (t • z) = s82n_leadingInverse nu B z +
      (∑ i : Fin d, B (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) / d * Real.log t / (4 * nu) := by
  have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hs : s82n_critS d = 2 := by unfold s82n_critS; rw [hd4]; norm_num
  unfold s82n_leadingInverse
  simp only [r26t8a_p22_omega_smul hz ht]
  simp only [norm_smul, Real.norm_of_nonneg ht.le, if_pos hd4, hs, Real.log_mul ht.ne' hzn.ne']
  norm_num
  ring

end HRS.MS.R26T8A
