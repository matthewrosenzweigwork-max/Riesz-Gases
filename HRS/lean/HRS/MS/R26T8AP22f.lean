import HRS.MS.R26T8AP22e
import HRS.MS.R26T8AP05a
import HRS.MD.DOMCalc

/-!
# S8.2 local Newton layer, packet T8A.P22 (part f): pointwise estimates for the leading inverse in the exponent `s' = 3d/4`
`r26t8a_p22_L_dom`: for `0 < |w| <= 2`, `|L_B w| <= C ‖B‖ |w|^(2-s')`, `‖∇ L_B w‖ <= C ‖B‖ |w|^(1-s')`, `|Δ L_B w| <= C ‖B‖ |w|^(-s')` (`s = d/2 < s' < d`).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ContDiff
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82N

namespace HRS.MS.R26T8A

variable {d : ℕ}

/-- The auxiliary exponent `s' = 3d/4`. -/
def r26t8a_p22_sp (d : ℕ) : ℝ := 3 * (d : ℝ) / 4

theorem r26t8a_p22_rpow_le {r a s' : ℝ} (hr : 0 < r) (hr2 : r ≤ 2) (ha : -s' ≤ a) :
    r ^ a ≤ 2 ^ (a + s') * r ^ (-s') := by
  have : r ^ a = r ^ (a + s') * r ^ (-s') := by rw [← Real.rpow_add hr]; congr 1; ring
  rw [this]
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hr.le hr2 (by linarith)) (Real.rpow_nonneg hr.le _)

theorem r26t8a_p22_L_dom (hd : 2 ≤ d) (nu : ℝ) (hnu : 0 < nu) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : Euc d →L[ℝ] Euc d →L[ℝ] ℝ), (∀ x y, B x y = B y x) → ∀ w : Euc d, w ≠ 0 → ‖w‖ ≤ 2 →
      |s82n_leadingInverse nu B w| ≤ C * ‖B‖ * ‖w‖ ^ (2 - r26t8a_p22_sp d) ∧
      ‖fderiv ℝ (s82n_leadingInverse nu B) w‖ ≤ C * ‖B‖ * ‖w‖ ^ (1 - r26t8a_p22_sp d) ∧
      |Laplacian.laplacian (s82n_leadingInverse nu B) w| ≤ C * ‖B‖ * ‖w‖ ^ (-r26t8a_p22_sp d) := by
  obtain ⟨C0, hC00, hC0⟩ := r26t8a_p22_L_bounds hd nu hnu
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  set s : ℝ := s82n_critS d with hs
  set s' : ℝ := r26t8a_p22_sp d with hsp
  have hss : s < s' := by simp only [hs, hsp, s82n_critS, r26t8a_p22_sp]; linarith
  have hs0 : 0 < s := by simp only [hs, s82n_critS]; positivity
  set K : ℝ := 2 ^ (s' - s) with hK
  have hK0 : 0 < K := by positivity
  refine ⟨(C0 * 7 * K + C0 * K + (s / (4 * nu)) * K + C0), by positivity, fun B hB w hw hw2 => ?_⟩
  obtain ⟨hv, hg⟩ := hC0 B w hw
  have hr : 0 < ‖w‖ := norm_pos_iff.2 hw
  have hnB : 0 ≤ ‖B‖ := ContinuousLinearMap.opNorm_nonneg B
  set r : ℝ := ‖w‖ with hrdef
  have hp1 : r ^ (2 - s) ≤ K * r ^ (2 - s') := by
    have : r ^ (2 - s) = r ^ (s' - s) * r ^ (2 - s') := by rw [← Real.rpow_add hr]; congr 1; ring
    rw [this]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hr.le hw2 (by linarith)) (Real.rpow_nonneg hr.le _)
  have hp2 : r ^ (1 - s) ≤ K * r ^ (1 - s') := by
    have : r ^ (1 - s) = r ^ (s' - s) * r ^ (1 - s') := by rw [← Real.rpow_add hr]; congr 1; ring
    rw [this]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hr.le hw2 (by linarith)) (Real.rpow_nonneg hr.le _)
  have hp3 : r ^ (-s) ≤ K * r ^ (-s') := by
    have : r ^ (-s) = r ^ (s' - s) * r ^ (-s') := by rw [← Real.rpow_add hr]; congr 1; ring
    rw [this]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hr.le hw2 (by linarith)) (Real.rpow_nonneg hr.le _)
  have hq : 0 ≤ r ^ (2 - s') := Real.rpow_nonneg hr.le _
  have hK1 : 1 ≤ K := Real.one_le_rpow (by norm_num) (by linarith)
  have hq0 : 0 ≤ r ^ (-s') := Real.rpow_nonneg hr.le _
  set Ctot : ℝ := C0 * 7 * K + C0 * K + (s / (4 * nu)) * K + C0 with hCtot
  have hCpos : 0 ≤ Ctot := by positivity
  refine ⟨?_, ?_, ?_⟩
  · by_cases hd4 : d = 4
    · have hs2 : s = 2 := by simp only [hs, s82n_critS]; rw [hd4]; norm_num
      have hs3 : s' = 3 := by simp only [hsp, r26t8a_p22_sp]; rw [hd4]; norm_num
      rw [if_pos hd4, hs2, sub_self, Real.rpow_zero] at hv
      have hr1 : r ^ (2 - s') = r⁻¹ := by
        rw [hs3, show (2 : ℝ) - 3 = -1 by norm_num, Real.rpow_neg_one]
      have hinv : (1 : ℝ) ≤ 2 * r⁻¹ := by
        have := inv_anti₀ hr hw2
        norm_num at this
        linarith
      have h1 := r26t8a_abs_log_le_inv hr hw2
      rw [Real.rpow_neg_one] at h1
      have h7 : 1 + |Real.log r| ≤ 7 * r⁻¹ := by linarith
      calc |s82n_leadingInverse nu B w| ≤ C0 * ‖B‖ * (1 + |Real.log r|) := hv
        _ ≤ C0 * ‖B‖ * (7 * r⁻¹) := mul_le_mul_of_nonneg_left h7 (by positivity)
        _ ≤ Ctot * ‖B‖ * r ^ (2 - s') := by
            rw [hr1]
            have hri : 0 ≤ r⁻¹ := inv_nonneg.2 hr.le
            have : 0 ≤ (C0 * 7 * (K - 1) + C0 * K + (s / (4 * nu)) * K + C0) * ‖B‖ * r⁻¹ := by
              have : 0 ≤ K - 1 := by linarith
              positivity
            nlinarith
    · rw [if_neg hd4, add_zero] at hv
      calc |s82n_leadingInverse nu B w| ≤ C0 * ‖B‖ * r ^ (2 - s) := hv
        _ ≤ C0 * ‖B‖ * (K * r ^ (2 - s')) := mul_le_mul_of_nonneg_left hp1 (by positivity)
        _ ≤ Ctot * ‖B‖ * r ^ (2 - s') := by
            have : 0 ≤ (C0 * 7 * K + (s / (4 * nu)) * K + C0) * ‖B‖ * r ^ (2 - s') := by positivity
            nlinarith [mul_nonneg (mul_nonneg hC00 hnB) (mul_nonneg hK0.le hq)]
  · calc ‖fderiv ℝ (s82n_leadingInverse nu B) w‖ ≤ C0 * ‖B‖ * r ^ (1 - s) := hg
      _ ≤ C0 * ‖B‖ * (K * r ^ (1 - s')) := mul_le_mul_of_nonneg_left hp2 (by positivity)
      _ ≤ Ctot * ‖B‖ * r ^ (1 - s') := by
          have hq1 : 0 ≤ r ^ (1 - s') := Real.rpow_nonneg hr.le _
          have : 0 ≤ (C0 * 7 * K + (s / (4 * nu)) * K + C0) * ‖B‖ * r ^ (1 - s') := by positivity
          nlinarith [mul_nonneg (mul_nonneg hC00 hnB) (mul_nonneg hK0.le hq1)]
  · have hlap := s82n_leading_laplacian hd nu hnu B hB w hw
    set om : Euc d := ‖w‖⁻¹ • w with homdef
    have hom : ‖om‖ = 1 := by
      simp only [homdef, norm_smul, norm_inv, norm_norm]; field_simp
    have hBo : |B om om| ≤ ‖B‖ := by
      have := B.le_opNorm₂ om om
      rw [hom] at this
      simpa using this
    have hΔ : Laplacian.laplacian (s82n_leadingInverse nu B) w = (s / (4 * nu)) * r ^ (-s) * B om om := by
      have hν : nu ≠ 0 := hnu.ne'
      field_simp
      linarith
    rw [hΔ, abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ s / (4 * nu)), abs_of_nonneg (Real.rpow_nonneg hr.le _)]
    calc s / (4 * nu) * r ^ (-s) * |B om om| ≤ s / (4 * nu) * r ^ (-s) * ‖B‖ :=
          mul_le_mul_of_nonneg_left hBo (by positivity)
      _ ≤ s / (4 * nu) * (K * r ^ (-s')) * ‖B‖ := by
          gcongr
      _ ≤ Ctot * ‖B‖ * r ^ (-s') := by
          have : 0 ≤ (C0 * 7 * K + C0 * K + C0) * ‖B‖ * r ^ (-s') := by positivity
          nlinarith

end HRS.MS.R26T8A
