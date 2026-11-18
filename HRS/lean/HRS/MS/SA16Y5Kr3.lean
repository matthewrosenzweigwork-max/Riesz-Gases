import HRS.MS.SA16Y5Kr2

/-!
# S.A.16 (SA16Y5) Kr3: `L^1` bound of the derivative of the far part, `∫ |V_i| ≤ Cf ε^{d-s-1}` for `s + 1 > d` (K1, part 3)
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA

section Kr3
variable {d : ℕ} {s : ℝ}

lemma sa16y5_V_meas (ε : ℝ) (i : Fin d) : Measurable (sa16y5_V d s ε i) := by
  unfold sa16y5_V rieszKernel
  have hc : Measurable (sa16z_chi d ε) := (sa16z_chi_smooth ε).continuous.measurable
  have hdc : Measurable (sa16z_dchi d ε i) := by
    unfold sa16z_dchi
    have h1 : Continuous (fun z : Euc d => deriv Real.smoothTransition (‖z‖ ^ 2 / ε ^ 2 - 1)) :=
      ((Real.smoothTransition.contDiff : ContDiff ℝ ∞ _).continuous_deriv (by simp)).comp (by fun_prop)
    exact h1.measurable.mul (by fun_prop)
  by_cases hs : s = 0
  · simp only [hs, if_true]
    exact ((sa16z_Kx_meas 0 i).mul hc).add (((measurable_norm.log).neg).mul hdc)
  · simp only [hs, if_false]
    exact ((sa16z_Kx_meas s i).mul hc).add ((measurable_norm.pow_const _).mul hdc)

lemma sa16y5_V_bound (hs : 0 < s) {M : ℝ} (hM : ∀ t, |deriv Real.smoothTransition t| ≤ M) {ε : ℝ} (hε : 0 < ε)
    (i : Fin d) (z : Euc d) :
    |sa16y5_V d s ε i z| ≤ (HRS.CZ.Hls.hlsg_c s + 4 * M) * (if ε ≤ ‖z‖ then ‖z‖ ^ (-(s + 1)) else 0) := by
  have hc := HRS.CZ.Hls.hlsg_c_nonneg hs.le
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  by_cases hz : ε ≤ ‖z‖
  · rw [if_pos hz]
    have hz0 : z ≠ 0 := by rintro rfl; simp at hz; linarith
    have hn : 0 < ‖z‖ := norm_pos_iff.2 hz0
    unfold sa16y5_V
    rw [sa16y5_riesz_eq hs]
    have h1 : |sa16z_Kx s i z * sa16z_chi d ε z| ≤ HRS.CZ.Hls.hlsg_c s * ‖z‖ ^ (-s - 1) := by
      rw [abs_mul, abs_of_nonneg (sa16z_chi_nonneg ε z)]
      calc |sa16z_Kx s i z| * sa16z_chi d ε z ≤ |sa16z_Kx s i z| * 1 :=
            mul_le_mul_of_nonneg_left (sa16z_chi_le_one ε z) (abs_nonneg _)
        _ ≤ _ := by rw [mul_one]; exact sa16z_Kx_bound hs.le i hz0
    have h2 : |‖z‖ ^ (-s) * sa16z_dchi d ε i z| ≤ 4 * M * ‖z‖ ^ (-s - 1) := by
      rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
      have h3 := sa16z_dchi_mul_norm_le hM hε i z
      have h4 : |sa16z_dchi d ε i z| ≤ 4 * M / ‖z‖ := by rw [le_div_iff₀ hn]; exact h3
      calc ‖z‖ ^ (-s) * |sa16z_dchi d ε i z| ≤ ‖z‖ ^ (-s) * (4 * M / ‖z‖) :=
            mul_le_mul_of_nonneg_left h4 (Real.rpow_nonneg (norm_nonneg _) _)
        _ = 4 * M * ‖z‖ ^ (-s - 1) := by
            rw [Real.rpow_sub hn, Real.rpow_one]
            field_simp
    have e : -(s + 1) = -s - 1 := by ring
    rw [e]
    calc _ ≤ |sa16z_Kx s i z * sa16z_chi d ε z| + |‖z‖ ^ (-s) * sa16z_dchi d ε i z| := abs_add_le _ _
      _ ≤ HRS.CZ.Hls.hlsg_c s * ‖z‖ ^ (-s - 1) + 4 * M * ‖z‖ ^ (-s - 1) := add_le_add h1 h2
      _ = _ := by ring
  · rw [if_neg hz, mul_zero]
    have hz' : ‖z‖ ≤ ε := (not_le.1 hz).le
    unfold sa16y5_V
    rw [sa16z_chi_zero hε hz', sa16z_dchi_zero hε i hz']
    simp

lemma sa16y5_far_ite_int (hd : 1 ≤ d) {t : ℝ} (htd : (d : ℝ) < t) {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun z : Euc d => if ε ≤ ‖z‖ then ‖z‖ ^ (-t) else 0) := by
  have h := integrable_one_add_norm (E := Euc d) (μ := volume) (r := t)
    (by rw [finrank_euclideanSpace_fin]; exact htd)
  refine (h.const_mul ((1 + 1 / ε) ^ t)).mono' ?_ (Eventually.of_forall fun z => ?_)
  · refine Measurable.aestronglyMeasurable ?_
    exact Measurable.ite (measurableSet_le measurable_const measurable_norm) (measurable_norm.pow_const _)
      measurable_const
  · rw [Real.norm_eq_abs]
    by_cases hz : ε ≤ ‖z‖
    · rw [if_pos hz, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
      have hn : 0 < ‖z‖ := hε.trans_le hz
      have h1 : 1 + ‖z‖ ≤ (1 + 1 / ε) * ‖z‖ := by
        have : 1 ≤ ‖z‖ / ε := by rw [le_div_iff₀ hε]; linarith
        calc 1 + ‖z‖ ≤ ‖z‖ / ε + ‖z‖ := by linarith
          _ = (1 + 1 / ε) * ‖z‖ := by field_simp; ring
      have ht0 : 0 ≤ t := by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
      calc ‖z‖ ^ (-t) = (‖z‖ ^ t)⁻¹ := Real.rpow_neg hn.le t
        _ ≤ (((1 + 1 / ε) ^ t) ⁻¹ * (1 + ‖z‖) ^ t)⁻¹ := by
            refine inv_anti₀ (by positivity) ?_
            have h2 : (1 + ‖z‖) ^ t ≤ ((1 + 1 / ε) * ‖z‖) ^ t := Real.rpow_le_rpow (by positivity) h1 ht0
            rw [Real.mul_rpow (by positivity) hn.le] at h2
            have h3 : 0 < (1 + 1 / ε) ^ t := by positivity
            rw [inv_mul_le_iff₀ h3]; linarith
        _ = (1 + 1 / ε) ^ t * (1 + ‖z‖) ^ (-t) := by
            rw [mul_inv, inv_inv, Real.rpow_neg (by positivity)]
    · rw [if_neg hz]; simp only [abs_zero]; positivity

theorem sa16y5_V_L1 (hd : 1 ≤ d) (hs : 0 < s) (hsd : (d : ℝ) < s + 1) :
    ∃ Cf : ℝ, 0 ≤ Cf ∧ ∀ ε : ℝ, 0 < ε → ∀ i : Fin d, Integrable (sa16y5_V d s ε i) ∧
      ∫ z, |sa16y5_V d s ε i z| ≤ Cf * ε ^ ((d : ℝ) - (s + 1)) := by
  obtain ⟨M, hM0, hM⟩ := sa16z_smoothTransition_deriv_bound
  have hc := HRS.CZ.Hls.hlsg_c_nonneg hs.le
  set C0 : ℝ := HRS.CZ.Hls.hlsg_c s + 4 * M with hC0
  have hC00 : 0 ≤ C0 := by positivity
  refine ⟨C0 * ((d : ℝ) * volume.real (ball (0 : Euc d) 1) * (1 / ((s + 1) - (d : ℝ)))), ?_, ?_⟩
  · have : 0 ≤ volume.real (ball (0 : Euc d) 1) := measureReal_nonneg
    have h2 : 0 < (s + 1) - (d : ℝ) := by linarith
    positivity
  · intro ε hε i
    have hI : Integrable (sa16y5_V d s ε i) :=
      ((sa16y5_far_ite_int hd hsd hε).const_mul C0).mono' (sa16y5_V_meas ε i).aestronglyMeasurable
        (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact sa16y5_V_bound hs hM hε i z)
    refine ⟨hI, ?_⟩
    calc ∫ z, |sa16y5_V d s ε i z| ≤ ∫ z : Euc d, C0 * (if ε ≤ ‖z‖ then ‖z‖ ^ (-(s + 1)) else 0) :=
          integral_mono hI.abs ((sa16y5_far_ite_int hd hsd hε).const_mul C0) (fun z => sa16y5_V_bound hs hM hε i z)
      _ = _ := by
          rw [integral_const_mul, sa16y5_radial_far hd hsd hε]
          have : (1 / ((s + 1) - (d : ℝ))) = 1 / (s + 1 - (d : ℝ)) := rfl
          field_simp

end Kr3

end HRS.Whole.AppendixA.Phase2SA16R
