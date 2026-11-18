import HRS.MS.SA16ZP1
import HRS.MS.CzHlsAux2

/-!
# S.A.16 (SA16Z) T1: a smooth radial cutoff around the origin (for `∂_i (g ⋆ f) = -c_s pvOdd f`)

`sa16z_chi ε z = smoothTransition (|z|²/ε² - 1)`: vanishes for `|z| ≤ ε`, equals `1` for `|z|² ≥ 2ε²`, is even and smooth;
`sa16z_dchi ε i z = ∂_i χ_ε z` is odd and `|∂_i χ_ε z| |z| ≤ 4 M` (`M` bound of `smoothTransition'`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution RealInnerProductSpace

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section T1
variable {d : ℕ}

/-- the radial cutoff -/
def sa16z_chi (d : ℕ) (ε : ℝ) (z : Euc d) : ℝ := Real.smoothTransition (‖z‖ ^ 2 / ε ^ 2 - 1)

lemma sa16z_chi_zero {ε : ℝ} (hε : 0 < ε) {z : Euc d} (hz : ‖z‖ ≤ ε) : sa16z_chi d ε z = 0 := by
  unfold sa16z_chi
  refine Real.smoothTransition.zero_of_nonpos ?_
  have : ‖z‖ ^ 2 ≤ ε ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hz 2
  have h2 : ‖z‖ ^ 2 / ε ^ 2 ≤ 1 := (div_le_one (by positivity)).2 this
  linarith

lemma sa16z_chi_one {ε : ℝ} (hε : 0 < ε) {z : Euc d} (hz : 2 * ε ^ 2 ≤ ‖z‖ ^ 2) : sa16z_chi d ε z = 1 := by
  unfold sa16z_chi
  refine Real.smoothTransition.one_of_one_le ?_
  have : 2 ≤ ‖z‖ ^ 2 / ε ^ 2 := by rw [le_div_iff₀ (by positivity)]; linarith
  linarith

lemma sa16z_chi_neg (ε : ℝ) (z : Euc d) : sa16z_chi d ε (-z) = sa16z_chi d ε z := by
  simp [sa16z_chi, norm_neg]

lemma sa16z_chi_nonneg (ε : ℝ) (z : Euc d) : 0 ≤ sa16z_chi d ε z := Real.smoothTransition.nonneg _

lemma sa16z_chi_le_one (ε : ℝ) (z : Euc d) : sa16z_chi d ε z ≤ 1 := Real.smoothTransition.le_one _

lemma sa16z_chi_smooth (ε : ℝ) : ContDiff ℝ ∞ (sa16z_chi d ε) := by
  unfold sa16z_chi
  exact Real.smoothTransition.contDiff.comp ((contDiff_norm_sq ℝ).div_const _ |>.sub contDiff_const)

lemma sa16z_chi_hasFDerivAt (ε : ℝ) (z : Euc d) :
    HasFDerivAt (sa16z_chi d ε)
      ((deriv Real.smoothTransition (‖z‖ ^ 2 / ε ^ 2 - 1) * (2 / ε ^ 2)) • innerSL ℝ z) z := by
  have h1 : HasFDerivAt (fun y : Euc d => ‖y‖ ^ 2 / ε ^ 2 - 1) ((2 / ε ^ 2) • innerSL ℝ z) z := by
    have h := ((hasStrictFDerivAt_norm_sq z).hasFDerivAt.const_smul (1 / ε ^ 2)).sub_const 1
    convert h using 1
    · funext y; simp; ring
    · ext v; simp [innerSL_apply_apply]; ring
  have h2 := (Real.smoothTransition.contDiff : ContDiff ℝ ∞ _).differentiable (by simp)
    (‖z‖ ^ 2 / ε ^ 2 - 1)
  have := h2.hasDerivAt.comp_hasFDerivAt z h1
  unfold sa16z_chi
  rw [mul_smul]
  exact this

/-- `∂_i χ_ε (z)` -/
def sa16z_dchi (d : ℕ) (ε : ℝ) (i : Fin d) (z : Euc d) : ℝ :=
  deriv Real.smoothTransition (‖z‖ ^ 2 / ε ^ 2 - 1) * (2 * z i / ε ^ 2)

lemma sa16z_dchi_eq (ε : ℝ) (i : Fin d) (z : Euc d) :
    fderiv ℝ (sa16z_chi d ε) z (EuclideanSpace.single i (1 : ℝ)) = sa16z_dchi d ε i z := by
  rw [(sa16z_chi_hasFDerivAt ε z).fderiv]
  simp [sa16z_dchi, innerSL_apply_apply, EuclideanSpace.inner_single_right]
  ring

lemma sa16z_dchi_neg (ε : ℝ) (i : Fin d) (z : Euc d) : sa16z_dchi d ε i (-z) = -sa16z_dchi d ε i z := by
  simp [sa16z_dchi, norm_neg]
  ring

lemma sa16z_st_deriv_zero_of_nonpos {t : ℝ} (ht : t ≤ 0) : deriv Real.smoothTransition t = 0 := by
  rcases lt_or_eq_of_le ht with hlt | rfl
  · have : Real.smoothTransition =ᶠ[𝓝 t] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds hlt] with y hy
      exact Real.smoothTransition.zero_of_nonpos (le_of_lt hy)
    rw [this.deriv_eq]; simp
  · have hmin : IsLocalMin Real.smoothTransition 0 := by
      refine Filter.Eventually.of_forall fun y => ?_
      rw [Real.smoothTransition.zero]; exact Real.smoothTransition.nonneg y
    exact hmin.deriv_eq_zero

lemma sa16z_st_deriv_zero_of_one_le {t : ℝ} (ht : 1 ≤ t) : deriv Real.smoothTransition t = 0 := by
  rcases lt_or_eq_of_le ht with hlt | rfl
  · have : Real.smoothTransition =ᶠ[𝓝 t] fun _ => 1 := by
      filter_upwards [Ioi_mem_nhds hlt] with y hy
      exact Real.smoothTransition.one_of_one_le (le_of_lt hy)
    rw [this.deriv_eq]; simp
  · have hmax : IsLocalMax Real.smoothTransition 1 := by
      refine Filter.Eventually.of_forall fun y => ?_
      rw [Real.smoothTransition.one]; exact Real.smoothTransition.le_one y
    exact hmax.deriv_eq_zero

lemma sa16z_dchi_zero {ε : ℝ} (hε : 0 < ε) (i : Fin d) {z : Euc d} (hz : ‖z‖ ≤ ε) : sa16z_dchi d ε i z = 0 := by
  unfold sa16z_dchi
  have h2 : ‖z‖ ^ 2 ≤ ε ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hz 2
  have h3 : ‖z‖ ^ 2 / ε ^ 2 ≤ 1 := (div_le_one (by positivity)).2 h2
  rw [sa16z_st_deriv_zero_of_nonpos (by linarith), zero_mul]

lemma sa16z_smoothTransition_deriv_bound : ∃ M : ℝ, 0 ≤ M ∧ ∀ t, |deriv Real.smoothTransition t| ≤ M := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff : ContDiff ℝ ∞ _).continuous_deriv (by simp)
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun t => ?_⟩
  by_cases ht : t ∈ Icc (0 : ℝ) 1
  · have := hM t ht; rw [Real.norm_eq_abs] at this; exact this.trans (le_max_left _ _)
  · rcases not_and_or.1 ht with h | h
    · rw [sa16z_st_deriv_zero_of_nonpos (not_le.1 h).le]; simp
    · rw [sa16z_st_deriv_zero_of_one_le (not_le.1 h).le]; simp

/-- `|∂_i χ_ε(z)| |z| ≤ 4 M` -/
lemma sa16z_dchi_mul_norm_le {M : ℝ} (hM : ∀ t, |deriv Real.smoothTransition t| ≤ M) {ε : ℝ} (hε : 0 < ε)
    (i : Fin d) (z : Euc d) : |sa16z_dchi d ε i z| * ‖z‖ ≤ 4 * M := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  by_cases hz : ‖z‖ ^ 2 < 2 * ε ^ 2
  · unfold sa16z_dchi
    rw [abs_mul, abs_div, abs_mul]
    have hzi : |z i| ≤ ‖z‖ := by
      calc |z i| = ‖z i‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖z‖ := PiLp.norm_apply_le z i
    have h1 : |2| * |z i| / |ε ^ 2| * ‖z‖ ≤ 2 * ‖z‖ * ‖z‖ / ε ^ 2 := by
      rw [abs_of_pos (by positivity : (0 : ℝ) < ε ^ 2)]
      have : (|2| : ℝ) = 2 := abs_of_pos (by norm_num)
      rw [this, div_mul_eq_mul_div]
      gcongr
    have h2 : 2 * ‖z‖ * ‖z‖ / ε ^ 2 ≤ 4 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    calc |deriv Real.smoothTransition (‖z‖ ^ 2 / ε ^ 2 - 1)| * (|2| * |z i| / |ε ^ 2|) * ‖z‖
        = |deriv Real.smoothTransition (‖z‖ ^ 2 / ε ^ 2 - 1)| * (|2| * |z i| / |ε ^ 2| * ‖z‖) := by ring
      _ ≤ M * 4 := mul_le_mul (hM _) (h1.trans h2) (by positivity) hM0
      _ = 4 * M := by ring
  · have h2 : 1 ≤ ‖z‖ ^ 2 / ε ^ 2 - 1 := by
      have : 2 ≤ ‖z‖ ^ 2 / ε ^ 2 := by rw [le_div_iff₀ (by positivity)]; linarith [not_lt.1 hz]
      linarith
    unfold sa16z_dchi
    rw [sa16z_st_deriv_zero_of_one_le h2]
    simp; positivity

end T1

end HRS.Whole.AppendixA.Phase2SA16R
