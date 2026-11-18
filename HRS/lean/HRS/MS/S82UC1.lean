import HRS.MS.S82UB4
import HRS.MS.CritForceMom14

/-!
# S8.2 A01 (S82U): pole rows and integrability toolkit (no short-range kernel needed)
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.S82U
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82P2 HRS.MS.S82T HRS.MH.PairingRd

lemma u_pole_eq {d : ℕ} (x y : Euc d) : HRS.MS.S82N.s82n_pole x y = pole x y := rfl

lemma u_row_pole {d : ℕ} (hd : 2 ≤ d) {a Gc c : ℝ} (ha : 0 ≤ a) (hG : 0 ≤ Gc) (hc : 0 < c)
    {rho : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity rho) (hρG : HRS.Whole.HasR2GaussianUpper Gc c rho) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Euc d,
      ∫⁻ z, ENNReal.ofReal (jbracket z ^ a * pole x z) ∂(HRS.Whole.withDensityReal rho) ≤
        ENNReal.ofReal (C * jbracket x ^ a) := by
  set K := 4 ^ a * Gc * ((d : ℝ) * (volume : Measure (Euc d)).real (Metric.ball (0 : Euc d) 1) * (4 * 1)) +
    ((1 + (1 : ℝ) ^ (1 - HRS.MS.S82N.s82n_critS d)) * (1 + (1 : ℝ) ^ (-HRS.MS.S82N.s82n_critS d))) *
      HRS.MS.S82N.s82n_Mom d a Gc c with hK
  refine ⟨max K 0, le_max_right _ _, fun x => ?_⟩
  have h := HRS.MS.S82N.s82n_E2 hd a Gc c 1 ha hG hc one_pos le_rfl rho hρ hρG x
  refine le_trans (lintegral_mono fun z => ?_) (h.trans ?_)
  · refine ENNReal.ofReal_le_ofReal ?_
    have h1 : 1 ≤ 1 + HRS.MS.S82N.s82n_smallRadius x z ^ (1 - HRS.MS.S82N.s82n_critS d) := by
      have : 0 ≤ HRS.MS.S82N.s82n_smallRadius x z ^ (1 - HRS.MS.S82N.s82n_critS d) :=
        Real.rpow_nonneg (le_min zero_le_one (norm_nonneg _)) _
      linarith
    have h2 : 1 ≤ pole x z := u_pole_pos x z
    have h3 : 0 ≤ jbracket z ^ a := (u_jb_rpow_pos a z).le
    have e : HRS.MS.S82N.s82n_pole x z = pole x z := rfl
    rw [e]
    nlinarith [mul_nonneg h3 (sub_nonneg.2 h1), mul_nonneg (mul_nonneg h3 (sub_nonneg.2 h1)) (by linarith : (0:ℝ) ≤ pole x z)]
  · refine ENNReal.ofReal_le_ofReal ?_
    have := (u_jb_rpow_pos a x).le
    nlinarith [le_max_left K 0]

lemma u_lint_dens {d : ℕ} {rho : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity rho) {g : Euc d → ℝ}
    (hg : Measurable g) :
    ∫⁻ z, ENNReal.ofReal (rho z * g z) = ∫⁻ z, ENNReal.ofReal (g z) ∂(HRS.Whole.withDensityReal rho) := by
  unfold HRS.Whole.withDensityReal
  have hm : Measurable (fun z => ENNReal.ofReal (rho z)) := ENNReal.measurable_ofReal.comp hρ.measurable
  have key := lintegral_withDensity_eq_lintegral_mul (volume : Measure (Euc d)) hm
    (ENNReal.measurable_ofReal.comp hg)
  simp only [Function.comp_apply] at key
  rw [key]
  refine lintegral_congr fun z => ?_
  simp only [Pi.mul_apply, Function.comp_apply]
  rw [ENNReal.ofReal_mul (hρ.nonneg z)]

lemma u_int_of_lint {d : ℕ} {rho : Euc d → ℝ} {g : Euc d → ℝ} (hg : Measurable g) (h0 : ∀ z, 0 ≤ g z)
    (hfin : ∫⁻ z, ENNReal.ofReal (g z) ∂(HRS.Whole.withDensityReal rho) < ⊤) :
    Integrable g (HRS.Whole.withDensityReal rho) :=
  ⟨hg.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (Eventually.of_forall h0)).2 hfin⟩

lemma u_int_pole {d : ℕ} (hd : 2 ≤ d) {a Gc c : ℝ} (ha : 0 ≤ a) (hG : 0 ≤ Gc) (hc : 0 < c)
    {rho : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity rho) (hρG : HRS.Whole.HasR2GaussianUpper Gc c rho)
    (x : Euc d) :
    Integrable (fun z => jbracket z ^ a * pole x z) (HRS.Whole.withDensityReal rho) := by
  obtain ⟨C, hC, h⟩ := u_row_pole hd ha hG hc hρ hρG
  refine u_int_of_lint ((s82q_measurable_jb a).mul (s82q_measurable_pole x))
    (fun z => mul_nonneg (u_jb_rpow_pos a z).le (by linarith [u_pole_pos x z])) ?_
  exact lt_of_le_of_lt (h x) ENNReal.ofReal_lt_top

lemma u_int_triple {d : ℕ} (hd : 2 ≤ d) {a Gc c : ℝ} (ha : 0 ≤ a) (hG : 0 ≤ Gc) (hc : 0 < c)
    {rho : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity rho) (hρG : HRS.Whole.HasR2GaussianUpper Gc c rho)
    {x y : Euc d} (hxy : x ≠ y) :
    Integrable (fun z => jbracket z ^ a * triplePole x y z) (HRS.Whole.withDensityReal rho) := by
  have h1 := u_int_pole hd ha hG hc hρ hρG x
  have h2 := u_int_pole hd ha hG hc hρ hρG y
  have hb := (h1.add h2).const_mul ((1 + 2 ^ criticalS d) * pole x y)
  refine Integrable.mono' hb ((s82q_measurable_jb a).mul (s82q_measurable_triplePole x y)).aestronglyMeasurable
    (Eventually.of_forall fun z => ?_)
  have hj := (u_jb_rpow_pos a z).le
  have := s82q_triple_le hd x y z hxy
  have htp : 0 ≤ triplePole x y z := by linarith [u_tp_ge x y z |>.1, u_pole_pos x y]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hj htp)]
  calc jbracket z ^ a * triplePole x y z ≤ jbracket z ^ a * ((1 + 2 ^ criticalS d) * pole x y * (pole x z + pole y z)) :=
        mul_le_mul_of_nonneg_left this hj
    _ = ((1 + 2 ^ criticalS d) * pole x y) * ((fun z => jbracket z ^ a * pole x z) z + (fun z => jbracket z ^ a * pole y z) z) := by
        simp only; ring

end HRS.MS.S82U
