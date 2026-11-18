import HRS.MS.R26T8AA01c
import HRS.MS.R26T8AP11g15
import HRS.MS.R26T8AP11g3

/-!
# S8.2 T8A A01 (part d): integrability of the pole envelope against the thermal measure
`r26t8a_a01_pole_int`: `z ↦ jb(z)^M' * pole x z` is `ρ dz`-integrable; `r26t8a_a01_pole_prod`: for `x ≠ y`,
`pole x z * pole y z ≤ c0 (pole x z + pole y z)`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_a01_pole_prod {x y : Euc d} (hxy : x ≠ y) (hs : 0 < criticalS d) :
    ∃ c0 : ℝ, 0 ≤ c0 ∧ ∀ z : Euc d, pole x z * pole y z ≤ c0 * (pole x z + pole y z) := by
  have hn : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy)
  set r0 : ℝ := min 1 (‖x - y‖ / 2) with hr0
  have hr0pos : 0 < r0 := lt_min zero_lt_one (by positivity)
  refine ⟨1 + r0 ^ (-criticalS d), by have := Real.rpow_nonneg hr0pos.le (-criticalS d); linarith, fun z => ?_⟩
  have key : ∀ (u : Euc d), ‖u - z‖ ≥ ‖x - y‖ / 2 → pole u z ≤ 1 + r0 ^ (-criticalS d) := by
    intro u hu
    unfold pole smallRadius
    have h1 : r0 ≤ min 1 ‖u - z‖ := min_le_min le_rfl hu
    have := Real.rpow_le_rpow_of_nonpos hr0pos h1 (by linarith : -criticalS d ≤ 0)
    linarith
  have hxz : 0 ≤ pole x z := by linarith [r26t8a_a01_pole_ge_one x z]
  have hyz : 0 ≤ pole y z := by linarith [r26t8a_a01_pole_ge_one y z]
  by_cases h : ‖x - z‖ ≥ ‖x - y‖ / 2
  · have := key x h
    nlinarith [mul_le_mul_of_nonneg_right this hyz]
  · push Not at h
    have h2 : ‖y - z‖ ≥ ‖x - y‖ / 2 := by
      have := norm_sub_le_norm_sub_add_norm_sub x z y
      have h3 : ‖z - y‖ = ‖y - z‖ := norm_sub_rev _ _
      linarith
    have := key y h2
    nlinarith [mul_le_mul_of_nonneg_right this hxz]

theorem r26t8a_a01_pole_int (hd : 2 ≤ d) {M' : ℝ} (hM' : 0 ≤ M') {a β : ℝ} (ha : 0 < a) (hβ : 0 < β)
    {rho : Euc d → ℝ} (hrho : IsThermalEquilibrium d (criticalS d) a β rho) (x : Euc d) :
    Integrable (fun z => jbracket z ^ M' * pole x z) (HRS.Whole.withDensityReal rho) := by
  have hdd : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < criticalS d := by unfold criticalS; linarith
  have hsd : criticalS d < d := by unfold criticalS; linarith
  obtain ⟨hdiff, C, c, hC, hc, hb⟩ := HRS.MS.Wad.s84_thermal_gaussReg hd ha hβ hrho
  have hρs : ContDiff ℝ ∞ rho :=
    (HRS.MS.Mov0.mv0_hgauss hd hs0.le hsd ha hβ hrho).1
  have hprob : HRS.Whole.IsProbDensity rho := hrho.1.1
  have hrho0 : ∀ x, 0 ≤ rho x := hprob.nonneg
  obtain ⟨Cp, hCp0, hCp⟩ := r26t8a_p10a_poly_gauss M' hc
  set a' : Euc d → ℝ := fun y => rho y * jbracket y ^ M' with ha'
  have ha'0 : ∀ y, 0 ≤ a' y := fun y => mul_nonneg (hrho0 y) (Real.rpow_nonneg (s83_jb_pos y).le _)
  have ha'c : Continuous a' := hρs.continuous.mul (s85_jb_rpow_continuous M')
  have ha'b : ∀ y, a' y ≤ C * Cp * Real.exp (-(c / 2) * ‖y‖ ^ 2) := by
    intro y
    have h1 : jbracket y ^ M' ≤ (1 + ‖y‖) ^ M' :=
      Real.rpow_le_rpow (s83_jb_pos y).le (s83_jb_le_one_add y) hM'
    have h2 := hCp ‖y‖ (norm_nonneg _)
    have h3 : rho y ≤ C * Real.exp (-c * ‖y‖ ^ 2) := (le_abs_self _).trans (hb y).1
    calc a' y = rho y * jbracket y ^ M' := rfl
      _ ≤ (C * Real.exp (-c * ‖y‖ ^ 2)) * (1 + ‖y‖) ^ M' :=
          mul_le_mul h3 h1 (Real.rpow_nonneg (s83_jb_pos y).le _) (by positivity)
      _ = C * ((1 + ‖y‖) ^ M' * Real.exp (-c * ‖y‖ ^ 2)) := by ring
      _ ≤ C * (Cp * Real.exp (-(c / 2) * ‖y‖ ^ 2)) := mul_le_mul_of_nonneg_left h2 hC
      _ = _ := by ring
  have hKa : ∀ y, a' y ≤ C * Cp := fun y => by
    refine (ha'b y).trans ?_
    have : Real.exp (-(c / 2) * ‖y‖ ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖y‖])
    have h0 : 0 ≤ C * Cp := by positivity
    nlinarith
  have ha'i : Integrable a' := by
    refine Integrable.mono' ((r26t8a_p10a_gauss_int (d := d) (b := c / 2) (by linarith)).const_mul (C * Cp))
      ha'c.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_of_nonneg (ha'0 y)]; exact ha'b y
  obtain ⟨Ω, hΩ0, hΩ⟩ := r26t8a_f25_conv_bound hd hs0 hsd
  obtain ⟨hI, -⟩ := hΩ a' (C * Cp) ha'0 hKa ha'c ha'i x
  rw [r26t8a_f25_wd_integrable hprob]
  have hmeas : AEStronglyMeasurable (fun z => rho z * (jbracket z ^ M' * pole x z)) volume := by
    have h1 : Continuous fun z : Euc d => rho z * jbracket z ^ M' := ha'c
    have h2 : Measurable (fun z : Euc d => pole x z) := by
      unfold pole smallRadius
      exact measurable_const.add (((measurable_const.min (measurable_const.sub measurable_id).norm)).pow_const _)
    have : AEStronglyMeasurable (fun z => (rho z * jbracket z ^ M') * pole x z) volume :=
      (h1.aestronglyMeasurable (μ := volume)).mul (h2.aestronglyMeasurable (μ := volume))
    refine this.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only; ring
  refine Integrable.mono' (hI.const_mul 2) hmeas (Filter.Eventually.of_forall fun z => ?_)
  have hp0 : 0 ≤ pole x z := by linarith [r26t8a_a01_pole_ge_one x z]
  rw [Real.norm_of_nonneg (mul_nonneg (hrho0 z) (mul_nonneg (Real.rpow_nonneg (s83_jb_pos z).le _) hp0))]
  have hpb : pole x z ≤ 2 * (1 + ‖x - z‖ ^ (-criticalS d)) := by
    unfold pole smallRadius
    by_cases h1 : 1 ≤ ‖x - z‖
    · rw [min_eq_left h1, Real.one_rpow]
      have := Real.rpow_nonneg (norm_nonneg (x - z)) (-criticalS d); linarith
    · push Not at h1
      rw [min_eq_right h1.le]
      have := Real.rpow_nonneg (norm_nonneg (x - z)) (-criticalS d); linarith
  calc rho z * (jbracket z ^ M' * pole x z) = a' z * pole x z := by rw [ha']; ring
    _ ≤ a' z * (2 * (1 + ‖x - z‖ ^ (-criticalS d))) := mul_le_mul_of_nonneg_left hpb (ha'0 z)
    _ = 2 * (a' z * (1 + ‖x - z‖ ^ (-criticalS d))) := by ring

end HRS.MS.R26T8A
