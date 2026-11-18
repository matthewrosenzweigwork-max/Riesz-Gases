import HRS.MS.R26T8AC07f
import HRS.MS.R26T8AO00d

/-!
# S8.2 observed-time layer, packet T8A.C07: critical twofold and threefold convolution envelopes

Twofold bound from C07c (`∫⁻ ρ q(x-z) q(z-y) ≤ C(1+|log min(1,‖x-y‖)|)`), threefold bound by integrating it against `q(x-z)ρ(z)`
(C07f).  The real integrals are bounded through their lintegrals (a non-integrable integrand has integral `0`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

theorem r26t8a_c07_int_le {α : Type*} [MeasurableSpace α] {ν : Measure α} {f : α → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) {B : ℝ} (hB : 0 ≤ B) (h : ∫⁻ x, ENNReal.ofReal (f x) ∂ν ≤ ENNReal.ofReal B) :
    ∫ x, f x ∂ν ≤ B := by
  by_cases hi : Integrable f ν
  · rw [← ENNReal.ofReal_le_ofReal_iff hB, ofReal_integral_eq_lintegral_ofReal hi
      (Eventually.of_forall hf0)]
    exact h
  · rw [integral_undef hi]; exact hB

theorem r26t8a_c07_ofReal_integral_le {α : Type*} [MeasurableSpace α] {ν : Measure α} {f : α → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) : ENNReal.ofReal (∫ x, f x ∂ν) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂ν := by
  by_cases hi : Integrable f ν
  · rw [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall hf0)]
  · rw [integral_undef hi]; simp

theorem r26t8a_critical_convolution (d : ℕ) (hd : 2 ≤ d) (q : Euc d → ℝ)
    (hq : ShortRangePole d q) (G c : ℝ) (hG : 0 < G) (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ rho : Euc d → ℝ, HRS.Whole.IsProbDensity rho →
      HRS.Whole.HasR2GaussianUpper G c rho →
      (∀ x y, x ≠ y → ∫ z, q (x-z)*q (z-y) ∂HRS.Whole.withDensityReal rho ≤
        C*(1+|Real.log (min 1 ‖x-y‖)|)) ∧
      (∀ x y, ∫ z, ∫ w, q (x-z)*q (z-w)*q (w-y)
        ∂HRS.Whole.withDensityReal rho ∂HRS.Whole.withDensityReal rho ≤ C) := by
  classical
  obtain ⟨C2, hC2, H2⟩ := r26t8a_c07c_twofold d hd q hq G hG
  obtain ⟨C3, hC3, H3⟩ := r26t8a_c07f_outer d hd q hq G hG
  refine ⟨C2 + C2 * C3, by positivity, ?_⟩
  intro rho hrho hGauss
  have hρG : ∀ y, rho y ≤ G := fun y => by
    have h1 := hGauss.2 y
    have h2 : Real.exp (-c * ‖y‖ ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [norm_nonneg y])
    nlinarith [Real.exp_pos (-c * ‖y‖ ^ 2)]
  haveI hprob : IsProbabilityMeasure (HRS.Whole.withDensityReal rho) :=
    HRS.Whole.Q09A.measure_isProb hrho
  have hρm : Measurable rho := hrho.measurable
  have hρE : Measurable fun y : Euc d => ENNReal.ofReal (rho y) := ENNReal.measurable_ofReal.comp hρm
  have hqm : Measurable q := hq.measurable
  have hq0 : ∀ u, 0 ≤ q u := hq.nonneg
  have hwd : ∀ g : Euc d → ℝ≥0∞, Measurable g →
      ∫⁻ z, g z ∂HRS.Whole.withDensityReal rho = ∫⁻ z, ENNReal.ofReal (rho z) * g z := fun g hg => by
    show ∫⁻ z, g z ∂(volume.withDensity fun y => ENNReal.ofReal (rho y)) = _
    exact lintegral_withDensity_eq_lintegral_mul volume hρE hg
  constructor
  · intro x y hxy
    refine r26t8a_c07_int_le (fun z => mul_nonneg (hq0 _) (hq0 _)) (by positivity) ?_
    have hm : Measurable fun z : Euc d => ENNReal.ofReal (q (x - z) * q (z - y)) :=
      ENNReal.measurable_ofReal.comp
        ((hqm.comp (measurable_const.sub measurable_id)).mul (hqm.comp (measurable_id.sub_const y)))
    rw [hwd _ hm]
    refine (H2 rho hrho hρG x y hxy).trans (ENNReal.ofReal_le_ofReal ?_)
    have hL : 0 ≤ |Real.log (min 1 ‖x - y‖)| := abs_nonneg _
    nlinarith [mul_nonneg hC2 hL, mul_nonneg (mul_nonneg hC2 hC3) hL]
  · intro x y
    set F : Euc d → ℝ := fun z => ∫ w, q (x - z) * q (z - w) * q (w - y)
      ∂HRS.Whole.withDensityReal rho with hF
    have hF0 : ∀ z, 0 ≤ F z := fun z => integral_nonneg fun w =>
      mul_nonneg (mul_nonneg (hq0 _) (hq0 _)) (hq0 _)
    have hFm : Measurable F := by
      have hmeas : Measurable fun p : Euc d × Euc d => q (x - p.1) * q (p.1 - p.2) * q (p.2 - y) :=
        ((hqm.comp (measurable_const.sub measurable_fst)).mul
          (hqm.comp (measurable_fst.sub measurable_snd))).mul
          (hqm.comp (measurable_snd.sub_const y))
      exact (hmeas.stronglyMeasurable.integral_prod_right' (ν := HRS.Whole.withDensityReal rho)).measurable
    refine r26t8a_c07_int_le hF0 (by positivity) ?_
    have hFm' : Measurable fun z : Euc d => ENNReal.ofReal (F z) := ENNReal.measurable_ofReal.comp hFm
    rw [hwd _ hFm']
    have hne : ∀ᵐ z ∂(volume : Measure (Euc d)), z ≠ y := by
      have hd1 : 1 ≤ d := by omega
      haveI : Nonempty (Fin d) := ⟨⟨0, hd1⟩⟩
      rw [ae_iff]; simp
    have hpt : ∀ᵐ z ∂(volume : Measure (Euc d)),
        ENNReal.ofReal (rho z) * ENNReal.ofReal (F z) ≤ ENNReal.ofReal C2 * (ENNReal.ofReal (rho z) *
          (ENNReal.ofReal (q (x - z)) * ENNReal.ofReal (1 + |Real.log (min 1 ‖z - y‖)|))) := by
      filter_upwards [hne] with z hz
      have hin := H2 rho hrho hρG z y hz
      have hinm : Measurable fun w : Euc d => ENNReal.ofReal (q (z - w) * q (w - y)) :=
        ENNReal.measurable_ofReal.comp
          ((hqm.comp (measurable_const.sub measurable_id)).mul (hqm.comp (measurable_id.sub_const y)))
      have hFz : F z = q (x - z) * ∫ w, q (z - w) * q (w - y) ∂HRS.Whole.withDensityReal rho := by
        simp only [hF]
        rw [← integral_const_mul]
        exact integral_congr_ae (Eventually.of_forall fun w => by ring)
      have h1 : ENNReal.ofReal (F z) ≤ ENNReal.ofReal (q (x - z)) *
          ENNReal.ofReal (C2 * (1 + |Real.log (min 1 ‖z - y‖)|)) := by
        rw [hFz, ENNReal.ofReal_mul (hq0 _)]
        refine mul_le_mul' le_rfl ?_
        refine (r26t8a_c07_ofReal_integral_le (fun w => mul_nonneg (hq0 _) (hq0 _))).trans ?_
        rw [hwd _ hinm]
        exact hin
      calc ENNReal.ofReal (rho z) * ENNReal.ofReal (F z)
          ≤ ENNReal.ofReal (rho z) * (ENNReal.ofReal (q (x - z)) *
              ENNReal.ofReal (C2 * (1 + |Real.log (min 1 ‖z - y‖)|))) := mul_le_mul' le_rfl h1
        _ = ENNReal.ofReal C2 * (ENNReal.ofReal (rho z) *
          (ENNReal.ofReal (q (x - z)) * ENNReal.ofReal (1 + |Real.log (min 1 ‖z - y‖)|))) := by
            rw [ENNReal.ofReal_mul hC2]; ring
    have hmo : Measurable fun z : Euc d => ENNReal.ofReal (rho z) *
        (ENNReal.ofReal (q (x - z)) * ENNReal.ofReal (1 + |Real.log (min 1 ‖z - y‖)|)) :=
      hρE.mul ((ENNReal.measurable_ofReal.comp (hqm.comp (measurable_const.sub measurable_id))).mul
        (ENNReal.measurable_ofReal.comp (measurable_const.add
          ((Real.measurable_log.comp (measurable_const.min (measurable_id.sub_const y).norm)).abs))))
    calc ∫⁻ z, ENNReal.ofReal (rho z) * ENNReal.ofReal (F z)
        ≤ ∫⁻ z, ENNReal.ofReal C2 * (ENNReal.ofReal (rho z) *
          (ENNReal.ofReal (q (x - z)) * ENNReal.ofReal (1 + |Real.log (min 1 ‖z - y‖)|))) :=
          lintegral_mono_ae hpt
      _ = ENNReal.ofReal C2 * ∫⁻ z, ENNReal.ofReal (rho z) *
          (ENNReal.ofReal (q (x - z)) * ENNReal.ofReal (1 + |Real.log (min 1 ‖z - y‖)|)) :=
          lintegral_const_mul _ hmo
      _ ≤ ENNReal.ofReal C2 * ENNReal.ofReal C3 := mul_le_mul' le_rfl (H3 rho hrho hρG x y)
      _ = ENNReal.ofReal (C2 * C3) := (ENNReal.ofReal_mul hC2).symm
      _ ≤ ENNReal.ofReal (C2 + C2 * C3) := ENNReal.ofReal_le_ofReal (by linarith)

end HRS.MS.R26T8A
