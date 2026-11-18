import HRS.MS.SA16Y7K1

/-!
# S.A.16 (SA16Y7) K2a: `L^p` bound of the difference quotient

`sa16y7_diff_lp`: for `g ∈ C¹` and `p > 1`, `‖g(·+h) - g‖_{L^p} ≤ |h| ‖Dg‖_{L^p}` (Hölder in the line integral and Tonelli).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16Q

open HRS HRS.Whole HRS.Whole.AppendixA

variable {d : ℕ}

lemma sa16y7_line_int {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {g : Euc d → E} (hg : ContDiff ℝ 1 g) (y h : Euc d) :
    ‖g (y + h) - g y‖ₑ ≤ ENNReal.ofReal ‖h‖ * ∫⁻ s in Ioc (0 : ℝ) 1, ‖fderiv ℝ g (y + s • h)‖ₑ := by
  have hdiff : Differentiable ℝ g := hg.differentiable one_ne_zero
  have hder : ∀ s : ℝ, HasDerivAt (fun s : ℝ => g (y + s • h)) (fderiv ℝ g (y + s • h) h) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => y + s • h) h s := by
      simpa using ((hasDerivAt_id s).smul_const h).const_add y
    exact (hdiff (y + s • h)).hasFDerivAt.comp_hasDerivAt s h1
  have hcont : Continuous (fun s : ℝ => fderiv ℝ g (y + s • h) h) :=
    ((hg.continuous_fderiv one_ne_zero).comp (continuous_const.add (continuous_id.smul continuous_const))).clm_apply
      continuous_const
  have hftc : ∫ s in (0 : ℝ)..1, fderiv ℝ g (y + s • h) h = g (y + (1 : ℝ) • h) - g (y + (0 : ℝ) • h) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hder s) (hcont.intervalIntegrable 0 1)
  simp only [one_smul, zero_smul, add_zero] at hftc
  rw [← hftc, intervalIntegral.integral_of_le zero_le_one]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun s => ?_
  rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul (norm_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [mul_comm]
  exact ((fderiv ℝ g (y + s • h)).le_opNorm h)

lemma sa16y7_holder_unit {p : ℝ} (hp : 1 < p) (G : ℝ → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ s in Ioc (0 : ℝ) 1, G s ≤ (∫⁻ s in Ioc (0 : ℝ) 1, G s ^ p) ^ (1 / p) := by
  have hpq := Real.HolderConjugate.conjExponent hp
  have := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (Ioc (0 : ℝ) 1)) hpq hG.aemeasurable
    (g := fun _ => (1 : ℝ≥0∞)) aemeasurable_const
  simpa [Pi.mul_def] using this

lemma sa16y7_diff_lp {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {g : Euc d → E} (hg : ContDiff ℝ 1 g) {p : ℝ} (hp : 1 < p) (h : Euc d) :
    eLpNorm (fun y => ‖g (y + h) - g y‖) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal ‖h‖ * eLpNorm (fun y => ‖fderiv ℝ g y‖) (ENNReal.ofReal p) volume := by
  have hp0 : 0 < p := by linarith
  have hpe0 : ENNReal.ofReal p ≠ 0 := by simpa using hp0
  have hpet : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hgc : Continuous g := hg.continuous
  have hDc : Continuous (fderiv ℝ g) := hg.continuous_fderiv one_ne_zero
  have hdc : Continuous (fun y => ‖g (y + h) - g y‖) :=
    ((hgc.comp (continuous_id.add continuous_const)).sub hgc).norm
  have hDnc : Continuous (fun y => ‖fderiv ℝ g y‖) := hDc.norm
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpe0 hpet hdc.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hpe0 hpet hDnc.aestronglyMeasurable, ENNReal.toReal_ofReal hp0.le]
  have h1p : (0 : ℝ) ≤ 1 / p := by positivity
  set B : ℝ≥0∞ := ∫⁻ y, ‖‖fderiv ℝ g y‖‖ₑ ^ p with hB
  have hGm : ∀ y : Euc d, Measurable (fun s : ℝ => ‖fderiv ℝ g (y + s • h)‖ₑ) := fun y =>
    ((hDc.comp (continuous_const.add (continuous_id.smul continuous_const))).measurable).enorm
  have hpt : ∀ y : Euc d, ‖‖g (y + h) - g y‖‖ₑ ^ p ≤
      ENNReal.ofReal ‖h‖ ^ p * ∫⁻ s in Ioc (0 : ℝ) 1, ‖fderiv ℝ g (y + s • h)‖ₑ ^ p := by
    intro y
    have h1 := sa16y7_line_int hg y h
    have h2 := sa16y7_holder_unit hp (fun s => ‖fderiv ℝ g (y + s • h)‖ₑ) (hGm y)
    rw [enorm_norm]
    calc ‖g (y + h) - g y‖ₑ ^ p ≤ (ENNReal.ofReal ‖h‖ * ∫⁻ s in Ioc (0 : ℝ) 1, ‖fderiv ℝ g (y + s • h)‖ₑ) ^ p :=
          ENNReal.rpow_le_rpow h1 hp0.le
      _ = ENNReal.ofReal ‖h‖ ^ p * (∫⁻ s in Ioc (0 : ℝ) 1, ‖fderiv ℝ g (y + s • h)‖ₑ) ^ p :=
          ENNReal.mul_rpow_of_nonneg _ _ hp0.le
      _ ≤ ENNReal.ofReal ‖h‖ ^ p * ((∫⁻ s in Ioc (0 : ℝ) 1, ‖fderiv ℝ g (y + s • h)‖ₑ ^ p) ^ (1 / p)) ^ p := by
          gcongr
      _ = _ := by
          rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp0.ne', ENNReal.rpow_one]
  have hmeasU : Measurable (Function.uncurry fun (y : Euc d) (s : ℝ) => ‖fderiv ℝ g (y + s • h)‖ₑ ^ p) :=
    (((hDc.comp (continuous_fst.add (continuous_snd.smul continuous_const))).measurable).enorm).pow_const p
  have hkey : ∫⁻ y, ‖‖g (y + h) - g y‖‖ₑ ^ p ≤ ENNReal.ofReal ‖h‖ ^ p * B := by
    calc ∫⁻ y, ‖‖g (y + h) - g y‖‖ₑ ^ p
        ≤ ∫⁻ y, ENNReal.ofReal ‖h‖ ^ p * ∫⁻ s in Ioc (0 : ℝ) 1, ‖fderiv ℝ g (y + s • h)‖ₑ ^ p :=
          lintegral_mono hpt
      _ = ENNReal.ofReal ‖h‖ ^ p * ∫⁻ y, ∫⁻ s in Ioc (0 : ℝ) 1, ‖fderiv ℝ g (y + s • h)‖ₑ ^ p := by
          rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp0.le ENNReal.ofReal_ne_top)]
      _ = ENNReal.ofReal ‖h‖ ^ p * ∫⁻ s in Ioc (0 : ℝ) 1, ∫⁻ y, ‖fderiv ℝ g (y + s • h)‖ₑ ^ p := by
          rw [lintegral_lintegral_swap hmeasU.aemeasurable]
      _ = ENNReal.ofReal ‖h‖ ^ p * ∫⁻ s in Ioc (0 : ℝ) 1, B := by
          congr 1
          refine lintegral_congr fun s => ?_
          have := lintegral_add_right_eq_self (μ := (volume : Measure (Euc d)))
            (fun y => ‖fderiv ℝ g y‖ₑ ^ p) (s • h)
          simpa [hB] using this
      _ = ENNReal.ofReal ‖h‖ ^ p * B := by simp
  calc (∫⁻ y, ‖‖g (y + h) - g y‖‖ₑ ^ p) ^ (1 / p)
      ≤ (ENNReal.ofReal ‖h‖ ^ p * B) ^ (1 / p) := ENNReal.rpow_le_rpow hkey h1p
    _ = ENNReal.ofReal ‖h‖ * B ^ (1 / p) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ h1p, ← ENNReal.rpow_mul, mul_one_div_cancel hp0.ne', ENNReal.rpow_one]

end HRS.Whole.AppendixA.Phase2SA16Q
