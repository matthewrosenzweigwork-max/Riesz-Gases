import HRS.Commutator.Whole.LocalAuxSAMP7
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# Continuity of `L^{p'} * L^p` (packet CMX-SAMP, helper file 8)
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal FourierTransform ContDiff Convolution

noncomputable section

namespace HRS.Commutator.Whole.SAMP1

open HRS HRS.Whole HRS.Commutator.Whole

variable {d : ℕ}

lemma holder_inst {p : ℝ} (hp : 1 < p) :
    (ENNReal.ofReal p).HolderConjugate (ENNReal.ofReal p.conjExponent) :=
  (Real.HolderConjugate.conjExponent hp).ennrealOfReal

lemma conv_integrable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℝ} (hp : 1 < p)
    {κ : Euc d → ℝ} (hκ : MemLp κ (ENNReal.ofReal p.conjExponent) volume)
    {w : Euc d → F} (hw : MemLp w (ENNReal.ofReal p) volume) (x : Euc d) :
    Integrable (fun y => κ (x - y) • w y) := by
  haveI := holder_inst hp
  have hκx : MemLp (fun y => κ (x - y)) (ENNReal.ofReal p.conjExponent) volume :=
    hκ.comp_measurePreserving (Measure.measurePreserving_sub_left volume x)
  have hprod := MemLp.integrable_mul (𝕜 := ℝ) (p := ENNReal.ofReal p.conjExponent)
    (q := ENNReal.ofReal p) (f := fun y => ‖κ (x - y)‖) (g := fun y => ‖w y‖) hκx.norm hw.norm
  refine hprod.mono' ?_ (Eventually.of_forall fun y => ?_)
  · exact hκx.aestronglyMeasurable.smul hw.aestronglyMeasurable
  · simp [norm_smul]

lemma conv_enorm_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℝ} (hp : 1 < p)
    {κ : Euc d → ℝ} (hκ : MemLp κ (ENNReal.ofReal p.conjExponent) volume)
    {w : Euc d → F} (hw : MemLp w (ENNReal.ofReal p) volume) (x : Euc d) :
    ‖∫ y, κ (x - y) • w y‖ₑ ≤
      eLpNorm κ (ENNReal.ofReal p.conjExponent) volume * eLpNorm w (ENNReal.ofReal p) volume := by
  haveI := holder_inst hp
  have hκx : MemLp (fun y => κ (x - y)) (ENNReal.ofReal p.conjExponent) volume :=
    hκ.comp_measurePreserving (Measure.measurePreserving_sub_left volume x)
  have h1 := eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (μ := volume)
    (p := ENNReal.ofReal p.conjExponent) (q := ENNReal.ofReal p) (r := 1)
    (f := fun y => κ (x - y)) (g := fun y => ‖w y‖) (fun a b : ℝ => a * b) (1 : ℝ≥0)
    continuous_mul hκx.aestronglyMeasurable hw.norm.aestronglyMeasurable
    (Eventually.of_forall fun y => by simp [nnnorm_mul])
  have hm : AEStronglyMeasurable (fun y => κ (x - y) * ‖w y‖) volume :=
    hκx.aestronglyMeasurable.mul hw.norm.aestronglyMeasurable
  rw [eLpNorm_one_eq_lintegral_enorm hm] at h1
  have e1 : eLpNorm (fun y => κ (x - y)) (ENNReal.ofReal p.conjExponent) volume =
      eLpNorm κ (ENNReal.ofReal p.conjExponent) volume :=
    eLpNorm_comp_measurePreserving hκ.aestronglyMeasurable
      (Measure.measurePreserving_sub_left volume x)
  have e2 : eLpNorm (fun y => ‖w y‖) (ENNReal.ofReal p) volume = eLpNorm w (ENNReal.ofReal p) volume :=
    eLpNorm_norm _ hw.aestronglyMeasurable
  rw [e1, e2, ENNReal.coe_one, one_mul] at h1
  refine (enorm_integral_le_lintegral_enorm _).trans (le_trans (le_of_eq ?_) h1)
  refine lintegral_congr fun y => ?_
  simp [enorm_smul, enorm_mul]

theorem continuous_conv_Lq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {p : ℝ} (hp : 1 < p) {κ : Euc d → ℝ}
    (hκ : MemLp κ (ENNReal.ofReal p.conjExponent) volume)
    {w : Euc d → F} (hw : MemLp w (ENNReal.ofReal p) volume) :
    Continuous (fun x => ∫ y, κ (x - y) • w y) := by
  haveI := holder_inst hp
  set Q : ℝ≥0∞ := ENNReal.ofReal p.conjExponent with hQ
  set P : ℝ≥0∞ := ENNReal.ofReal p with hP
  have hQt : Q ≠ ⊤ := ENNReal.ofReal_ne_top
  have hP1 : 1 ≤ P := by
    rw [hP, ← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp.le
  have happrox : ∀ n : ℕ, ∃ g : Euc d → ℝ, HasCompactSupport g ∧
      eLpNorm (κ - g) Q volume ≤ ENNReal.ofReal (1 / ((n : ℝ) + 1)) ∧ Continuous g ∧
      MemLp g Q volume := fun n =>
    hκ.exists_hasCompactSupport_eLpNorm_sub_le hQt
      (by simp [ENNReal.ofReal_eq_zero]; positivity)
  choose g hgs hgn hgc hgm using happrox
  have hcont : ∀ n, Continuous (fun x => ∫ y, g n (x - y) • w y) := by
    intro n
    have := (hgs n).continuous_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) (hgc n)
      (hw.locallyIntegrable hP1)
    convert this using 1
    ext x
    rw [convolution_lsmul_swap]
  have hwt : eLpNorm w P volume ≠ ⊤ := hw.eLpNorm_lt_top.ne
  have hunif : TendstoUniformly (fun n x => ∫ y, g n (x - y) • w y)
      (fun x => ∫ y, κ (x - y) • w y) atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    set C : ℝ := (eLpNorm w P volume).toReal with hC
    have hC0 : 0 ≤ C := ENNReal.toReal_nonneg
    obtain ⟨N, hN⟩ := exists_nat_gt ((C + 1) / ε)
    filter_upwards [eventually_ge_atTop N] with n hn x
    have hsub : (∫ y, κ (x - y) • w y) - ∫ y, g n (x - y) • w y =
        ∫ y, (κ - g n) (x - y) • w y := by
      rw [← integral_sub (conv_integrable hp hκ hw x) (conv_integrable hp (hgm n) hw x)]
      simp_rw [Pi.sub_apply, sub_smul]
    have h1 := conv_enorm_le hp (hκ.sub (hgm n)) hw x
    have h2 : ‖∫ y, (κ - g n) (x - y) • w y‖ ≤ (1 / ((n : ℝ) + 1)) * C := by
      have h3 : ‖∫ y, (κ - g n) (x - y) • w y‖ₑ ≤
          ENNReal.ofReal (1 / ((n : ℝ) + 1)) * eLpNorm w P volume :=
        h1.trans (mul_le_mul_left (hgn n) _)
      have h4 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hwt) h3
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), toReal_enorm] at h4
      exact h4
    rw [dist_eq_norm, hsub]
    refine lt_of_le_of_lt h2 ?_
    have hn' : (C + 1) / ε < (n : ℝ) := lt_of_lt_of_le hN (by exact_mod_cast hn)
    rw [div_lt_iff₀ hε] at hn'
    rw [one_div, inv_mul_eq_div, div_lt_iff₀ (by positivity)]
    nlinarith
  exact hunif.continuous (Eventually.of_forall hcont).frequently

end HRS.Commutator.Whole.SAMP1
