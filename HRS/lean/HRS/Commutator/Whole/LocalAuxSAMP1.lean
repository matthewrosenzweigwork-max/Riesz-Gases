import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Group.Prod

/-!
# Young-type inequalities (packet CMX-SAMP, helper file 1)

Generic `ℝ≥0∞`-valued Young inequality with an `L¹` kernel on a commutative group (used for the
convolutions of `vlo_bound`, `vhi_Lp` and, with the counting measure on `ℤ^d`, for the sequence
Young inequality of `vhi_cube_sampling`).
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace HRS.Commutator.Whole.SAMP1

variable {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableSub₂ G] [MeasurableAdd G]

/-- Young's inequality `‖k * f‖_p ≤ ‖k‖₁ ‖f‖_p` in `ℝ≥0∞` (`1 < p < ∞`). -/
lemma young_lintegral (μ : Measure G) [SFinite μ] [μ.IsAddRightInvariant]
    {k f : G → ℝ≥0∞} (hk : Measurable k) (hf : Measurable f) {p : ℝ} (hp : 1 < p)
    (hA : ∫⁻ y, k y ∂μ ≠ ⊤) :
    ∫⁻ x, (∫⁻ y, k y * f (x - y) ∂μ) ^ p ∂μ ≤ (∫⁻ y, k y ∂μ) ^ p * ∫⁻ x, f x ^ p ∂μ := by
  set A := ∫⁻ y, k y ∂μ with hAdef
  have hq := Real.HolderConjugate.conjExponent hp
  set q := p.conjExponent with hqdef
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := hq.symm.pos
  have hsum : 1 / q + 1 / p = 1 := by
    have := hq.symm.inv_add_inv_eq_one
    simpa [one_div] using this
  -- pointwise Hölder
  have hpt : ∀ x, ∫⁻ y, k y * f (x - y) ∂μ ≤
      A ^ (1 / q) * (∫⁻ y, k y * f (x - y) ^ p ∂μ) ^ (1 / p) := by
    intro x
    have hmeas : Measurable fun y => f (x - y) := hf.comp (measurable_const.sub measurable_id)
    have e1 : ∀ y, k y * f (x - y) = (k y) ^ (1 / q) * ((k y) ^ (1 / p) * f (x - y)) := by
      intro y
      rw [← mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by positivity), hsum,
        ENNReal.rpow_one]
    simp_rw [e1]
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hq.symm
      (f := fun y => (k y) ^ (1 / q)) (g := fun y => (k y) ^ (1 / p) * f (x - y))
      (hk.pow_const _).aemeasurable ((hk.pow_const _).mul hmeas).aemeasurable
    have e2 : (∫⁻ y, (k y ^ (1 / q)) ^ q ∂μ) = A := by
      refine lintegral_congr fun y => ?_
      rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hq0.ne', ENNReal.rpow_one]
    have e3 : (∫⁻ y, (k y ^ (1 / p) * f (x - y)) ^ p ∂μ) = ∫⁻ y, k y * f (x - y) ^ p ∂μ := by
      refine lintegral_congr fun y => ?_
      rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul, one_div,
        inv_mul_cancel₀ hp0.ne', ENNReal.rpow_one]
    simp only [Pi.mul_apply] at h
    rw [e2, e3] at h
    exact h
  have hpt2 : ∀ x, (∫⁻ y, k y * f (x - y) ∂μ) ^ p ≤
      A ^ (p / q) * ∫⁻ y, k y * f (x - y) ^ p ∂μ := by
    intro x
    calc (∫⁻ y, k y * f (x - y) ∂μ) ^ p
        ≤ (A ^ (1 / q) * (∫⁻ y, k y * f (x - y) ^ p ∂μ) ^ (1 / p)) ^ p :=
          ENNReal.rpow_le_rpow (hpt x) hp0.le
      _ = A ^ (p / q) * ∫⁻ y, k y * f (x - y) ^ p ∂μ := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
          have e1 : 1 / p * p = 1 := by field_simp
          have e2 : 1 / q * p = p / q := by field_simp
          rw [e1, e2, ENNReal.rpow_one]
  calc ∫⁻ x, (∫⁻ y, k y * f (x - y) ∂μ) ^ p ∂μ
      ≤ ∫⁻ x, A ^ (p / q) * ∫⁻ y, k y * f (x - y) ^ p ∂μ ∂μ := lintegral_mono hpt2
    _ = A ^ (p / q) * ∫⁻ x, ∫⁻ y, k y * f (x - y) ^ p ∂μ ∂μ := lintegral_const_mul' _ _ (by
          exact ENNReal.rpow_ne_top_of_nonneg (by positivity) hA)
    _ = A ^ (p / q) * ∫⁻ y, ∫⁻ x, k y * f (x - y) ^ p ∂μ ∂μ := by
          congr 1
          refine lintegral_lintegral_swap ?_
          exact ((hk.comp measurable_snd).mul
            ((hf.comp (measurable_fst.sub measurable_snd)).pow_const p)).aemeasurable
    _ = A ^ (p / q) * (A * ∫⁻ x, f x ^ p ∂μ) := by
          congr 1
          have : ∀ y, ∫⁻ x, k y * f (x - y) ^ p ∂μ = k y * ∫⁻ x, f x ^ p ∂μ := by
            intro y
            have hm : Measurable fun x => f (x - y) ^ p :=
              (hf.pow_const p).comp (measurable_sub_const y)
            rw [lintegral_const_mul _ hm]
            congr 1
            exact lintegral_sub_right_eq_self (fun x => f x ^ p) y
          simp_rw [this]
          rw [lintegral_mul_const _ hk]
    _ = A ^ p * ∫⁻ x, f x ^ p ∂μ := by
          rw [← mul_assoc]
          congr 1
          rw [show A ^ (p / q) * A = A ^ (p / q) * A ^ (1 : ℝ) by rw [ENNReal.rpow_one],
            ← ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by norm_num)]
          congr 1
          have : p / q = p - 1 := by
            have h1 : 1 / q = 1 - 1 / p := by linarith
            calc p / q = p * (1 / q) := by ring
              _ = p - 1 := by rw [h1]; field_simp
          linarith

/-- The sequence form on a countable group (`μ = count`). -/
lemma young_tsum [Countable G] [MeasurableSingletonClass G]
    {b a : G → ℝ≥0∞} {p : ℝ} (hp : 1 < p) (hb : ∑' y, b y ≠ ⊤) :
    ∑' x, (∑' y, b y * a (x - y)) ^ p ≤ (∑' y, b y) ^ p * ∑' x, a x ^ p := by
  have h := young_lintegral (Measure.count : Measure G) (k := b) (f := a)
    (measurable_of_countable _) (measurable_of_countable _) hp (by rwa [lintegral_count])
  simpa only [lintegral_count] using h

end HRS.Commutator.Whole.SAMP1
