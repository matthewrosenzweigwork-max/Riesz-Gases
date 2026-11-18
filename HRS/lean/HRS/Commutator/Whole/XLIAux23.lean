import HRS.Commutator.Whole.XLIAux22

/-!
# X-LI part 23: Young's inequality for integrable kernels and the Bessel potential bound
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal FourierTransform ContDiff Convolution Topology SchwartzMap

noncomputable section

namespace HRS.Commutator.Whole.XLI

open HRS.Commutator.Whole

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- Young's inequality for nonnegative functions: `‖a ⋆ b‖_p ≤ ‖a‖₁ ‖b‖_p` (`1 ≤ p < ∞`) -/
lemma young_lintegral {a b : 𝔼 → ℝ≥0∞} (ha : Measurable a) (hb : Measurable b) {p : ℝ}
    (hp : 1 ≤ p) :
    ∫⁻ x, (∫⁻ z, a z * b (x - z)) ^ p ≤ (∫⁻ z, a z) ^ p * ∫⁻ x, b x ^ p := by
  have hswap : ∀ (c : 𝔼 → ℝ≥0∞), Measurable c →
      ∫⁻ x, ∫⁻ z, a z * c (x - z) = (∫⁻ z, a z) * ∫⁻ x, c x := by
    intro c hc
    have hm : Measurable (fun q : 𝔼 × 𝔼 => a q.2 * c (q.1 - q.2)) :=
      (ha.comp measurable_snd).mul (hc.comp (measurable_fst.sub measurable_snd))
    rw [lintegral_lintegral_swap hm.aemeasurable]
    have : ∀ z, ∫⁻ x, a z * c (x - z) = a z * ∫⁻ x, c x := fun z => by
      have hmz : Measurable (fun x : 𝔼 => c (x - z)) := hc.comp (measurable_id.sub_const z)
      rw [lintegral_const_mul _ hmz, lintegral_sub_right_eq_self c z]
    simp_rw [this]
    rw [lintegral_mul_const _ ha]
  rcases eq_or_lt_of_le hp with hp1 | hp1
  · subst hp1
    simp only [ENNReal.rpow_one]
    exact (hswap b hb).le
  have hp0 : 0 < p := by linarith
  set q : ℝ := p.conjExponent with hq
  have hconj : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp1
  have hq0 : 0 < q := hconj.symm.pos
  have hpq : p / q = p - 1 := by
    have h := hconj.inv_add_inv_eq_one
    have hq' : q ≠ 0 := hq0.ne'
    field_simp at h
    field_simp
    linarith
  -- pointwise Hölder
  have hpt : ∀ x, (∫⁻ z, a z * b (x - z)) ^ p ≤
      (∫⁻ z, a z) ^ (p - 1) * ∫⁻ z, a z * b (x - z) ^ p := by
    intro x
    have hbx : Measurable (fun z => b (x - z)) := hb.comp (measurable_const.sub measurable_id)
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq volume hconj.symm
      (f := fun z => a z ^ (1 / q)) (g := fun z => a z ^ (1 / p) * b (x - z))
      (ha.pow_const _).aemeasurable ((ha.pow_const _).mul hbx).aemeasurable
    have e1 : ∀ z, a z ^ (1 / q) * (a z ^ (1 / p) * b (x - z)) = a z * b (x - z) := by
      intro z
      rw [← mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by positivity)]
      have : 1 / q + 1 / p = 1 := by
        have := hconj.inv_add_inv_eq_one; simp only [one_div]; linarith
      rw [this, ENNReal.rpow_one]
    have e2 : ∀ z, (a z ^ (1 / q)) ^ q = a z := by
      intro z; rw [← ENNReal.rpow_mul]; field_simp; simp
    have e3 : ∀ z, (a z ^ (1 / p) * b (x - z)) ^ p = a z * b (x - z) ^ p := by
      intro z
      rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul]
      field_simp; simp
    simp only [Pi.mul_apply, e1, e2, e3] at h
    calc (∫⁻ z, a z * b (x - z)) ^ p
        ≤ ((∫⁻ z, a z) ^ (1 / q) * (∫⁻ z, a z * b (x - z) ^ p) ^ (1 / p)) ^ p := by
          gcongr
      _ = (∫⁻ z, a z) ^ (p - 1) * ∫⁻ z, a z * b (x - z) ^ p := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
          have h1 : 1 / q * p = p - 1 := by rw [one_div, ← div_eq_inv_mul, hpq]
          have h2 : 1 / p * p = 1 := by field_simp
          rw [h1, h2, ENNReal.rpow_one]
  have hmeasB : Measurable (fun x => ∫⁻ z, a z * b (x - z) ^ p) := by
    refine Measurable.lintegral_prod_right'
      (f := fun q : 𝔼 × 𝔼 => a q.2 * b (q.1 - q.2) ^ p) ?_
    exact (ha.comp measurable_snd).mul ((hb.comp (measurable_fst.sub measurable_snd)).pow_const _)
  calc ∫⁻ x, (∫⁻ z, a z * b (x - z)) ^ p
      ≤ ∫⁻ x, (∫⁻ z, a z) ^ (p - 1) * ∫⁻ z, a z * b (x - z) ^ p := lintegral_mono hpt
    _ = (∫⁻ z, a z) ^ (p - 1) * ∫⁻ x, ∫⁻ z, a z * b (x - z) ^ p :=
        lintegral_const_mul'' _ hmeasB.aemeasurable
    _ = (∫⁻ z, a z) ^ (p - 1) * ((∫⁻ z, a z) * ∫⁻ x, b x ^ p) := by
        rw [hswap (fun x => b x ^ p) (hb.pow_const _)]
    _ = (∫⁻ z, a z) ^ p * ∫⁻ x, b x ^ p := by
        rw [← mul_assoc]
        congr 1
        have := ENNReal.rpow_add_of_nonneg (x := ∫⁻ z, a z) (p - 1) 1 (by linarith) (by norm_num)
        rw [ENNReal.rpow_one, show p - 1 + 1 = p by ring] at this
        exact this.symm

end HRS.Commutator.Whole.XLI
