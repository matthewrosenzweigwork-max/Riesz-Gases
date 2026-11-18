import HRS.MS.SA16JetConv

/-!
# S.A.16 (SA16Y3) Yg1: Young's convolution inequality in `L^p(ℝ^d)` (generic, for SA16S item (iii))

`sa16y3_young_lintegral`: `∫⁻ (∫⁻ |g y| |f(x-y)| dy)^p dx ≤ (∫⁻ |g|)^p ∫⁻ |f|^p` for `1 ≤ p`
(from the weighted Minkowski inequality `sa16j_mink` and translation invariance).
`sa16y3_young_eLp`: `‖∫ g(y) f(· - y) dy‖_{L^p} ≤ (∫⁻ |g|) ‖f‖_{L^p}` (the Bochner convolution, no integrability of `g` needed).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HRS.Whole.AppendixA.Phase2SA16R

lemma sa16y3_young_lintegral {d : ℕ} {p : ℝ} (hp : 1 ≤ p) (g f : EuclideanSpace ℝ (Fin d) → ℝ)
    (hg : Measurable g) (hf : Measurable f) :
    ∫⁻ x, (∫⁻ y, ‖g y‖ₑ * ‖f (x - y)‖ₑ) ^ p ≤ (∫⁻ y, ‖g y‖ₑ) ^ p * ∫⁻ x, ‖f x‖ₑ ^ p := by
  have hF : Measurable (Function.uncurry fun (x y : EuclideanSpace ℝ (Fin d)) => ‖f (x - y)‖ₑ) :=
    (hf.comp (measurable_fst.sub measurable_snd)).enorm
  have ha : Measurable (fun y => ‖g y‖ₑ) := hg.enorm
  have hmink := HRS.Whole.AppendixA.Phase2SA16.sa16j_mink (μ := (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (ν := (volume : Measure (EuclideanSpace ℝ (Fin d)))) hp ha hF
  have hinner : ∀ y : EuclideanSpace ℝ (Fin d),
      ∫⁻ x, ‖f (x - y)‖ₑ ^ p = ∫⁻ x, ‖f x‖ₑ ^ p := fun y =>
    lintegral_sub_right_eq_self (fun x => ‖f x‖ₑ ^ p) y
  simp only [hinner] at hmink
  rw [lintegral_mul_const _ ha] at hmink
  have hA : (∫⁻ y, ‖g y‖ₑ) ^ (p - 1) * (∫⁻ y, ‖g y‖ₑ) = (∫⁻ y, ‖g y‖ₑ) ^ p := by
    conv_rhs => rw [show p = (p - 1) + 1 by ring]
    rw [ENNReal.rpow_add_of_nonneg (p - 1) 1 (show (0 : ℝ) ≤ p - 1 by linarith) zero_le_one, ENNReal.rpow_one]
  refine hmink.trans (le_of_eq ?_)
  rw [← mul_assoc, hA]

theorem sa16y3_young_eLp {d : ℕ} {p : ℝ} (hp : 1 ≤ p) (g f : EuclideanSpace ℝ (Fin d) → ℝ)
    (hg : Measurable g) (hf : Measurable f) :
    eLpNorm (fun x => ∫ y, g y * f (x - y)) (ENNReal.ofReal p) volume ≤
      (∫⁻ y, ‖g y‖ₑ) * eLpNorm f (ENNReal.ofReal p) volume := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hpne : ENNReal.ofReal p ≠ 0 := by simpa using hp0
  have hpt : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpr : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
  have hpm : Measurable (fun q : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => g q.2 * f (q.1 - q.2)) :=
    (hg.comp measurable_snd).mul (hf.comp (measurable_fst.sub measurable_snd))
  have hCm : StronglyMeasurable (fun x => ∫ y, g y * f (x - y)) :=
    hpm.stronglyMeasurable.integral_prod_right
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpne hpt hCm.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hpne hpt hf.aestronglyMeasurable, hpr]
  have hpt' : p ≠ 0 := hp0.ne'
  have hC : ∀ x, ‖∫ y, g y * f (x - y)‖ₑ ≤ ∫⁻ y, ‖g y‖ₑ * ‖f (x - y)‖ₑ := fun x => by
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    congr 1
    funext y
    rw [enorm_mul]
  have hmain : ∫⁻ x, ‖∫ y, g y * f (x - y)‖ₑ ^ p ≤
      (∫⁻ y, ‖g y‖ₑ) ^ p * ∫⁻ x, ‖f x‖ₑ ^ p :=
    (lintegral_mono fun x => ENNReal.rpow_le_rpow (hC x) hp0.le).trans
      (sa16y3_young_lintegral hp g f hg hf)
  calc (∫⁻ x, ‖∫ y, g y * f (x - y)‖ₑ ^ p) ^ (1 / p)
      ≤ ((∫⁻ y, ‖g y‖ₑ) ^ p * ∫⁻ x, ‖f x‖ₑ ^ p) ^ (1 / p) :=
        ENNReal.rpow_le_rpow hmain (by positivity)
    _ = (∫⁻ y, ‖g y‖ₑ) * (∫⁻ x, ‖f x‖ₑ ^ p) ^ (1 / p) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), one_div, ENNReal.rpow_rpow_inv hpt']

end HRS.Whole.AppendixA.Phase2SA16R
