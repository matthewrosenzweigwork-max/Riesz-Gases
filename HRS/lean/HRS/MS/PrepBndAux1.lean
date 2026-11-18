import HRS.MS.WrEnt

/-!
# HRS.MS.PrepBndAux1 -- relative entropy between two exponentially tilted laws (packet PREP, part 1)

Generic measure-theoretic input for `euclidean_preparations_bounds` (S3.2).

* `prep_kl_gibbs`: if `P = K₀⁻¹ e^{a₀ F} π` and `Q = K₁⁻¹ e^{a₁ F} π` are probability measures
  (`K_i = ∫ e^{a_i F} dπ`, `K_i > 0`) and `F` is `P`-integrable, then
  `klDiv P Q = ofReal (log K₁ - log K₀ + (a₀ - a₁) E_P F)`: in particular it is finite and no Bochner
  junk value enters (the integrability of `F` is a hypothesis, and the identity is an equality in `ℝ≥0∞`).

Helper lemmas carry the prefix `prep_`.
-/

set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Function Set
open scoped ENNReal

noncomputable section

namespace HRS.MS.Wr

variable {α : Type*} [MeasurableSpace α]

theorem prep_withDensity_ratio (π : Measure α) {F : α → ℝ} (hF : Measurable F) {a0 a1 K0 K1 : ℝ}
    (hK0 : 0 < K0) (hK1 : 0 < K1) :
    ((ENNReal.ofReal K1)⁻¹ • π.withDensity (fun x => ENNReal.ofReal (Real.exp (a1 * F x)))).withDensity
        (fun x => ENNReal.ofReal (K1 / K0 * Real.exp ((a0 - a1) * F x))) =
      (ENNReal.ofReal K0)⁻¹ • π.withDensity (fun x => ENNReal.ofReal (Real.exp (a0 * F x))) := by
  have hm1 : Measurable (fun x => ENNReal.ofReal (Real.exp (a1 * F x))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul hF))
  have hm2 : Measurable (fun x => ENNReal.ofReal (K1 / K0 * Real.exp ((a0 - a1) * F x))) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul
      (Real.measurable_exp.comp (measurable_const.mul hF)))
  rw [withDensity_smul_measure, ← withDensity_mul _ hm1 hm2]
  have hfun : ((fun x => ENNReal.ofReal (Real.exp (a1 * F x))) *
      (fun x => ENNReal.ofReal (K1 / K0 * Real.exp ((a0 - a1) * F x)))) =
      (ENNReal.ofReal K1 * (ENNReal.ofReal K0)⁻¹) •
        (fun x => ENNReal.ofReal (Real.exp (a0 * F x))) := by
    funext x
    simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_inv_of_pos hK0,
      ← ENNReal.ofReal_mul hK1.le, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have : Real.exp (a1 * F x) * (K1 / K0 * Real.exp ((a0 - a1) * F x)) =
        K1 * K0⁻¹ * Real.exp (a0 * F x) := by
      have h := Real.exp_add (a1 * F x) ((a0 - a1) * F x)
      have e : a1 * F x + (a0 - a1) * F x = a0 * F x := by ring
      rw [e] at h
      calc Real.exp (a1 * F x) * (K1 / K0 * Real.exp ((a0 - a1) * F x))
          = K1 / K0 * (Real.exp (a1 * F x) * Real.exp ((a0 - a1) * F x)) := by ring
        _ = K1 * K0⁻¹ * Real.exp (a0 * F x) := by rw [← h]; ring
    exact this
  rw [hfun, withDensity_smul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hK0).ne')), smul_smul]
  congr 1
  rw [← mul_assoc, ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.2 hK1).ne' ENNReal.ofReal_ne_top,
    one_mul]

/-- **Relative entropy of two tilts of one reference measure.** -/
theorem prep_kl_gibbs (π : Measure α) {F : α → ℝ} (hF : Measurable F) {a0 a1 K0 K1 : ℝ}
    (hK0 : 0 < K0) (hK1 : 0 < K1)
    (h0 : ∫⁻ x, ENNReal.ofReal (Real.exp (a0 * F x)) ∂π = ENNReal.ofReal K0)
    (h1 : ∫⁻ x, ENNReal.ofReal (Real.exp (a1 * F x)) ∂π = ENNReal.ofReal K1)
    (P Q : Measure α)
    (hP : P = (ENNReal.ofReal K0)⁻¹ • π.withDensity (fun x => ENNReal.ofReal (Real.exp (a0 * F x))))
    (hQ : Q = (ENNReal.ofReal K1)⁻¹ • π.withDensity (fun x => ENNReal.ofReal (Real.exp (a1 * F x))))
    (hint : Integrable F P) :
    InformationTheory.klDiv P Q =
      ENNReal.ofReal (Real.log K1 - Real.log K0 + (a0 - a1) * ∫ x, F x ∂P) := by
  have hPu : P Set.univ = 1 := by
    rw [hP, Measure.smul_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, h0,
      smul_eq_mul]
    exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.2 hK0).ne' ENNReal.ofReal_ne_top
  have hQu : Q Set.univ = 1 := by
    rw [hQ, Measure.smul_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, h1,
      smul_eq_mul]
    exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.2 hK1).ne' ENNReal.ofReal_ne_top
  haveI : IsProbabilityMeasure P := ⟨hPu⟩
  haveI : IsProbabilityMeasure Q := ⟨hQu⟩
  set r : α → ℝ := fun x => K1 / K0 * Real.exp ((a0 - a1) * F x) with hr
  have hrpos : ∀ x, 0 < r x := fun x => by simp only [hr]; positivity
  have hrm : Measurable r := measurable_const.mul
    (Real.measurable_exp.comp (measurable_const.mul hF))
  have hPQ : P = Q.withDensity (fun x => ENNReal.ofReal (r x)) := by
    rw [hQ, prep_withDensity_ratio π hF hK0 hK1, ← hP]
  have hac : P ≪ Q := by rw [hPQ]; exact withDensity_absolutelyContinuous _ _
  have hrn : P.rnDeriv Q =ᵐ[Q] fun x => ENNReal.ofReal (r x) := by
    conv_lhs => rw [hPQ]
    exact Measure.rnDeriv_withDensity Q (ENNReal.measurable_ofReal.comp hrm)
  have hllr : llr P Q =ᵐ[P] fun x => Real.log K1 - Real.log K0 + (a0 - a1) * F x := by
    filter_upwards [hac.ae_le hrn] with x hx
    unfold llr
    rw [hx, ENNReal.toReal_ofReal (hrpos x).le]
    simp only [hr]
    rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_div hK1.ne' hK0.ne',
      Real.log_exp]
  have hi : Integrable (fun x => Real.log K1 - Real.log K0 + (a0 - a1) * F x) P :=
    (integrable_const _).add (hint.const_mul _)
  have hill : Integrable (llr P Q) P := hi.congr hllr.symm
  rw [InformationTheory.klDiv_of_ac_of_integrable hac hill, integral_congr_ae hllr,
    integral_add (integrable_const _) (hint.const_mul _), integral_const, integral_const_mul]
  simp [Measure.real, hPu, hQu]

end HRS.MS.Wr
