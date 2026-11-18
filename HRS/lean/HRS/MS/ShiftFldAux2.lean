import HRS.MS.ShiftFldAux1

/-!
# S79: translation of smooth distances, and `shifted_field_static`

* `s79_smoothDist_shifted_le`: `d_{C_b^2}(Law(X)(. + a), Law(Y)(. + b)) <= d_{C_b^2}(Law X, Law Y) + ||a - b||`
  (translation preserves the `C_b^2` unit ball, `C_b^1` unit-ball functions are 1-Lipschitz).
* `shifted_field_static_proof`: the TeX proof of S L6171-6192 for the static clause: `eta_N = zeta_N + sqrt N (m_N - mu)`
  (`eta_eq_zeta_add`), `S45.quadratic_static_field_osc_proof` for `zeta_N`, and the bias bound
  `||sqrt N (m_N - mu) - N^{3/2-p} b|| <= K C_b N^{3/2-p-theta}` from `S71.sharp_bias_quadratic_proof` and `s79_bias_vec_bound`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.Whole.S79

open HRS (Euc)

section Transl

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B] [BorelSpace B]

theorem s79_smoothDist_map_add_le (k : ℕ) (P Q : Measure B) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (v : B) : HRS.smoothDist k (P.map (· + v)) (Q.map (· + v)) ≤ HRS.smoothDist k P Q := by
  unfold HRS.smoothDist
  refine Real.iSup_le (fun Φ => ?_) (HRS.smoothDist_nonneg k P Q)
  have hm : Measurable (fun z : B => z + v) := measurable_add_const v
  have hΦ := HRS.cbUnitBall_translate Φ.2 v
  rw [integral_map hm.aemeasurable Φ.2.1.continuous.aestronglyMeasurable,
    integral_map hm.aemeasurable Φ.2.1.continuous.aestronglyMeasurable]
  exact HRS.abs_integral_sub_le_smoothDist hΦ P Q

theorem s79_smoothDist_shift_le (Q : Measure B) [IsProbabilityMeasure Q] (a b : B) :
    HRS.smoothDist 2 (Q.map (· + a)) (Q.map (· + b)) ≤ ‖a - b‖ := by
  unfold HRS.smoothDist
  refine Real.iSup_le (fun Φ => ?_) (norm_nonneg _)
  have hma : Measurable (fun z : B => z + a) := measurable_add_const a
  have hmb : Measurable (fun z : B => z + b) := measurable_add_const b
  have hc : Continuous Φ.1 := Φ.2.1.continuous
  have hΦ1 : Φ.1 ∈ HRS.CbUnitBall B 1 := HRS.cbUnitBall_anti (by norm_num) Φ.2
  rw [integral_map hma.aemeasurable hc.aestronglyMeasurable,
    integral_map hmb.aemeasurable hc.aestronglyMeasurable]
  have hi : ∀ v : B, Integrable (fun z => Φ.1 (z + v)) Q := fun v =>
    Integrable.of_bound (C := 1) ((hc.comp (continuous_id.add continuous_const)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun z => by simpa using HRS.abs_apply_le_of_mem Φ.2 (z + v))
  rw [← integral_sub (hi a) (hi b)]
  have := norm_integral_le_of_norm_le_const (μ := Q) (f := fun z => Φ.1 (z + a) - Φ.1 (z + b))
    (C := ‖a - b‖) (Filter.Eventually.of_forall fun z => by
      have := HRS.norm_sub_le_of_mem_one hΦ1 (z + a) (z + b)
      simpa [add_sub_add_left_eq_sub] using this)
  simpa [Real.norm_eq_abs, Measure.real] using this

theorem s79_smoothDist_shifted_le (P Q : Measure B) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (a b : B) :
    HRS.smoothDist 2 (P.map (· + a)) (Q.map (· + b)) ≤ HRS.smoothDist 2 P Q + ‖a - b‖ :=
  (HRS.smoothDist_triangle 2 (P.map (· + a)) (Q.map (· + a)) (Q.map (· + b))).trans
    (add_le_add (s79_smoothDist_map_add_le 2 P Q a) (s79_smoothDist_shift_le Q a b))

end Transl

end HRS.Whole.S79
