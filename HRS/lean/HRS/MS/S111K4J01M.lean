import HRS.MS.S111K4J01L

/-!
# S11.1 / J01 piece: real norm bounds of `Dq` and `Jq` (S11K4)
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111K4J01

open HRS HRS.Whole HRS.MS.S111K2

theorem weighted_lintegral {H a b' : ℝ} (ha : 0 ≤ a) (hb : b' ≤ H) (q : TimeCoeff H) {w : ℝ → ℝ}
    (hw0 : ∀ v, 0 ≤ w v) (hw1 : ∀ v, w v ≤ 1) (hwm : Measurable w) :
    ∫⁻ v in Set.Ioc a b', ENNReal.ofReal (w v) * ‖(q : ℝ → Coeff) v‖ₑ =
      ENNReal.ofReal (∫ v in Set.Ioc a b', w v * ‖(q : ℝ → Coeff) v‖) := by
  have hsub : Set.Ioc a b' ⊆ Set.Icc (0 : ℝ) H := fun v hv => ⟨ha.trans hv.1.le, hv.2.trans hb⟩
  have hI : IntegrableOn (fun v => ‖(q : ℝ → Coeff) v‖) (Set.Icc (0 : ℝ) H) volume := q_integrable q
  have hIo : IntegrableOn (fun v => ‖(q : ℝ → Coeff) v‖) (Set.Ioc a b') volume := hI.mono_set hsub
  have hwI : Integrable (fun v => w v * ‖(q : ℝ → Coeff) v‖) (volume.restrict (Set.Ioc a b')) := by
    refine Integrable.mono' hIo (hwm.aemeasurable.mul
      (Lp.stronglyMeasurable q).norm.measurable.aemeasurable).aestronglyMeasurable ?_
    refine Eventually.of_forall fun v => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw0 v) (norm_nonneg _))]
    calc w v * ‖(q : ℝ → Coeff) v‖ ≤ 1 * ‖(q : ℝ → Coeff) v‖ :=
          mul_le_mul_of_nonneg_right (hw1 v) (norm_nonneg _)
      _ = _ := one_mul _
  rw [ofReal_integral_eq_lintegral_ofReal hwI (Eventually.of_forall fun v =>
    mul_nonneg (hw0 v) (norm_nonneg _))]
  refine lintegral_congr fun v => ?_
  rw [ENNReal.ofReal_mul (hw0 v), ofReal_norm_eq_enorm]

section ops
variable {d r : ℕ} {Pw : ℝ} (E : WeightedChart d r Pw) {C : WholeCoeff d} {c0 S T u K : ℝ}
  {b : MultiIndex d → ℝ}
  (hdata : ∀ q : TimeCoeff (u + T),
    S111k2Drift C (wholeSpaceIndex d : ℝ) c0 r b S T u Pw (zq E q))

theorem age_props (hc0 : 0 < c0) (k : ℕ) :
    (∀ v, 0 ≤ s111k2_age c0 u v ^ k) ∧ (∀ v, s111k2_age c0 u v ^ k ≤ 1) ∧
      Measurable (fun v => s111k2_age c0 u v ^ k) := by
  refine ⟨fun v => (pow_pos (s111k2_age_pos c0 u v) k).le, fun v =>
    pow_le_one₀ (s111k2_age_pos c0 u v).le (s111k2_age_le_one hc0 u v), ?_⟩
  unfold s111k2_age
  fun_prop

include hdata in
theorem Dq_norm_int (hc0 : 0 < c0) (q : TimeCoeff (u + T)) {a b' : ℝ} (ha : 0 ≤ a) (hab : a ≤ b')
    (hb : b' ≤ u + T) :
    ‖Dq E hdata q a b'‖ ≤ s111k2_Kdrift d r Pw S *
      ∫ v in Set.Ioc a b', s111k2_age c0 u v * ‖(q : ℝ → Coeff) v‖ := by
  have h := Dq_enorm_le E hdata q ha hab hb hc0
  obtain ⟨h0, h1, hm⟩ := age_props (u := u) hc0 1
  simp only [pow_one] at h0 h1 hm
  rw [weighted_lintegral ha hb q h0 h1 hm, ← ofReal_norm_eq_enorm] at h
  have hK := (s111k2_Kdrift_pos d r Pw S).le
  rw [← ENNReal.ofReal_mul hK] at h
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hK (integral_nonneg fun v =>
    mul_nonneg (h0 v) (norm_nonneg _)))).1 h

include hdata in
theorem Dq_norm_le (hc0 : 0 < c0) (q : TimeCoeff (u + T)) {a b' : ℝ} (ha : 0 ≤ a) (hab : a ≤ b')
    (hb : b' ≤ u + T) : ‖Dq E hdata q a b'‖ ≤ s111k2_Kdrift d r Pw S * ‖q‖ := by
  refine (Dq_norm_int E hdata hc0 q ha hab hb).trans ?_
  obtain ⟨h0, h1, hm⟩ := age_props (u := u) hc0 1
  simp only [pow_one] at h0 h1 hm
  exact mul_le_mul_of_nonneg_left (weighted_int_le ha hb q h0 h1 hm) (s111k2_Kdrift_pos d r Pw S).le

end ops

end HRS.MS.S111K4J01
