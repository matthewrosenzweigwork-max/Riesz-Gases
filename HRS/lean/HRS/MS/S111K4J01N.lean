import HRS.MS.S111K4J01M

/-!
# S11.1 / J01 piece: real norm bounds of the covariance interval tensor of an `L¹` coefficient path (S11K4)
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111K4J01

open HRS HRS.Whole HRS.MS.S111K2

section cov2
variable {d r : ℕ} {Pw : ℝ} (E : WeightedChart d r Pw) {C : WholeCoeff d} {T u c0 K : ℝ}
  {J : (ℝ → (Euc d → ℝ) → ℝ) → ℝ → ℝ → projTensor (OscPath d (wholeSpaceIndex d : ℝ) T) 2}

theorem Jq_norm_int (hco : ChartedOrbits E C (wholeSpaceIndex d : ℝ) (u + T))
    (hJ : CovCore d r (wholeSpaceIndex d : ℝ) T Pw u c0 K C J) (hc0 : 0 < c0) (hK : 0 ≤ K)
    (q : TimeCoeff (u + T)) {a b' : ℝ} (ha : 0 ≤ a) (hab : a ≤ b') (hb : b' ≤ u + T) :
    ‖Jq E J q a b'‖ ≤ K * |2 * C.ν| *
      ∫ v in Set.Ioc a b', s111k2_age c0 u v ^ 2 * ‖(q : ℝ → Coeff) v‖ := by
  obtain ⟨-, -, hprops⟩ := hJ
  obtain ⟨hA, hM⟩ := zq0_adm E hco q
  obtain ⟨-, -, -, hv⟩ := hprops _ hA hM
  have h := (hv a b' ha hab hb).2
  have hle : ∫⁻ v in Set.Ioc a b', ENNReal.ofReal (s111k2_age c0 u v ^ 2) *
        dualNormE r Pw (coefficientField E (q : ℝ → Coeff) v) ≤
      ∫⁻ v in Set.Ioc a b', ENNReal.ofReal (s111k2_age c0 u v ^ 2) * ‖(q : ℝ → Coeff) v‖ₑ := by
    refine lintegral_mono fun v => mul_le_mul' le_rfl ?_
    rw [← ofReal_norm_eq_enorm]
    exact dualNormE_coefficientField_le E _ v
  obtain ⟨h0, h1, hm⟩ := age_props (u := u) hc0 2
  have h2 := h.trans (mul_le_mul' le_rfl hle)
  rw [weighted_lintegral ha hb q h0 h1 hm, ← ofReal_norm_eq_enorm] at h2
  have hKn : 0 ≤ K * |2 * C.ν| := mul_nonneg hK (abs_nonneg _)
  rw [← ENNReal.ofReal_mul hKn] at h2
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hKn (integral_nonneg fun v =>
    mul_nonneg (h0 v) (norm_nonneg _)))).1 h2

theorem Jq_norm_le (hco : ChartedOrbits E C (wholeSpaceIndex d : ℝ) (u + T))
    (hJ : CovCore d r (wholeSpaceIndex d : ℝ) T Pw u c0 K C J) (hc0 : 0 < c0) (hK : 0 ≤ K)
    (q : TimeCoeff (u + T)) {a b' : ℝ} (ha : 0 ≤ a) (hab : a ≤ b') (hb : b' ≤ u + T) :
    ‖Jq E J q a b'‖ ≤ K * |2 * C.ν| * ‖q‖ := by
  refine (Jq_norm_int E hco hJ hc0 hK q ha hab hb).trans ?_
  obtain ⟨h0, h1, hm⟩ := age_props (u := u) hc0 2
  exact mul_le_mul_of_nonneg_left (weighted_int_le ha hb q h0 h1 hm) (mul_nonneg hK (abs_nonneg _))

end cov2

end HRS.MS.S111K4J01
