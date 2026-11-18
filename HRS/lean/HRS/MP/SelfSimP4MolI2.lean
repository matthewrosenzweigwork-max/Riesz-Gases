import HRS.MP.SelfSimP4MolI1

/-!
# MPP4MOL stage 5c (19): moments, and the clamped data
-/

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MP.SelfSimP4Mol

variable {d N : ℕ}

theorem p4m_moment {μ : Measure (EucConfig d N)} {C : ℝ≥0∞} (hC : C < ⊤)
    (h : ∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂μ ≤ C) :
    Integrable p4m_q μ ∧ ∫ x, p4m_q x ∂μ ≤ N * C.toReal := by
  have hmeas : Measurable (p4m_q : EucConfig d N → ℝ) := p4m_continuous_q.measurable
  have hle : ∫⁻ x, ENNReal.ofReal (p4m_q x) ∂μ ≤ ENNReal.ofReal N * C := by
    calc ∫⁻ x, ENNReal.ofReal (p4m_q x) ∂μ ≤ ∫⁻ x, ENNReal.ofReal N * ENNReal.ofReal (‖x‖ ^ 2) ∂μ := by
          refine lintegral_mono fun x => ?_
          rw [← ENNReal.ofReal_mul (Nat.cast_nonneg N)]
          exact ENNReal.ofReal_le_ofReal (by
            have := p4m_q_le x
            have h2 : (‖x‖ ^ 2) * (N : ℝ) = N * ‖x‖ ^ 2 := mul_comm _ _
            linarith)
      _ = ENNReal.ofReal N * ∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂μ := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal N * C := by gcongr
  have hfin : ∫⁻ x, ENNReal.ofReal (p4m_q x) ∂μ < ⊤ :=
    lt_of_le_of_lt hle (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hC)
  have hint : Integrable p4m_q μ :=
    ⟨hmeas.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall
      fun x => p4m_q_nonneg x)).2 hfin⟩
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => p4m_q_nonneg x)
    hmeas.aestronglyMeasurable]
  have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hC.ne) hle
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Nat.cast_nonneg N)] at this

end HRS.MP.SelfSimP4Mol
