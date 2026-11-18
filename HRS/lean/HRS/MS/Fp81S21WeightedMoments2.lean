import HRS.MS.Fp81S21WeightedMoments

/-! A first-moment consequence of the exact weighted chart representation. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory
open scoped ENNReal RealInnerProductSpace

namespace HRS.Fp81.S21

/-- Under a `MomentRep` on a probability space, the dual norm is a.e.
measurable and its first moment is bounded by the square root of the
coefficient second-moment constant. -/
theorem fp81s21_MomentRep_firstMoment
    {d r : ℕ} {Pw : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (E : HRS.MS.R26T6.r26t6_WeightedChart d r Pw)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Q : ℝ → Ω → (HRS.Euc d → ℝ) → ℝ)
    (q : ℝ → Ω → HRS.MS.R26T6.r26t6_Coeff) (M : ℝ)
    (hrep : fp81s21_MomentRep E P Q q M) (u : ℝ) (hu : 0 ≤ u) :
    AEMeasurable (fun ω => HRS.Whole.dualNormE r Pw (Q u ω)) P ∧
      (∫⁻ ω, HRS.Whole.dualNormE r Pw (Q u ω) ∂P) ≤ ENNReal.ofReal (Real.sqrt M) := by
  let hsec := hrep.2 u hu
  have hq : MemLp (q u) 2 P := hsec.1
  have hsecond : (∫ ω, ‖q u ω‖ ^ 2 ∂P) ≤ M := hsec.2.1
  have hfields := hsec.2.2
  have hnormEq : (fun ω => HRS.Whole.dualNormE r Pw (Q u ω)) =ᵐ[P]
      (fun ω => ENNReal.ofReal ‖q u ω‖) := by
    filter_upwards [hfields] with ω hω
    exact hω.2
  have hqMeas : Measurable (q u) := by
    exact hrep.1.comp (measurable_const.prodMk measurable_id)
  have hbaseMeas : Measurable (fun ω => ENNReal.ofReal ‖q u ω‖) :=
    ENNReal.measurable_ofReal.comp (measurable_norm.comp hqMeas)
  have hdualMeas : AEMeasurable
      (fun ω => HRS.Whole.dualNormE r Pw (Q u ω)) P :=
    hbaseMeas.aemeasurable.congr hnormEq.symm
  have hqnorm : MemLp (fun ω => ‖q u ω‖) (ENNReal.ofReal 2) P := by
    simpa using hq.norm
  have hone : MemLp (fun _ : Ω => (1 : ℝ)) (ENNReal.ofReal 2) P := by
    simpa using (memLp_const 1 : MemLp (fun _ : Ω => (1 : ℝ)) 2 P)
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := P) (p := 2) (q := 2) Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall fun _ => (show 0 ≤ (1 : ℝ) by norm_num))
    (Filter.Eventually.of_forall fun ω => norm_nonneg (q u ω)) hone hqnorm
  have hMean : (∫ ω, ‖q u ω‖ ∂P) ≤ Real.sqrt M := by
    have hCS' : (∫ ω, ‖q u ω‖ ∂P) ≤
        Real.sqrt (∫ ω, ‖q u ω‖ ^ 2 ∂P) := by
      simpa [Real.sqrt_eq_rpow, IsProbabilityMeasure.measure_univ] using hCS
    exact hCS'.trans (Real.sqrt_le_sqrt hsecond)
  have hqNormIntegrable : Integrable (fun ω => ‖q u ω‖) P :=
    hqnorm.integrable (by norm_num)
  have hIntegral :
      (∫⁻ ω, ENNReal.ofReal ‖q u ω‖ ∂P) =
        ENNReal.ofReal (∫ ω, ‖q u ω‖ ∂P) := by
    exact (ofReal_integral_eq_lintegral_ofReal hqNormIntegrable
      (Filter.Eventually.of_forall fun ω => norm_nonneg (q u ω))).symm
  refine ⟨hdualMeas, ?_⟩
  calc
    (∫⁻ ω, HRS.Whole.dualNormE r Pw (Q u ω) ∂P) =
        ∫⁻ ω, ENNReal.ofReal ‖q u ω‖ ∂P := lintegral_congr_ae hnormEq
    _ = ENNReal.ofReal (∫ ω, ‖q u ω‖ ∂P) := hIntegral
    _ ≤ ENNReal.ofReal (Real.sqrt M) :=
      ENNReal.ofReal_le_ofReal hMean

#print axioms HRS.Fp81.S21.fp81s21_MomentRep_firstMoment

end HRS.Fp81.S21
