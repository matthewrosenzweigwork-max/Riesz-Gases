import HRS.MS.Fp81S21FutureIndep39
import HRS.MS.R2InterpAux4

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Set Classical
open scoped ENNReal NNReal BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R2Interp

/-- Heat derivatives along a measurable prediction and an integrable increment.
The bound includes the norms of all derivative directions. -/
theorem fp81s21_heat_derivative_increment
    {d : ℕ} {m H : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (γ : ℝ → Measure (OscPath d m H)) (r : ℝ) [IsProbabilityMeasure (γ r)]
    (Φ : OscPath d m H → ℝ) (hΦ : MemCb 5 Φ)
    (j : ℕ) (hj : j ≤ 5) (h : Fin j → OscPath d m H)
    (Y : Ω → OscPath d m H) (hY : Measurable Y)
    (D : Ω → ℝ) (hD : Integrable D P) :
    let C := (⨆ z, ‖iteratedFDeriv ℝ j Φ z‖) * ∏ i, ‖h i‖
    (∀ ω, iteratedFDeriv ℝ j (r2HeatFn γ Φ r) (Y ω) h =
      ∫ z, iteratedFDeriv ℝ j Φ (Y ω + z) h ∂(γ r)) ∧
    Integrable (fun ω => D ω * iteratedFDeriv ℝ j (r2HeatFn γ Φ r) (Y ω) h) P ∧
    ‖∫ ω, D ω * iteratedFDeriv ℝ j (r2HeatFn γ Φ r) (Y ω) h ∂P‖ ≤
      C * ∫ ω, ‖D ω‖ ∂P := by
  dsimp only
  let L := ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => OscPath d m H) ℝ h
  have hcont : Continuous (iteratedFDeriv ℝ j Φ) :=
    hΦ.1.continuous_iteratedFDeriv (m := j) (by exact_mod_cast hj)
  have hformula := s102_r2HeatFn_derivs γ r hΦ
  have hb : ∀ y, ‖iteratedFDeriv ℝ j (r2HeatFn γ Φ r) y h‖ ≤
      (⨆ z, ‖iteratedFDeriv ℝ j Φ z‖) * ∏ i, ‖h i‖ := by
    intro y
    exact ((iteratedFDeriv ℝ j (r2HeatFn γ Φ r) y).le_opNorm h).trans
      (mul_le_mul_of_nonneg_right ((hformula.2 j hj y).2) (Finset.prod_nonneg fun _ _ => norm_nonneg _))
  have hm : Measurable (fun ω => iteratedFDeriv ℝ j (r2HeatFn γ Φ r) (Y ω) h) := by
    exact (L.continuous.comp (hformula.1.continuous_iteratedFDeriv (m := j)
      (by exact_mod_cast hj))).measurable.comp hY
  have hi : Integrable (fun ω => D ω * iteratedFDeriv ℝ j (r2HeatFn γ Φ r) (Y ω) h) P :=
    by simpa only [mul_comm] using
      hD.bdd_mul hm.aestronglyMeasurable (Eventually.of_forall fun ω => hb (Y ω))
  refine ⟨?_, hi, ?_⟩
  · intro ω
    rw [(hformula.2 j hj (Y ω)).1]
    have hz : Integrable (fun z => iteratedFDeriv ℝ j Φ (Y ω + z)) (γ r) := by
      refine Integrable.of_bound (C := ⨆ z, ‖iteratedFDeriv ℝ j Φ z‖) ?_ ?_
      · exact (hcont.comp (by fun_prop)).aestronglyMeasurable
      · exact Eventually.of_forall fun z => s102_le_sup hΦ hj _
    exact (L.integral_comp_comm hz).symm
  · refine (norm_integral_le_integral_norm _).trans ?_
    rw [← integral_const_mul]
    apply integral_mono_ae hi.norm (hD.norm.const_mul _)
    exact Eventually.of_forall fun ω => by
      dsimp only
      rw [norm_mul]
      simpa [mul_comm] using mul_le_mul_of_nonneg_left (hb (Y ω)) (norm_nonneg (D ω))

#print axioms fp81s21_heat_derivative_increment
end HRS.Fp81.S21
end
