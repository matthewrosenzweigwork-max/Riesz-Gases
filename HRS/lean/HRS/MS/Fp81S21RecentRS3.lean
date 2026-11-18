import HRS.MS.Fp81S21RecentRS2
import HRS.MS.S21G2_S26

/-!
# S2.1(iii), packet 34a: mixed-coupling RS expectation bound

This file records the generic dual-map interface needed by the Wasserstein
adapter and derives the mixed expectation estimate from the staged R26 mixed
coupling theorem.  The positive RS constant is harmless: a zero operator bound
can always be replaced by any positive larger bound.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.Fp81.S21

/-- A uniformly bounded, path-Lipschitz family of linear RS functionals on a
variation Banach space. -/
structure fp81s21_RecentRSKernel
    (C V : Type*) [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (C_RS : ℝ) where
  kernel : C → V →L[ℝ] ℝ
  bound : ∀ y, ‖kernel y‖ ≤ C_RS
  lipschitz : ∀ y y', ‖kernel y - kernel y'‖ ≤ C_RS * ‖y - y'‖

/-- The mixed-coupling bound for a bounded linear functional family. -/
theorem fp81s21_recentRS_mixed_expectation
    {C V Ω : Type*} [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace C] [BorelSpace C]
    [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {C_RS : ℝ} (hC : 0 < C_RS)
    (F : fp81s21_RecentRSKernel C V C_RS)
    (X Y : Ω → C) (A A' : Ω → V)
    (hm : AEStronglyMeasurable X P ∧ AEStronglyMeasurable Y P ∧
      AEStronglyMeasurable A P ∧ AEStronglyMeasurable A' P)
    (h2 : MemLp (fun ω => X ω - Y ω) 2 P ∧ MemLp A 2 P ∧ MemLp A' 2 P) :
    |(∫ ω, F.kernel (X ω) (A ω) ∂P) -
      (∫ ω, F.kernel (Y ω) (A' ω) ∂P)| ≤
      C_RS * ((∫ ω, ‖A ω - A' ω‖ ∂P) +
        Real.sqrt (∫ ω, ‖A' ω‖ ^ 2 ∂P) *
          Real.sqrt (∫ ω, ‖X ω - Y ω‖ ^ 2 ∂P)) := by
  let G : C → V →L[ℝ] ℝ := fun y => C_RS⁻¹ • F.kernel y
  have hGbound : ∀ y, ‖G y‖ ≤ 1 := by
    intro y
    change ‖C_RS⁻¹ • F.kernel y‖ ≤ 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hC)]
    calc
      C_RS⁻¹ * ‖F.kernel y‖ ≤ C_RS⁻¹ * C_RS :=
        mul_le_mul_of_nonneg_left (F.bound y) (le_of_lt (inv_pos.mpr hC))
      _ = 1 := by field_simp
  have hGlip : ∀ y y', ‖G y - G y'‖ ≤ ‖y - y'‖ := by
    intro y y'
    change ‖(C_RS⁻¹ • F.kernel y) - (C_RS⁻¹ • F.kernel y')‖ ≤ ‖y - y'‖
    have hsub : (C_RS⁻¹ • F.kernel y) - (C_RS⁻¹ • F.kernel y') =
        C_RS⁻¹ • (F.kernel y - F.kernel y') := by module
    rw [hsub, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hC)]
    calc
      C_RS⁻¹ * ‖F.kernel y - F.kernel y'‖ ≤
          C_RS⁻¹ * (C_RS * ‖y - y'‖) :=
        mul_le_mul_of_nonneg_left (F.lipschitz y y') (le_of_lt (inv_pos.mpr hC))
      _ = ‖y - y'‖ := by field_simp
  have hGmeas : Continuous G := by
    apply LipschitzWith.continuous
    exact LipschitzWith.of_dist_le_mul (K := (1 : ℝ≥0)) fun y y' => by
      simpa [dist_eq_norm] using hGlip y y'
  have hEvalMeas (U : Ω → C) (W : Ω → V)
      (hU : AEStronglyMeasurable U P) (hW : AEStronglyMeasurable W P) :
      AEStronglyMeasurable (fun ω => G (U ω) (W ω)) P := by
    have hEval : Continuous fun z : (V →L[ℝ] ℝ) × V => z.1 z.2 :=
      (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := V) (F := ℝ)).continuous
    exact hEval.comp_aestronglyMeasurable ((hGmeas.comp_aestronglyMeasurable hU).prodMk hW)
  have hGint (U : Ω → C) (W : Ω → V)
      (hU : AEStronglyMeasurable U P) (hW : AEStronglyMeasurable W P)
      (hWnorm : Integrable (fun ω => ‖W ω‖) P) :
      Integrable (fun ω => G (U ω) (W ω)) P :=
    hWnorm.mono' (hEvalMeas U W hU hW) (ae_of_all P fun ω => by
      calc
        ‖G (U ω) (W ω)‖ ≤ ‖G (U ω)‖ * ‖W ω‖ := (G (U ω)).le_opNorm _
        _ ≤ 1 * ‖W ω‖ := by gcongr; exact hGbound _
        _ = ‖W ω‖ := one_mul _)
  obtain ⟨hX, hY, hA, hA'⟩ := hm
  obtain ⟨hXY, hA2, hA'2⟩ := h2
  have hAint : Integrable (fun ω => ‖A ω‖) P := (hA2.norm.integrable one_le_two)
  have hA'int : Integrable (fun ω => ‖A' ω‖) P := (hA'2.norm.integrable one_le_two)
  have hG1 := hGint X A hX hA hAint
  have hG2 := hGint Y A' hY hA' hA'int
  have hEq1 : (fun ω => G (X ω) (A ω)) = fun ω => C_RS⁻¹ * F.kernel (X ω) (A ω) := by
    funext ω
    simp [G]
  have hEq2 : (fun ω => G (Y ω) (A' ω)) = fun ω => C_RS⁻¹ * F.kernel (Y ω) (A' ω) := by
    funext ω
    simp [G]
  have hscaled :
      |(∫ ω, G (X ω) (A ω) ∂P) - (∫ ω, G (Y ω) (A' ω) ∂P)| ≤
        (∫ ω, ‖A ω - A' ω‖ ∂P) +
          Real.sqrt (∫ ω, ‖A' ω‖ ^ 2 ∂P) *
            Real.sqrt (∫ ω, ‖X ω - Y ω‖ ^ 2 ∂P) := by
    exact HRS.MS.R26T3.r26t3_mixed_coupling P X Y A A' G hGbound hGlip
      ⟨hX, hY, hA, hA'⟩ ⟨hXY, hA2, hA'2⟩
  have hscaleEq :
      |(∫ ω, G (X ω) (A ω) ∂P) - (∫ ω, G (Y ω) (A' ω) ∂P)| =
        C_RS⁻¹ * |(∫ ω, F.kernel (X ω) (A ω) ∂P) -
          (∫ ω, F.kernel (Y ω) (A' ω) ∂P)| := by
    rw [hEq1, hEq2, integral_const_mul, integral_const_mul]
    rw [← mul_sub, abs_mul, abs_of_pos (inv_pos.mpr hC)]
  calc
    |(∫ ω, F.kernel (X ω) (A ω) ∂P) -
        (∫ ω, F.kernel (Y ω) (A' ω) ∂P)| =
        C_RS * (C_RS⁻¹ * |(∫ ω, F.kernel (X ω) (A ω) ∂P) -
          (∫ ω, F.kernel (Y ω) (A' ω) ∂P)|) := by field_simp
    _ ≤ C_RS * ((∫ ω, ‖A ω - A' ω‖ ∂P) +
          Real.sqrt (∫ ω, ‖A' ω‖ ^ 2 ∂P) *
            Real.sqrt (∫ ω, ‖X ω - Y ω‖ ^ 2 ∂P)) := by
      rw [← hscaleEq]
      exact mul_le_mul_of_nonneg_left hscaled hC.le

#print axioms fp81s21_recentRS_mixed_expectation

end HRS.Fp81.S21

end
