import HRS.MS.Fp81S21GaussianQuadraticHilbert3

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology
open scoped ENNReal BigOperators
open HRS HRS.MC.E213U13 HRS.MS.R26T6
namespace HRS.Fp81.S21

/-- A bounded chart map transports the uniform moment estimate and finite
polynomial approximations on the retained sequence. -/
theorem fp81s21_InQ2_coeff_map_uniform
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : ℕ → Ω → ℝ} (hξ : IsStdGaussianSeq P ξ)
    (q : ℝ → Ω → r26t6_Coeff) (M : ℝ) (hM : 0 ≤ M)
    (hq : ∀ u, 0 ≤ u → MemLp (q u) 2 P ∧
      (∫ ω, ‖q u ω‖ ^ 2 ∂P) ≤ M ∧
      ∀ j, InQ2 hξ (fun ω => q u ω j))
    (A : r26t6_Coeff →L[ℝ] r26t6_Coeff) (hA : ‖A‖ ≤ 1) :
    ∃ M4 : ℝ, 0 ≤ M4 ∧ ∀ u, 0 ≤ u →
      MemLp (fun ω => A (q u ω)) 4 P ∧
      (∫ ω, ‖A (q u ω)‖ ^ 4 ∂P) ≤ M4 ∧
      ∃ (N : ℕ → ℕ → ℕ) (c : ℕ → ℕ → ℕ → ℕ → ℝ),
        Tendsto (fun n => eLpNorm (fun ω =>
          (∑ j ∈ Finset.range n, quadSum (c n j) ξ (N n j) ω • fp81s21_coeffBasis j) - A (q u ω))
          4 P) atTop (𝓝 0) := by
  refine ⟨15 * M ^ 2, by positivity, ?_⟩
  intro u hu
  obtain ⟨hqu, hE, hc⟩ := hq u hu
  have hAq : MemLp (fun ω => A (q u ω)) 2 P := A.comp_memLp' hqu
  have hEn : (∫ ω, ‖A (q u ω)‖ ^ 2 ∂P) ≤ M := by
    calc
      _ ≤ ∫ ω, ‖q u ω‖ ^ 2 ∂P := by
        apply integral_mono (hAq.integrable_norm_pow') (hqu.integrable_norm_pow')
        intro ω
        have hb : ‖A (q u ω)‖ ≤ ‖q u ω‖ :=
          (A.le_opNorm _).trans (by nlinarith [norm_nonneg (q u ω)])
        exact pow_le_pow_left₀ (norm_nonneg _) hb 2
      _ ≤ M := hE
  have hcoord : ∀ j, InQ2 hξ (fun ω => A (q u ω) j) := fun j =>
    fp81s21_InQ2_coeff_functional hξ (q u) hqu hc
      ((lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 j).comp A)
  have h4 := fp81s21_InQ2_coeff_fourth hξ (fun ω => A (q u ω)) hAq hcoord
  refine ⟨h4.1, h4.2.trans ?_, fp81s21_InQ2_coeff_L4_polynomials hξ _ hAq hcoord⟩
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (integral_nonneg fun ω => sq_nonneg _) hEn 2) (by norm_num)

#print axioms fp81s21_InQ2_coeff_map_uniform
end HRS.Fp81.S21
end
