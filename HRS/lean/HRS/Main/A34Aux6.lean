import HRS.Main.A34Aux5

/-!
# Packet A34, helper 6: scale bounds, monotonicity of Sobolev norms, linearity of the propagator
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory
open scoped ENNReal NNReal BigOperators ComplexConjugate RealInnerProductSpace

namespace HRS.A34

open HRS HRS.PDE HRS.PDE.ET HRS.A33 HRS.Main

variable {d : ℕ}

theorem a34_sigma_nonneg {N : ℕ} {κ invβ : ℝ} (hκ : 0 < κ) : 0 ≤ sigmaScale N κ invβ := by
  unfold sigmaScale
  split_ifs
  · exact hκ.le
  · exact le_min hκ.le (Real.sqrt_nonneg _)

theorem a34_sigma_le {N : ℕ} {κ invβ : ℝ} : sigmaScale N κ invβ ≤ κ := by
  unfold sigmaScale
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

theorem a34_qScale_bounds {N : ℕ} (hN : 0 < N) {κ invβ : ℝ} (hκ : 0 < κ) (hβ : 0 ≤ invβ) :
    0 ≤ qScale N κ invβ ∧ qScale N κ invβ ≤ 1 := by
  unfold qScale
  by_cases h0 : invβ = 0
  · simp [h0]
  · simp only [h0, if_false]
    have hinv : 0 < invβ := lt_of_le_of_ne hβ (Ne.symm h0)
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have hσ0 := a34_sigma_nonneg (N := N) (invβ := invβ) hκ
    refine ⟨by positivity, ?_⟩
    have hσle : sigmaScale N κ invβ ≤ Real.sqrt (N / invβ) := by
      unfold sigmaScale
      simp only [h0, if_false]
      exact min_le_right _ _
    have hsq : sigmaScale N κ invβ ^ 2 ≤ N / invβ := by
      calc sigmaScale N κ invβ ^ 2 ≤ (Real.sqrt (N / invβ)) ^ 2 := pow_le_pow_left₀ hσ0 hσle 2
        _ = N / invβ := Real.sq_sqrt (by positivity)
    rw [div_le_one hNr]
    calc sigmaScale N κ invβ ^ 2 * invβ ≤ (N / invβ) * invβ :=
          mul_le_mul_of_nonneg_right hsq hinv.le
      _ = N := by field_simp

theorem a34_Ascale_abs_le {N : ℕ} {κ invβ : ℝ} (hκ : 0 < κ) : |Ascale N κ invβ| ≤ 1 := by
  unfold Ascale
  by_cases h0 : invβ = 0
  · simp [h0]
  · simp only [h0, if_false]
    have hσ0 := a34_sigma_nonneg (N := N) (invβ := invβ) hκ
    have hσκ := a34_sigma_le (N := N) (κ := κ) (invβ := invβ)
    rw [abs_of_nonneg (div_nonneg hσ0 hκ.le), div_le_one hκ]
    exact hσκ

theorem a34_sobolevNorm_mono {a b : ℝ} (hab : a ≤ b) {ψ : Torus d → ℝ} (hψ : MemSobolev b ψ) :
    sobolevNorm a ψ ≤ sobolevNorm b ψ := by
  have hψa : MemSobolev a ψ := MFAdjoint.memSobolev_mono_idx hψ hab
  rw [ClassicalPart.sobolevNorm_eq_hsNorm hψa, ClassicalPart.sobolevNorm_eq_hsNorm hψ]
  exact MFApriori.hsNorm_mono_idx hab (hsNormSq_coeffOf b ψ hψ).1

theorem a34_sobolevNorm_nonneg (a : ℝ) (ψ : Torus d → ℝ) : 0 ≤ sobolevNorm a ψ :=
  Real.sqrt_nonneg _

end HRS.A34
