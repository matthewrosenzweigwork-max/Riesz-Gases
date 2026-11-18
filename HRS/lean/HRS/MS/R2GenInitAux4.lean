import HRS.MS.R2GenInitAux3

/-!
# S10.5 packet G0'': monotonicity of `generalLocalizationRate` in the second-moment bound

`s105_glr_mono`: if `1 + M₂ ≤ K (1 + M₃)` with `K ≥ 1` then
`generalLocalizationRate d E M₂ N ≤ K · generalLocalizationRate d E M₃ N` (for `E ≥ 0`, `M₃ ≥ 0`): replaces the second-moment bound
`C(1 + B_N/N)` of S10.5 by the `B_N/N` of the displayed `w_N^{ent}`.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace HRS.MS.R2GenInit

open HRS.Whole

theorem s105_glr_mono (d N : ℕ) (E M₂ M₃ K : ℝ) (hE : 0 ≤ E) (hM₂ : 0 ≤ M₂) (hM₃ : 0 ≤ M₃) (hK : 1 ≤ K)
    (h : 1 + M₂ ≤ K * (1 + M₃)) :
    generalLocalizationRate d E M₂ N ≤ K * generalLocalizationRate d E M₃ N := by
  have hK0 : 0 < K := by linarith
  unfold generalLocalizationRate
  haveI : Nonempty {R : ℝ // 1 ≤ R} := ⟨⟨1, le_rfl⟩⟩
  have hbdd₂ : BddBelow (Set.range (fun R : {R : ℝ // 1 ≤ R} =>
      R.1 ^ ((d : ℝ) / 2) * ((N : ℝ) ^ (-(1 / (d : ℝ))) + Real.sqrt E) + (1 + M₃) * R.1 ^ (-(2 : ℝ)))) :=
    ⟨0, by
      rintro _ ⟨R, rfl⟩
      have : 0 < R.1 := by linarith [R.2]
      positivity⟩
  have hbdd₁ : BddBelow (Set.range (fun R : {R : ℝ // 1 ≤ R} =>
      R.1 ^ ((d : ℝ) / 2) * ((N : ℝ) ^ (-(1 / (d : ℝ))) + Real.sqrt E) + (1 + M₂) * R.1 ^ (-(2 : ℝ)))) := by
    refine ⟨-(0 : ℝ) , ?_⟩
    rintro _ ⟨R, rfl⟩
    have : 0 < R.1 := by linarith [R.2]
    simp only [neg_zero]
    positivity
  rw [← div_le_iff₀' hK0]
  refine le_ciInf fun R => ?_
  rw [div_le_iff₀' hK0]
  refine (ciInf_le hbdd₁ R).trans ?_
  have hRpos : 0 < R.1 := by linarith [R.2]
  have h1 : 0 ≤ R.1 ^ ((d : ℝ) / 2) * ((N : ℝ) ^ (-(1 / (d : ℝ))) + Real.sqrt E) := by positivity
  have h2 : 0 ≤ R.1 ^ (-(2 : ℝ)) := Real.rpow_nonneg hRpos.le _
  nlinarith [mul_le_mul_of_nonneg_right h h2]

end HRS.MS.R2GenInit
