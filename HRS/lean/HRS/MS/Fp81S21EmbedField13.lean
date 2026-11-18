import HRS.MS.Fp81S21EmbedField12

/-! The compact field embedding has an operator-norm coordinate projection
profile tending to zero. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111
  HRS.MS.FixEq
open Filter Topology
open scoped RealInnerProductSpace

/-- The finite coordinate projections approximate the field embedding in
operator norm, with a nonnegative error tending to zero. -/
theorem fp81s21_embedField_projectionProfile
    {d q : ℕ} {Pw : ℝ}
    (hP : (d : ℝ) < 2 * Pw)
    (hPs : (d : ℝ) < 2 * (Pw + 2))
    (Es : r26t6_WeightedChart d q (Pw + 2))
    (E : r26t6_WeightedChart d (q + 2) Pw) :
    ∃ ε : ℕ → ℝ,
      (∀ m, 0 ≤ ε m) ∧
      Tendsto ε atTop (𝓝 0) ∧
      ∀ m, ‖fp81s21_embedField hP hPs Es E -
        (fp81s21_projectField m).comp (fp81s21_embedField hP hPs Es E)‖ ≤ ε m := by
  let K := fp81s21_embedField hP hPs Es E
  have hK : IsCompactOperator K :=
    fp81s21_embedField_isCompactOperator hP hPs Es E
  have hproj := fp81s21_projectField_comp_tendsto K hK
  let ε : ℕ → ℝ := fun m => ‖K - (fp81s21_projectField m).comp K‖
  refine ⟨ε, ?_, ?_, ?_⟩
  · intro m
    exact norm_nonneg _
  · have hnorm := (tendsto_iff_norm_sub_tendsto_zero).1 hproj
    have heq : ∀ m, ε m =
        ‖(fp81s21_projectField m).comp K - K‖ := by
      intro m
      dsimp [ε]
      exact norm_sub_rev _ _
    exact hnorm.congr' (Filter.Eventually.of_forall fun m => (heq m).symm)
  · intro m
    dsimp [ε]
    exact le_rfl

#print axioms HRS.Fp81.S21.fp81s21_embedField_projectionProfile

end HRS.Fp81.S21
