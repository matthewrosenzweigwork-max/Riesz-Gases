import HRS.MS.Fp81S21EmbedField10

/-! A compact operator on the coefficient Hilbert space has compact adjoint,
proved here by finite-rank coordinate approximation. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111
  HRS.MS.FixEq
open Filter Topology
open scoped RealInnerProductSpace

/-- The Hilbert adjoint preserves the operator norm. -/
theorem fp81s21_adjoint_opNorm_eq
    (T : r26t6_Coeff →L[ℝ] r26t6_Coeff) :
    ‖T.adjoint‖ = ‖T‖ := by
  have hle : ∀ A : r26t6_Coeff →L[ℝ] r26t6_Coeff,
      ‖A.adjoint‖ ≤ ‖A‖ := by
    intro A
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
    have h := A.adjoint.le_opNorm x
    rwa [LinearIsometryEquiv.norm_map] at h
  apply le_antisymm (hle T)
  have h := hle T.adjoint
  simpa only [ContinuousLinearMap.adjoint_adjoint] using h

/-- The Hilbert adjoint of a compact coefficient operator is compact. -/
theorem fp81s21_adjoint_isCompactOperator
    (T : r26t6_Coeff →L[ℝ] r26t6_Coeff)
    (hT : IsCompactOperator T) :
    IsCompactOperator T.adjoint := by
  have hlim := fp81s21_projectField_comp_tendsto T hT
  have hdiff (m : ℕ) :
      ((T.adjoint.comp (fp81s21_projectField m)) - T.adjoint).adjoint =
        (fp81s21_projectField m).comp T - T := by
    apply ContinuousLinearMap.ext
    intro x
    refine ext_inner_right ℝ fun y => ?_
    rw [ContinuousLinearMap.adjoint_inner_left]
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
      inner_sub_right, inner_sub_left]
    rw [← real_inner_comm x (T.adjoint (fp81s21_projectField m y)),
      ContinuousLinearMap.adjoint_inner_left,
      ← real_inner_comm x (T.adjoint y),
      ContinuousLinearMap.adjoint_inner_left]
    conv_rhs =>
      rw [← fp81s21_projectField_adjoint m]
      rw [ContinuousLinearMap.adjoint_inner_left]
    simp [real_inner_comm]
  have hnorm (m : ℕ) :
      ‖(T.adjoint.comp (fp81s21_projectField m)) - T.adjoint‖ =
        ‖(fp81s21_projectField m).comp T - T‖ := by
    rw [← fp81s21_adjoint_opNorm_eq, hdiff m]
  have hlimAdj :
      Tendsto (fun m => T.adjoint.comp (fp81s21_projectField m)) atTop
        (𝓝 T.adjoint) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h := (tendsto_iff_norm_sub_tendsto_zero).1 hlim
    simpa only [hnorm] using h
  have hcompactApprox : ∀ m : ℕ,
      IsCompactOperator (T.adjoint.comp (fp81s21_projectField m)) := by
    intro m
    exact (fp81s21_projectField_isCompactOperator m).clm_comp T.adjoint
  exact isCompactOperator_of_tendsto hlimAdj (Eventually.of_forall hcompactApprox)

#print axioms HRS.Fp81.S21.fp81s21_adjoint_opNorm_eq
#print axioms HRS.Fp81.S21.fp81s21_adjoint_isCompactOperator

end HRS.Fp81.S21
