import HRS.MS.Fp81S21CompatPotentials
import HRS.MS.MovAdjAux24

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole
open HRS.MS.R26T3

/-- The compatible corrector gradients lie in the staged bounded `C_b²`
velocity balls. The factor `3` accounts for the three derivative suprema in
`cbNormVecE 2`. -/
theorem fp81s21_compat_gradient_velocityBall
    {p : Parameters} {δ : ℝ} (R : Trajectory p δ)
    (F : fp81s21_CompatPotentialFamily R)
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 ≤ c)
    (hdecay : ∀ a : Set.Ici (0 : ℝ), ∀ j : ℕ,
      HasCbBound (fp81s21_k0 p.d)
        (C * Real.exp (-c * (a : ℝ)) * r26t3_feature_weight p.d j)
        (gradient ((F a).χ j)))
    (a : Set.Ici (0 : ℝ)) (j : ℕ) :
    IsR2VelocityBall p.d (3 * C * r26t3_feature_weight p.d j)
      (gradient ((F a).χ j)) := by
  let v : Euc p.d → Euc p.d := gradient ((F a).χ j)
  let A : ℝ := C * Real.exp (-c * (a : ℝ)) * r26t3_feature_weight p.d j
  have hk2 : 2 ≤ fp81s21_k0 p.d := by
    unfold fp81s21_k0
    omega
  have hcb := hdecay a j
  have hcont : ContDiff ℝ 2 v := by
    dsimp [v]
    exact hcb.1.of_le (by exact_mod_cast hk2)
  have hweight : 0 ≤ r26t3_feature_weight p.d j := by
    dsimp [r26t3_feature_weight]
    apply mul_nonneg
    · apply Real.rpow_nonneg
      positivity
    · exact Real.rpow_nonneg (oscEigenvalue_pos _).le _
  have hA0 : 0 ≤ C * r26t3_feature_weight p.d j := mul_nonneg hC hweight
  have hexp : Real.exp (-c * (a : ℝ)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have hca : 0 ≤ c * (a : ℝ) := mul_nonneg hc a.2
    linarith
  have hAle : A ≤ C * r26t3_feature_weight p.d j := by
    dsimp [A]
    calc
      C * Real.exp (-c * (a : ℝ)) * r26t3_feature_weight p.d j
          = (C * r26t3_feature_weight p.d j) * Real.exp (-c * (a : ℝ)) := by ring
      _ ≤ (C * r26t3_feature_weight p.d j) * 1 :=
        mul_le_mul_of_nonneg_left hexp hA0
      _ = C * r26t3_feature_weight p.d j := by ring
  have hderiv : ∀ i : ℕ, i ≤ 2 → ∀ x : Euc p.d,
      ‖iteratedFDeriv ℝ i v x‖ ≤ A := by
    intro i hi x
    dsimp [v, A]
    exact hcb.2 i (hi.trans hk2) x
  have hnorm : cbNormVecE 2 v ≤ ENNReal.ofReal (3 * A) := by
    simpa [A, Finset.sum_const, Finset.card_range, nsmul_eq_mul] using
      (HRS.MS.MovAdj.s67_cb_le (j := 2) (v := v) (Y := fun _ => A) hderiv)
  have hnorm' : cbNormVecE 2 v ≤
      ENNReal.ofReal (3 * C * r26t3_feature_weight p.d j) := by
    calc
      cbNormVecE 2 v ≤ ENNReal.ofReal (3 * A) := hnorm
      _ ≤ ENNReal.ofReal (3 * C * r26t3_feature_weight p.d j) :=
        ENNReal.ofReal_le_ofReal (by nlinarith)
  exact ⟨hcont, hnorm'⟩

#print axioms fp81s21_compat_gradient_velocityBall

end HRS.Fp81.S21

end
