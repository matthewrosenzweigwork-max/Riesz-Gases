import HRS.MS.Fp81S21JointW2
import HRS.MS.Fp81S21GaussModification
import HRS.MS.Fp81S21WickApprox26

/-! Jointly measurable raw Gaussian polynomial fields. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter
open scoped BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111

/-- The finite-rank polynomial is continuous in the oscillator dual. -/
theorem fp81s21_polyAt_continuous {d : ℕ} (D : fp81s21_RankKernel d) :
    Continuous (fp81s21_polyAt D) := by
  have heval : ∀ i, Continuous (fun x : OscDual d (wholeSpaceIndex d : ℝ) =>
      OscDual.eval x (D.u i)) := by
    intro i
    let φ : HRS.MS.S111X1.oscSub d (wholeSpaceIndex d : ℝ) :=
      ⟨D.u i, fp81s21_isOscTest_of_r2 D.valid i⟩
    have heq : (fun x : OscDual d (wholeSpaceIndex d : ℝ) => OscDual.eval x (D.u i)) =
        fun x => gaussianOscEval φ x := by
      funext x
      exact (gaussianOscEval_apply φ x).symm
    rw [heq]
    exact (gaussianOscEval φ).continuous
  unfold fp81s21_polyAt
  exact continuous_const.mul (continuous_finset_sum _ fun i _ =>
    continuous_finset_sum _ fun j _ => (continuous_const.mul (heval i)).mul (heval j))

/-- One jointly measurable version realizes all raw polynomial coordinates
simultaneously at all nonnegative times on a common probability-one event. -/
theorem fp81s21_rawPolynomial_joint_field
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ) (G : GaussianRealization R)
    (m : ℕ) (D : Fin m → fp81s21_RankKernel p.d) :
    ∃ r : ℝ → G.Ω → r26t6_Coeff,
      Measurable (Function.uncurry r) ∧
      ∀ᵐ ω ∂G.P, ∀ u, 0 ≤ u →
        r u ω = ∑ j : Fin m, fp81s21_polyAt (D j) (G.Z u ω) • fp81s21_coeffBasis j := by
  obtain ⟨Zbar, hZbar, _, hZbarEq⟩ := fp81s21_gauss_modification p R G
  let r : ℝ → G.Ω → r26t6_Coeff := fun u ω =>
    ∑ j : Fin m, fp81s21_polyAt (D j) (Zbar u ω) • fp81s21_coeffBasis j
  refine ⟨r, ?_, ?_⟩
  · exact Finset.measurable_sum _ fun j _ =>
      ((fp81s21_polyAt_continuous (D j)).measurable.comp hZbar).smul measurable_const
  · filter_upwards [hZbarEq] with ω hω u hu
    simp [r, hω u hu]

#print axioms fp81s21_polyAt_continuous
#print axioms fp81s21_rawPolynomial_joint_field
end HRS.Fp81.S21
end
