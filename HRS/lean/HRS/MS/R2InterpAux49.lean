import HRS.MS.R2InterpAux48

/-!
# S10.2 (worker S102), part 49 (packet F9, helpers): the second derivative of the cylindrical heat function as a combination of products of evaluations, and the value of `𝒥` on them
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MS.CovMeas HRS.MC.Sec7.S7PIF6

variable {d : ℕ} {C : WholeCoeff d} {m T : ℝ}

/-- The product of two evaluations as a bounded bilinear form. -/
def s102_gen {q : ℕ} (τ : Fin q → Icc (0 : ℝ) T) (α : Fin q → MultiIndex d) (i j : Fin q) :
    OscPath d m T [×2]→L[ℝ] ℝ :=
  (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 2) ℝ).compContinuousLinearMap
    ![s102_ell (τ i) (α i), s102_ell (τ j) (α j)]

theorem s102_cyl_expand {q : ℕ} (τ : Fin q → Icc (0 : ℝ) T) (α : Fin q → MultiIndex d)
    (f : EuclideanSpace ℝ (Fin q) → ℝ) (c : EuclideanSpace ℝ (Fin q)) :
    (iteratedFDeriv ℝ 2 f c).compContinuousLinearMap (fun _ => s102_obs τ α) =
      ∑ i, ∑ j, iteratedFDeriv ℝ 2 f c ![EuclideanSpace.single i 1, EuclideanSpace.single j 1] •
        s102_gen (m := m) τ α i j := by
  ext x
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  simp only [ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.smul_apply, s102_gen,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, ContinuousMultilinearMap.mkPiAlgebra_apply,
    Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul, s102_ell_apply]
  rw [iteratedFDeriv_two_apply]
  have hB := S7PIF6_bilin_expand (fderiv ℝ (fderiv ℝ f) c) (s102_obs τ α (x 0)) (s102_obs τ α (x 1))
  simp only [Function.comp_apply] at hB ⊢
  rw [hB]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, s102_obs_apply]
  ring

theorem s102_isCombo_osc (m : ℝ) (α : MultiIndex d) : IsR2DualCombo m (oscTestFun m α) :=
  ⟨{α}, fun _ => 1, by funext x; simp⟩

/-- The value of a covariance tensor on a product of two evaluations. -/
theorem s102_J_gen {z : ℝ → (Euc d → ℝ) → ℝ} {I : Set ℝ} {J : TensorDual (OscPath d m T) 2}
    (hJ : IsR2JValue C m T z I J) {q : ℕ} (τ : Fin q → Icc (0 : ℝ) T) (α : Fin q → MultiIndex d) (i j : Fin q) :
    J (s102_gen (m := m) τ α i j) = 2 * C.ν * ∫ u in I ∩ Icc (0 : ℝ) (min (τ i : ℝ) (τ j : ℝ)), z u (fun x =>
      inner ℝ (gradient (propagatorW C u (τ i) (oscTestFun m (α i))) x)
        (gradient (propagatorW C u (τ j) (oscTestFun m (α j))) x)) := by
  refine hJ.2 (τ i) (τ j) (oscTestFun m (α i)) (oscTestFun m (α j)) (s102_ell (τ i) (α i)) (s102_ell (τ j) (α j))
    (s102_isCombo_osc m _) (s102_isCombo_osc m _) (τ i).2 (τ j).2 (fun w => ?_) (fun w => ?_)
  · rw [s102_ell_apply, s102_ellp_eval']
  · rw [s102_ell_apply, s102_ellp_eval']

end HRS.MS.R2Interp

end
