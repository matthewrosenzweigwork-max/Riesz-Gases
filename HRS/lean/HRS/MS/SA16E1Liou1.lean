import HRS.MS.SA16E1Red2

/-!
# S.A.16 E1: Jacobi's formula for the derivative of a determinant, and absolute continuity helpers
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16Evolution

/-- Jacobi's formula in row form. -/
theorem e1_hasDerivAt_det {n : ℕ} (R : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (R' : Matrix (Fin n) (Fin n) ℝ) {τ : ℝ}
    (h : ∀ i, HasDerivAt (fun σ => R σ i) (R' i) τ) :
    HasDerivAt (fun σ => (R σ).det) (∑ i, ((R τ).updateRow i (R' i)).det) τ := by
  classical
  let f : ContinuousMultilinearMap ℝ (fun _ : Fin n => Fin n → ℝ) ℝ :=
    { toMultilinearMap :=
        (Matrix.detRowAlternating : (Fin n → ℝ) [⋀^Fin n]→ₗ[ℝ] ℝ).toMultilinearMap
      cont := by
        have : Continuous (fun x : Matrix (Fin n) (Fin n) ℝ => x.det) := continuous_id.matrix_det
        exact this }
  have hf : ∀ x : Fin n → Fin n → ℝ, f x = Matrix.det (Matrix.of x) := fun x => rfl
  have hcurve : HasDerivAt (fun σ => fun i => R σ i) (fun i => R' i) τ := hasDerivAt_pi.2 h
  have hfd := (f.hasFDerivAt (x := fun i => R τ i)).comp_hasDerivAt τ hcurve
  have e1 : (fun σ => f (fun i => R σ i)) = fun σ => (R σ).det := by
    funext σ; rw [hf]; rfl
  rw [show (f ∘ fun σ => fun i => R σ i) = _ from e1] at hfd
  convert hfd using 1
  rw [ContinuousMultilinearMap.linearDeriv_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hf]
  rfl

end HRS.Whole.AppendixA.Phase2SA16Evolution
