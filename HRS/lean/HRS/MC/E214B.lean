import HRS.Main.HeadlineEdgeworth
import HRS.Sections.AdjKDFinal
import HRS.Prob.Metrics

/-!
# Packet e214b: the analytic core of uniqueness of the window Edgeworth tensor

`e214_tensor_diff_cube`: if `K, K'` both satisfy the expansion clause of `IsWindowEdgeworth`, then
`(K a - K' a)` vanishes on every cube `L ⊗ L ⊗ L`.  Test functions `Φ = (1/6) sin (t L)` have the
constant third derivative direction `L^{⊗3}`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E214B

open HRS HRS.Main

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]

/-- The product trilinear form (same definition as `HRS.MC.E213U18.trilin`). -/
def trilin (ℓ : Fin 3 → B →L[ℝ] ℝ) : B [×3]→L[ℝ] ℝ :=
  (ContinuousMultilinearMap.mkPiAlgebraFin ℝ 3 ℝ).compContinuousLinearMap ℓ

theorem trilin_apply (ℓ : Fin 3 → B →L[ℝ] ℝ) (x : Fin 3 → B) :
    trilin ℓ x = ℓ 0 (x 0) * ℓ 1 (x 1) * ℓ 2 (x 2) := by
  simp [trilin, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebraFin_apply, List.ofFn_succ, mul_assoc]

/-- The third Fréchet derivative of `sin` on `ℝ`. -/
theorem iteratedFDeriv_three_sin (u : ℝ) :
    iteratedFDeriv ℝ 3 Real.sin u =
      (-Real.cos u) • (ContinuousMultilinearMap.mkPiAlgebraFin ℝ 3 ℝ) := by
  apply ContinuousMultilinearMap.ext_ring
  have h := iteratedDeriv_eq_iteratedFDeriv (𝕜 := ℝ) (n := 3) (f := Real.sin) (x := u)
  have h3 : iteratedDeriv 3 Real.sin u = -Real.cos u := by
    have : iteratedDeriv 3 Real.sin = fun u => -Real.cos u := by
      rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one]
      funext u
      simp [Real.deriv_sin, deriv_cos]
    simp [this]
  rw [← h, h3]
  simp [ContinuousMultilinearMap.mkPiAlgebraFin_apply]

/-- Third derivative of `z ↦ c * sin (L z)`: the constant direction `L ⊗ L ⊗ L`. -/
theorem iteratedFDeriv_three_const_mul_sin (L : StrongDual ℝ B) (c : ℝ) (z : B) :
    iteratedFDeriv ℝ 3 (fun z => c * Real.sin (L z)) z =
      (-(c * Real.cos (L z))) • trilin ![L, L, L] := by
  have hcd : ContDiff ℝ 3 (Real.sin ∘ L) := Real.contDiff_sin.comp L.contDiff
  have e : (fun z => c * Real.sin (L z)) = c • (Real.sin ∘ L) := by
    funext z; simp
  rw [e, iteratedFDeriv_const_smul_apply (hcd.of_le le_rfl).contDiffAt]
  have h2 := L.iteratedFDeriv_comp_right (Real.contDiff_sin (n := 3)) z (i := 3) le_rfl
  rw [h2, iteratedFDeriv_three_sin]
  ext x
  simp [trilin_apply, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebraFin_apply, List.ofFn_succ]
  ring

end HRS.MC.E214B
