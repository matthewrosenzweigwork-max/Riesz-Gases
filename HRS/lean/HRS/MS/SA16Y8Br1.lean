import HRS.MS.SA16Y8Rp5

/-!
# S.A.16 (SA16Y8) Br1: bridging `iteratedFDeriv ℝ j`, `j ≤ 2`, with `fderiv`, `D2` (classical clause, K4, part 2)

`sa16y8_iter1_eq`: `iteratedFDeriv ℝ 1 f x = Θ₁.symm (fderiv ℝ f x)` with the linear isometry `Θ₁`.
`sa16y8_Psi`, `sa16y8_iter2_eq`: `iteratedFDeriv ℝ 2 f x = Ψ (D2 f x)` for `C²` `f`, `Ψ` a continuous linear map (independent of `f`, `x`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16Q
open HRS HRS.Whole HRS.Whole.AppendixA

section Br1
variable {d : ℕ}

lemma sa16y8_iter1_eq (f : Euc d → ℝ) (x : Euc d) :
    iteratedFDeriv ℝ 1 f x = (continuousMultilinearCurryFin1 ℝ (Euc d) ℝ).symm (fderiv ℝ f x) := by
  ext m
  simp [iteratedFDeriv_one_apply]

set_option synthInstance.maxHeartbeats 400000 in
/-- the continuous linear map taking the nested second derivative to the multilinear one -/
def sa16y8_Psi (d : ℕ) : (Euc d →L[ℝ] (Euc d →L[ℝ] ℝ)) →L[ℝ] (Euc d [×2]→L[ℝ] ℝ) :=
  (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 2 => Euc d) ℝ).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (ContinuousLinearMap.compL ℝ (Euc d) (Euc d →L[ℝ] ℝ) (Euc d [×1]→L[ℝ] ℝ)
      (continuousMultilinearCurryFin1 ℝ (Euc d) ℝ).symm.toContinuousLinearEquiv.toContinuousLinearMap)

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
lemma sa16y8_iter2_eq {f : Euc d → ℝ} (hf : ContDiff ℝ 2 f) (x : Euc d) :
    iteratedFDeriv ℝ 2 f x = sa16y8_Psi d (sa16y8_D2 f x) := by
  ext m
  rw [iteratedFDeriv_two_apply]
  simp only [sa16y8_Psi, sa16y8_D2, ContinuousLinearMap.coe_comp', Function.comp_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, ContinuousLinearEquiv.coe_coe,
    continuousMultilinearCurryLeftEquiv_symm_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.comp_apply, continuousMultilinearCurryFin1_symm_apply, Fin.tail]
  rfl

end Br1

end HRS.Whole.AppendixA.Phase2SA16Q
