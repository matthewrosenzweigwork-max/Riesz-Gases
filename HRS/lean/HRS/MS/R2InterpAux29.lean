import HRS.MS.R2InterpAux28
import HRS.MC.S7PIF6D

/-!
# S10.2 (worker S102), part 29 (packet B1): bilinear expansion and the Gram identity
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MS.CovMeas HRS.MS.FixEq

/-- Expansion of a bounded bilinear form on a sum of vectors. -/
theorem s102_bilin_expand {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {q : ℕ}
    (N : G [×2]→L[ℝ] ℝ) (e : Fin q → G) (v : Fin q → ℝ) :
    N ![∑ k, v k • e k, ∑ k, v k • e k] = ∑ k, ∑ k', v k * v k' * N ![e k, e k'] := by
  classical
  have h1 : (![∑ k, v k • e k, ∑ k, v k • e k] : Fin 2 → G) = fun i => ∑ k, v k • e k := by
    funext i; fin_cases i <;> rfl
  rw [h1, ContinuousMultilinearMap.map_sum (f := N) (g := fun (_ : Fin 2) (k : Fin q) => v k • e k)]
  simp_rw [ContinuousMultilinearMap.map_smul_univ]
  rw [← Fintype.sum_equiv (finTwoArrowEquiv (Fin q)).symm (fun p : Fin q × Fin q => (∏ i : Fin 2, v ((finTwoArrowEquiv (Fin q)).symm p i)) •
      N fun i => e ((finTwoArrowEquiv (Fin q)).symm p i)) _ (fun p => rfl)]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun k' _ => ?_
  simp [finTwoArrowEquiv, Fin.prod_univ_two]
  left
  congr 1
  funext i; fin_cases i <;> rfl

end HRS.MS.R2Interp

end
