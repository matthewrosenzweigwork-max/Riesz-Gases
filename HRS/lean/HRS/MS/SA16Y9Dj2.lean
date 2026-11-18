import HRS.MS.SA16Y9Dj1
import HRS.MS.SA16V2Calc

/-!
# S.A.16 (SA16Y9) Dj2: `D(jetEnergy)_v (S) ≤ p E(v)^{1/p'} E(S)^{1/p}` (stability, P1, part 2)
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.Whole.AppendixA.Phase2SA16S
open HRS.Whole.AppendixA.Phase2SA16V HRS.Whole.AppendixA.Phase2SA16V2
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16Transfer

section Dj2
variable (d k : ℕ) (p : ℝ) [Fact (2 ≤ p)]

theorem sa16y9_Dj_le (v S : WmpSpace d k p) :
    sa16v2_Dj d k p v S ≤ p * ((jetEnergy d k p v) ^ (1 / Real.conjExponent p) * (jetEnergy d k p S) ^ (1 / p)) := by
  have hp2 : (2 : ℝ) ≤ p := Fact.out
  have hp1 : 1 < p := by linarith
  have hp0 : 0 < p := by linarith
  have hH := Real.HolderConjugate.conjExponent hp1
  have hqe : Real.conjExponent p = p / (p - 1) := rfl
  have hp1' : p - 1 ≠ 0 := by linarith
  set T := fun j : Fin (k + 1) => sa16v2_T d k p j with hT
  have h1 : sa16v2_Dj d k p v S ≤ ∑ j : Fin (k + 1), p * (‖T j v‖ ^ (p - 1) * ‖T j S‖) := by
    unfold sa16v2_Dj
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply]
    exact Finset.sum_le_sum fun j _ => sa16y9_D_le p (T j v) (T j S)
  refine h1.trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ hp0.le
  have hHC : Real.HolderConjugate p (Real.conjExponent p) := hH
  have h2 := Real.inner_le_Lp_mul_Lq (Finset.univ : Finset (Fin (k + 1))) (fun j => ‖T j S‖)
    (fun j => ‖T j v‖ ^ (p - 1)) hHC
  have e1 : ∑ j : Fin (k + 1), ‖T j v‖ ^ (p - 1) * ‖T j S‖ = ∑ j : Fin (k + 1), ‖T j S‖ * ‖T j v‖ ^ (p - 1) :=
    Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [e1]
  refine h2.trans (le_of_eq ?_)
  have e2 : ∑ j : Fin (k + 1), |‖T j S‖| ^ p = jetEnergy d k p S := by
    rw [sa16v2_jetEnergy_eq_norm]
    exact Finset.sum_congr rfl fun j _ => by rw [abs_of_nonneg (norm_nonneg _)]
  have e3 : ∑ j : Fin (k + 1), |‖T j v‖ ^ (p - 1)| ^ Real.conjExponent p = jetEnergy d k p v := by
    rw [sa16v2_jetEnergy_eq_norm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), ← Real.rpow_mul (norm_nonneg _), hqe]
    congr 1
    field_simp
  rw [e2, e3, mul_comm]

end Dj2

end HRS.Whole.AppendixA.Phase2SA16S
