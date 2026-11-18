import HRS.MS.SA16ZT8
import HRS.Commutator.Whole.XLIAux23
import HRS.MS.CzPvAux3
import HRS.MS.CzElemAux1

/-!
# S.A.16 (SA16Z) L1: Jensen's inequality for finite measures (lintegral form)

`sa16z_jensen`: `(∫⁻ h dν)^p ≤ ν(univ)^{p-1} ∫⁻ h^p dν` for a finite measure and `p > 1`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R

section L1

lemma sa16z_jensen {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsFiniteMeasure ν] {p : ℝ} (hp : 1 < p)
    {h : Ω → ℝ≥0∞} (hh : AEMeasurable h ν) :
    (∫⁻ a, h a ∂ν) ^ p ≤ (ν univ) ^ (p - 1) * ∫⁻ a, h a ^ p ∂ν := by
  have hpq := Real.HolderConjugate.conjExponent hp
  set q := Real.conjExponent p with hq
  have h1 := ENNReal.lintegral_mul_le_Lp_mul_Lq ν hpq hh (g := fun _ => (1 : ℝ≥0∞)) aemeasurable_const
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, one_mul] at h1
  have hp0 : 0 < p := by linarith
  have h2 := ENNReal.rpow_le_rpow h1 hp0.le
  rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul] at h2
  have e1 : 1 / p * p = 1 := by field_simp
  have e2 : 1 / q * p = p - 1 := by
    have : 1 / p + 1 / q = 1 := by simpa [one_div] using hpq.inv_add_inv_eq_one
    have h3 : 1 / q = 1 - 1 / p := by linarith
    rw [h3]; field_simp
  rw [e1, e2, ENNReal.rpow_one] at h2
  rw [mul_comm]; exact h2

end L1

end HRS.Whole.AppendixA.Phase2SA16R
