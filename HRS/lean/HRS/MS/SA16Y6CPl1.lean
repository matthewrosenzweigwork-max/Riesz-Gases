import HRS.MS.SA16Y6CRm1
import HRS.MS.SA16Y6C1
import HRS.MS.SA16Y5Pl1

/-! # SA16Y6 critical-case copy of SA16Y5Pl1 (s = d-1) -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16Q

section Pl1
variable {d : ℕ} {s : ℝ}
theorem sa16y6c_Rw_bound (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hs1 : s = (d : ℝ) - 1) {p : ℝ} (hp : 2 ≤ p)
    (hfar : (d : ℝ) < p * (s + 1)) {W : ℝ} (hW : 0 ≤ W) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {μ w : Euc d → ℝ}, ContDiff ℝ ∞ μ → sa16y5_Dec 2 W μ → IsCcInfty w →
      eLpNorm (fun x => ∑ i : Fin d, fderiv ℝ (convFun (rieszKernel d s) (fun z => sa16z_dm μ i z * w z)) x (sa16z_e i))
        (ENNReal.ofReal p) volume ≤ ENNReal.ofReal (K * (d : ℝ)) * eLpNorm w (ENNReal.ofReal p) volume := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal (by linarith : (1 : ℝ) ≤ p)
  obtain ⟨K, hK0, hK⟩ := sa16y6c_D0 hd hs0 hs1 hp hfar hW
  refine ⟨K, hK0, fun {μ w} hμ hdec hw => ?_⟩
  have hfun : (fun x => ∑ i : Fin d, fderiv ℝ (convFun (rieszKernel d s) (fun z => sa16z_dm μ i z * w z)) x
      (sa16z_e i)) = ∑ i : Fin d, (fun x => fderiv ℝ (convFun (rieszKernel d s)
        (fun z => sa16z_dm μ i z * w z)) x (sa16z_e i)) := by
    funext x; simp [Finset.sum_apply]
  have hi : ∀ i : Fin d, eLpNorm (fun x => fderiv ℝ (convFun (rieszKernel d s) (fun z => sa16z_dm μ i z * w z)) x
      (sa16z_e i)) (ENNReal.ofReal p) volume ≤ ENNReal.ofReal K * eLpNorm w (ENNReal.ofReal p) volume :=
    fun i => hK (sa16z_dm_smooth hμ i) (sa16y5_Dec_dm hμ hdec i) hw i
  rw [hfun]
  refine (eLpNorm_sum_le hp1).trans ((Finset.sum_le_sum fun i _ => hi i).trans (le_of_eq ?_))
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ENNReal.ofReal_mul hK0,
    ENNReal.ofReal_natCast]
  ring

end Pl1

end HRS.Whole.AppendixA.Phase2SA16R
