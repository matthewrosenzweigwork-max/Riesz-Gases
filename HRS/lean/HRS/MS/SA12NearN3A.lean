import HRS.MS.SA12NearDefs
import HRS.Whole.MovtrAux3
import HRS.Whole.MovtrAux2
import HRS.MS.UniqN0b
import HRS.MS.SA12CompB4A

/-!
# S.A.12 N3, part A: the smoothed Riesz kernel

`movtr_gEps` is smooth for `ε > 0`, has the derivative `movtr_dEps`, is dominated by a locally integrable
majorant for `0 ≤ ε ≤ 1`, and converges to the Riesz kernel as `ε → 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.Whole.AppendixA

variable {d : ℕ}

theorem n3_gEps_contDiff (s : ℝ) {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ ∞ (movtr_gEps d s ε) := by
  have hbase : ContDiff ℝ ∞ (fun z : Euc d => ‖z‖ ^ 2 + ε ^ 2) :=
    (contDiff_norm_sq ℝ).add contDiff_const
  have hpos : ∀ z : Euc d, ‖z‖ ^ 2 + ε ^ 2 ≠ 0 := fun z => by positivity
  unfold movtr_gEps
  by_cases hs : s = 0
  · simp only [hs, ite_true]
    exact contDiff_const.mul (hbase.log hpos)
  · simp only [hs, ite_false]
    exact hbase.rpow_const_of_ne hpos

theorem n3_gEps_fderiv (s : ℝ) {ε : ℝ} (hε : 0 < ε) (e z : Euc d) :
    fderiv ℝ (movtr_gEps d s ε) z e = movtr_dEps d s ε e z := by
  have hu : 0 < ‖z‖ ^ 2 + ε ^ 2 := by positivity
  rw [(movtr_gEps_hasFDerivAt (d := d) s ε z hu).fderiv]
  simp [movtr_dEps]

/-- The integrable majorant of the smoothed kernels. -/
theorem n3_majorant_locInt (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    LocallyIntegrable (fun z : Euc d => 2 * ‖z‖ ^ (-movtr_sp s) + ‖z‖ + 1) volume := by
  have hsp := movtr_sp_pos (s := s) hs0
  have hlt := movtr_sp_lt (d := d) hsd hd
  have h1 : LocallyIntegrable (fun z : Euc d => ‖z‖ ^ (-movtr_sp s)) volume := by
    have := rieszKernel_locallyIntegrable (d := d) (s := movtr_sp s) hsp.le hlt
    refine this.congr ?_
    refine Filter.Eventually.of_forall fun z => ?_
    unfold rieszKernel
    simp [hsp.ne']
  have h2 : LocallyIntegrable (fun z : Euc d => 2 * ‖z‖ ^ (-movtr_sp s)) volume := by
    refine (h1.add h1).congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [Pi.add_apply]; ring
  exact (h2.add (continuous_norm.locallyIntegrable)).add (continuous_const.locallyIntegrable)

end HRS.MH.AdjointRd.Phase2SA12Near
