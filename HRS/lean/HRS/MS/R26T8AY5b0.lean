import HRS.MS.R26T8AY2
import HRS.MS.R26T8AY3c
import HRS.MS.R26T8AZ5a2

/-!
# S8.2 T8A Y5b0: `∂_{x_i}` commutes with the local Riesz potential of a negative-order conormal function supported in `|x-y| ≤ 1/2`
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_Y5b0_dx_eq (hd : 2 ≤ d) {α : ℝ} (hα : 0 < α) {chi : Euc d → ℝ} (hchi : NewtonCutoff chi)
    (b : ℕ) (M σ : ℝ) (hM : 0 ≤ M) (hσ : σ < 0) {A : ℝ} (hA : 0 ≤ A) {P : Euc d → Euc d → ℝ}
    (hP : Conormal 1 b M σ A P) (hsupp : ∀ x y : Euc d, 1 / 2 ≤ ‖x - y‖ → P x y = 0) (i : Fin d)
    {x y : Euc d} (hxy : x ≠ y) (hx1 : ‖x - y‖ < 1) :
    r26t8a_dx i (r26t8a_localRiesz α chi P) x y = r26t8a_localRiesz α chi (r26t8a_dx i P) x y := by
  obtain ⟨c0, c1, hc0, hc1⟩ := r26t8a_Y3c_slice hchi b M σ hM hσ hA hP hsupp y
  have hP1 : ContDiffOn ℝ 1 (Function.uncurry P) {p : Euc d × Euc d | p.1 ≠ p.2} := by simpa using hP.1
  obtain ⟨h1, h2⟩ := r26t8a_Y2_deriv hd hα hchi hP1 y
    (fun v hv => hsupp (y + v) y (by simp only [add_sub_cancel_left]; exact hv.le)) hc0 hc1 hxy hx1
  unfold r26t8a_dx
  rw [h1.fderiv]
  exact h2 i

end HRS.MS.R26T8A
