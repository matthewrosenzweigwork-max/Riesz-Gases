import HRS.MS.R26T8AP11f16
import HRS.MS.R26T8AP10a15
import HRS.MS.R26T8AP11jet

/-!
# S8.2 T8A P11f (part 17): centre jets of the fibre `y ↦ F(y+v,y)` of a conormal pair, with weights
`r26t8a_f17_center_jet`: `‖D^m (y' ↦ F(y'+v) y') y‖ ≤ A w(y+v,y) (1 + |v|^(-σ)(1+|log|v||)^b)` for `0 < |v| ≤ 1`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_f17_center_jet {K b : ℕ} {M σ A : ℝ} {F : Euc d → Euc d → ℝ} (hF : Conormal K b M σ A F)
    {m : ℕ} (hm : m ≤ K) {v : Euc d} (hv : v ≠ 0) (hv1 : ‖v‖ ≤ 1) (y : Euc d) :
    ‖iteratedFDeriv ℝ m (fun y' : Euc d => F (y' + v) y') y‖ ≤
      A * HRS.MS.Phase2S82.pairWeight M (y + v) y *
        (1 + ‖v‖ ^ (-(σ + ((0 : ℕ) : ℝ))) * (1 + |Real.log ‖v‖|) ^ b) := by
  have h0 := hF.2 m 0 (by omega) (y + (1 / 2 : ℝ) • v) v hv
  have hX : y + (1 / 2 : ℝ) • v + (1 / 2 : ℝ) • v = y + v := by module
  have hX' : y + (1 / 2 : ℝ) • v - (1 / 2 : ℝ) • v = y := by module
  rw [hX, hX', min_eq_right hv1] at h0
  have hfun : (fun y' : Euc d => F (y' + v) y') =
      fun y' => (fun Y : Euc d => midPair F Y v) (y' + (1 / 2 : ℝ) • v) := by
    funext y'
    have e1 : y' + (1 / 2 : ℝ) • v + (1 / 2 : ℝ) • v = y' + v := by module
    have e2 : y' + (1 / 2 : ℝ) • v - (1 / 2 : ℝ) • v = y' := by module
    show F (y' + v) y' = F (y' + (1 / 2 : ℝ) • v + (1 / 2 : ℝ) • v) (y' + (1 / 2 : ℝ) • v - (1 / 2 : ℝ) • v)
    rw [e1, e2]
  have hnorm : ‖iteratedFDeriv ℝ m (fun y' : Euc d => F (y' + v) y') y‖ =
      ‖mixedJet m 0 F (y + (1 / 2 : ℝ) • v) v‖ := by
    have h1 : iteratedFDeriv ℝ m (fun y' : Euc d => F (y' + v) y') y =
        iteratedFDeriv ℝ m (fun Y : Euc d => midPair F Y v) (y + (1 / 2 : ℝ) • v) := by
      rw [hfun]
      exact iteratedFDeriv_comp_add_right (f := fun Y : Euc d => midPair F Y v) m ((1 / 2 : ℝ) • v) y
    rw [h1]
    exact (r26t8a_nest_zero (E := Euc d) m (fun Yw : Euc d × Euc d => midPair F Yw.1 Yw.2)
      (y + (1 / 2 : ℝ) • v) v).symm
  rw [hnorm]
  exact h0

end HRS.MS.R26T8A
