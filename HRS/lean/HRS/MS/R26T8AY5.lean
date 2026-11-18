import HRS.MS.R26T8AY5c

/-!
# S8.2 T8A Y5: same-`k` local Riesz gain (P11e for every `σ < d`, no `0 ≤ σ`)
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

theorem r26t8a_local_riesz_gain_same (d : ℕ) (hd : 2 ≤ d) (k b : ℕ) (alpha M sigma : ℝ)
    (halpha : 0 < alpha) (had : alpha < d) (hM : 0 ≤ M) (hsd : sigma < d)
    (chi : Euc d → ℝ) (hchi : NewtonCutoff chi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ F : Euc d → Euc d → ℝ, ∀ A : ℝ, 0 ≤ A → Conormal k b M sigma A F →
      (∀ x y, x ≠ y → Integrable (fun v => ‖x - y - v‖ ^ (alpha - (d : ℝ)) * chi v * F (y + v) y)) ∧
      Conormal k (b + 1) M (sigma - alpha) (C * A) (r26t8a_localRiesz alpha chi F) := by
  refine r26t8a_Y5c_same_k hd halpha had hchi ⌈-sigma⌉₊ k b M sigma hM ?_ hsd
  have := Nat.le_ceil (-sigma)
  linarith

end HRS.MS.R26T8A
