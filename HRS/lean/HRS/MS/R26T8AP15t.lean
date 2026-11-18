import HRS.MS.R26T8AP15s

/-!
# S8.2 T8A P15t: differences of conormal pair functions
`r26t8a_conormal_sub`: `f` conormal `A`, `g` conormal `A'` (same `k b M σ`) gives `f - g` conormal `A + 2^k (k+1)^2 A'`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_conormal_sub {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {k b : ℕ} {M σ A A' : ℝ} (hA : 0 ≤ A)
    (hA' : 0 ≤ A') {f g : Euc d → Euc d → ℝ} (hf : Conormal k b M σ A f) (hg : Conormal k b M σ A' g) :
    Conormal k b M σ (A + 2 ^ k * (((k : ℝ) + 1) ^ 2 * A')) (fun x y => f x y - g x y) := by
  have h1 := r26t8a_conormal_const_mul hchi hA' (-1 : ℝ) hg
  have h2 := r26t8a_conormal_add hchi hf h1
  refine r26t8a_conormal_mono_sA (by positivity) (le_of_eq ?_) le_rfl (r26t8a_conormal_congr (fun x y _ => ?_) h2)
  · simp
  · ring

end HRS.MS.R26T8A
