import HRS.MS.R26T8AA01s

/-!
# S8.2 T8A A01 (part t): helpers for sums of exterior-region integrals
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A

variable {d : ℕ}

theorem r26t8a_a01_ind_neg_int {S : Set (Euc d)} {f : Euc d → ℝ} (h : Integrable (Set.indicator S f)) :
    Integrable (Set.indicator S (fun z => -f z)) := by
  have := h.neg
  refine this.congr (Filter.Eventually.of_forall fun z => ?_)
  by_cases hz : z ∈ S
  · simp [Set.indicator_of_mem hz]
  · simp [Set.indicator_of_notMem hz]

theorem r26t8a_a01_ind_neg_tendsto {S : ℝ → Set (Euc d)} {f : Euc d → ℝ} {l : Filter ℝ} {L : ℝ}
    (h : Tendsto (fun ε => ∫ z, Set.indicator (S ε) f z) l (𝓝 L)) :
    Tendsto (fun ε => ∫ z, Set.indicator (S ε) (fun z => -f z) z) l (𝓝 (-L)) := by
  have := h.neg
  refine this.congr (fun ε => ?_)
  rw [← integral_neg]
  congr 1; funext z
  by_cases hz : z ∈ S ε
  · simp [Set.indicator_of_mem hz]
  · simp [Set.indicator_of_notMem hz]

theorem r26t8a_a01_omega_comm (x y : Euc d) (ε : ℝ) :
    {z : Euc d | ε < ‖y - z‖ ∧ ε < ‖x - z‖} = {z : Euc d | ε < ‖x - z‖ ∧ ε < ‖y - z‖} := by
  ext z; exact and_comm

end HRS.MS.R26T8A
