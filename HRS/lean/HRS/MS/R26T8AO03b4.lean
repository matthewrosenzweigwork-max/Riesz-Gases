import HRS.MS.R26T8AO03b3

/-!
# S8.2 T8A O03b (part 4): the collision set is closed; compact neighbourhoods of collision-free configurations
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d N : ℕ}

theorem r26t8a_o03b_coll_closed : IsClosed (eucCollisionSet d N) := by
  have : eucCollisionSet d N = ⋃ i : Fin N, ⋃ j : Fin N, ⋃ (_ : i ≠ j), {X : EucConfig d N | X i = X j} := by
    ext X; simp [eucCollisionSet]
  rw [this]
  exact isClosed_iUnion_of_finite fun i => isClosed_iUnion_of_finite fun j =>
    isClosed_iUnion_of_finite fun _ => isClosed_eq (continuous_apply i) (continuous_apply j)

theorem r26t8a_o03b_nbhd {X0 : EucConfig d N} (hX0 : X0 ∉ eucCollisionSet d N) :
    ∃ r : ℝ, 0 < r ∧ closedBall X0 r ⊆ (eucCollisionSet d N)ᶜ ∧ IsCompact (closedBall X0 r) := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (r26t8a_o03b_coll_closed (d := d) (N := N)).isOpen_compl X0 hX0
  refine ⟨ε / 2, by positivity, ?_, isCompact_closedBall _ _⟩
  exact (closedBall_subset_ball (by linarith)).trans hball

end HRS.MS.R26T8A
