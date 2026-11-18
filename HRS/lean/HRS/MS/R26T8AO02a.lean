import HRS.MS.R26T8AG00
import HRS.MS.R26T8AA10
import HRS.MS.R26T8AD01

/-!
# S8.2 T8A O02 (part a): the pole envelope is bounded on compact sets away from collisions
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82U

theorem r26t8a_o02_env_sup {d N : ℕ} (p q : ℝ) (K : Set (EucConfig d N)) (hK : IsCompact K)
    (hKD : K ⊆ (eucCollisionSet d N)ᶜ) : ∃ S : ℝ, ∀ X ∈ K, u4Env p q X ≤ S := by
  have h1 : Continuous (fun X : EucConfig d N => (1 + ‖X‖) ^ p) :=
    (continuous_const.add continuous_norm).rpow_const (fun X => Or.inl (by show (1 + ‖X‖) ≠ 0; positivity))
  have h2 : ContinuousOn (fun X : EucConfig d N => ∏ i, ∏ j ∈ Finset.univ.erase i, (1 + ‖X i - X j‖ ^ (-q))) K := by
    refine continuousOn_finset_prod _ fun i _ => continuousOn_finset_prod _ fun j hj => ?_
    have hij : i ≠ j := (Finset.ne_of_mem_erase hj).symm
    refine continuousOn_const.add ?_
    refine ContinuousOn.rpow_const ?_ fun X hX => Or.inl ?_
    · exact ((continuous_apply i).sub (continuous_apply j)).norm.continuousOn
    · have : X ∉ eucCollisionSet d N := hKD hX
      exact (norm_pos_iff.2 (sub_ne_zero.2 fun h => this ⟨i, j, hij, h⟩)).ne'
  have hc : ContinuousOn (u4Env p q : EucConfig d N → ℝ) K := h1.continuousOn.mul h2
  obtain ⟨S, hS⟩ := (hK.bddAbove_image hc)
  exact ⟨S, fun X hX => hS ⟨X, hX, rfl⟩⟩

end HRS.MS.R26T8A
