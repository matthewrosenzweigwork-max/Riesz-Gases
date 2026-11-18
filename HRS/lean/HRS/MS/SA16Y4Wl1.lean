import Mathlib

/-!
# S.A.16 (SA16Y4) Wl1: weak lower semicontinuity of the norm along a weakly convergent sequence
-/

noncomputable section
set_option autoImplicit false
open Filter Topology

namespace HRS.Whole.AppendixA.Phase2SA16R

theorem sa16y4_norm_le_of_weak {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : ℕ → E) (G : E) {b : ℝ}
    (hb : ∀ j, ‖g j‖ ≤ b) (hw : ∀ ℓ : StrongDual ℝ E, Tendsto (fun j => ℓ (g j)) atTop (𝓝 (ℓ G))) :
    ‖G‖ ≤ b := by
  obtain ⟨ℓ, hℓ, hℓG⟩ := exists_dual_vector'' ℝ G
  have h2 : ℓ G = ‖G‖ := by simpa using hℓG
  rw [← h2]
  refine le_of_tendsto (hw ℓ) (Eventually.of_forall fun j => ?_)
  calc ℓ (g j) ≤ ‖ℓ (g j)‖ := Real.le_norm_self _
    _ ≤ ‖ℓ‖ * ‖g j‖ := ℓ.le_opNorm _
    _ ≤ 1 * b := mul_le_mul hℓ (hb j) (norm_nonneg _) zero_le_one
    _ = b := one_mul b

end HRS.Whole.AppendixA.Phase2SA16R
