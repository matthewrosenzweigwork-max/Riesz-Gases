import HRS.MS.S111K4J01A

/-!
# S11.1 / J01 piece: the zero-mass projection of the coefficient space (S11K4)

The drift interval map needs `z^v(1) = 0` pointwise.  Instead of extending by `f ↦ f - f(0)` (which needs a weighted Sobolev point
evaluation), the operator is composed with the orthogonal projection `PM E` of `ℓ²` onto `(E 1)^⊥` (norm `≤ 1`, identity on
zero-mass coefficients).  `⟪PM E q, E 1⟫ = 0` holds for every `q`, pointwise in time.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111K4J01

open HRS HRS.Whole

/-- The unit vector direction `E 1`. -/
def massVec {d r : ℕ} {Pw : ℝ} (E : WeightedChart d r Pw) : Coeff := E.encode (fun _ => 1)

/-- Orthogonal projection onto `(E 1)^⊥`, as a continuous linear map of `ℓ²`. -/
def PM {d r : ℕ} {Pw : ℝ} (E : WeightedChart d r Pw) : Coeff →L[ℝ] Coeff :=
  ((ℝ ∙ massVec E)ᗮ).subtypeL.comp (Submodule.orthogonalProjection (ℝ ∙ massVec E)ᗮ)

theorem PM_norm_le {d r : ℕ} {Pw : ℝ} (E : WeightedChart d r Pw) (q : Coeff) : ‖PM E q‖ ≤ ‖q‖ := by
  unfold PM
  exact Submodule.norm_orthogonalProjection_apply_le _ q

theorem PM_inner_mass {d r : ℕ} {Pw : ℝ} (E : WeightedChart d r Pw) (q : Coeff) :
    inner ℝ (PM E q) (massVec E) = 0 := by
  have h : (PM E q) ∈ (ℝ ∙ massVec E)ᗮ := (Submodule.orthogonalProjection (ℝ ∙ massVec E)ᗮ q).2
  rw [Submodule.mem_orthogonal_singleton_iff_inner_left] at h
  exact h

theorem PM_of_inner_zero {d r : ℕ} {Pw : ℝ} (E : WeightedChart d r Pw) {q : Coeff}
    (hq : inner ℝ q (massVec E) = 0) : PM E q = q := by
  have h : q ∈ (ℝ ∙ massVec E)ᗮ := by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left]; exact hq
  unfold PM
  simp [Submodule.orthogonalProjection_mem_subspace_eq_self ⟨q, h⟩]

end HRS.MS.S111K4J01
