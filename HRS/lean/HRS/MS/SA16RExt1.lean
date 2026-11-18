import Mathlib

/-!
# S.A.16 (SA16R) Ext1: extension of a bounded linear map from a dense linear image

`sa16r_ext_abstract`: let `J : 𝒞 →ₗ E` have dense range and `A : 𝒞 →ₗ F` satisfy `‖A φ‖ ≤ c ‖J φ‖` (`F` complete).
Then there is a unique continuous linear `T : E →L F` with `T ∘ J = A` and `‖T‖ ≤ c`.
-/

noncomputable section
set_option autoImplicit false
open Filter Topology Set

namespace HRS.Whole.AppendixA.Phase2SA16R

theorem sa16r_ext_abstract {𝒞 E F : Type*} [AddCommGroup 𝒞] [Module ℝ 𝒞] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (J : 𝒞 →ₗ[ℝ] E) (hJ : DenseRange J) (A : 𝒞 →ₗ[ℝ] F) {c : ℝ} (hc : 0 ≤ c)
    (hA : ∀ φ, ‖A φ‖ ≤ c * ‖J φ‖) :
    ∃ T : E →L[ℝ] F, ‖T‖ ≤ c ∧ (∀ φ, T (J φ) = A φ) ∧
      ∀ T' : E →L[ℝ] F, (∀ φ, T' (J φ) = A φ) → T' = T := by
  refine ⟨A.extendOfNorm J, LinearMap.opNorm_extendOfNorm_le hJ hc hA, fun φ =>
    LinearMap.extendOfNorm_eq hJ ⟨c, hA⟩ φ, fun T' hT' => ?_⟩
  exact (LinearMap.extendOfNorm_unique hJ c hA T' (LinearMap.ext hT')).symm

end HRS.Whole.AppendixA.Phase2SA16R
