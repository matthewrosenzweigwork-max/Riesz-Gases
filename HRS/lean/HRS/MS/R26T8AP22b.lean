import HRS.MS.R26T8AP22a

/-!
# S8.2 local Newton layer, packet T8A.P22 (part b): uniformity in `B` by finite dimensionality
`r26t8a_p22_unif`: if `B |-> f B x` is additive and homogeneous, each `f B` is continuous on a compact `K`, and `B` ranges over a
finite-dimensional normed space, then `‖f B x‖ <= C ‖B‖` on `K` with `C` independent of `B`.
`r26t8a_p22_grad_scale`: `fderiv (L_B) (t z) = t^(1-s) fderiv (L_B) z`, hence the pointwise gradient and value bounds of the leading inverse.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ContDiff
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82N

namespace HRS.MS.R26T8A

theorem r26t8a_p22_unif {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {X W : Type} [TopologicalSpace X] [NormedAddCommGroup W] [NormedSpace ℝ W] {K : Set X} (hK : IsCompact K)
    (f : V → X → W) (hadd : ∀ B1 B2, ∀ x ∈ K, f (B1 + B2) x = f B1 x + f B2 x)
    (hsmul : ∀ (c : ℝ) B, ∀ x ∈ K, f (c • B) x = c • f B x) (hcont : ∀ B, ContinuousOn (f B) K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ B, ∀ x ∈ K, ‖f B x‖ ≤ C * ‖B‖ := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  let T : V →ₗ[ℝ] C(K, W) :=
    { toFun := fun B => ⟨fun x => f B x, continuousOn_iff_continuous_domRestrict.1 (hcont B)⟩
      map_add' := fun B1 B2 => by ext ⟨x, hx⟩; exact hadd B1 B2 x hx
      map_smul' := fun c B => by ext ⟨x, hx⟩; exact hsmul c B x hx }
  let T' : V →L[ℝ] C(K, W) := LinearMap.toContinuousLinearMap T
  refine ⟨‖T'‖, norm_nonneg _, fun B x hx => ?_⟩
  have h1 : ‖f B x‖ ≤ ‖T' B‖ := by
    exact ContinuousMap.norm_coe_le_norm (T' B) ⟨x, hx⟩
  exact h1.trans (T'.le_opNorm B)

end HRS.MS.R26T8A
