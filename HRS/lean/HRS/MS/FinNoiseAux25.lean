import HRS.MS.FinNoiseAux24

/-!
# S8.6 `finite_noise`: partial isometry of the polar decomposition (S86, for Araki-Yamagami)

`s86_polar_map`: if `‖S x‖ = ‖X x‖` for all `x` (`S : K →L K`, `X : K →L F`, `K, F` Hilbert), there is a contraction
`U : K →L F` with `U (S x) = X x`.
-/

noncomputable section

open Filter Topology Set
open scoped RealInnerProductSpace

namespace HRS.MS.FinNoise

theorem s86_polar_map {K F : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] (S : K →L[ℝ] K)
    (X : K →L[ℝ] F) (h : ∀ x, ‖X x‖ = ‖S x‖) :
    ∃ U : K →L[ℝ] F, ‖U‖ ≤ 1 ∧ ∀ x, U (S x) = X x := by
  classical
  set L : Submodule ℝ K := (LinearMap.range (S : K →ₗ[ℝ] K)).topologicalClosure with hL
  haveI : CompleteSpace L := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  haveI : L.HasOrthogonalProjection := Submodule.HasOrthogonalProjection.ofCompleteSpace L
  let e : K →ₗ[ℝ] L := LinearMap.codRestrict L (S : K →ₗ[ℝ] K)
    (fun x => (LinearMap.range (S : K →ₗ[ℝ] K)).le_topologicalClosure ⟨x, rfl⟩)
  have hdense : DenseRange e := by
    intro y
    rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image, mem_preimage]
    have himg : Subtype.val '' range e = range (S : K → K) := by
      ext z
      constructor
      · rintro ⟨_, ⟨x, rfl⟩, rfl⟩; exact ⟨x, rfl⟩
      · rintro ⟨x, rfl⟩; exact ⟨e x, ⟨x, rfl⟩, rfl⟩
    have hy : (y : K) ∈ (LinearMap.range (S : K →ₗ[ℝ] K)).topologicalClosure := y.2
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hy
    have key' : (y : K) ∈ closure (range (S : K → K)) := by
      rw [LinearMap.coe_range] at hy; exact hy
    exact himg.symm ▸ key'
  have hnorm : ∀ x, ‖(X : K →ₗ[ℝ] F) x‖ = ‖e x‖ := fun x => by
    simpa [e] using h x
  let U₀ : L →ₗᵢ[ℝ] F := (X : K →ₗ[ℝ] F).extendOfIsometry hdense hnorm
  refine ⟨U₀.toContinuousLinearMap.comp (Submodule.orthogonalProjectionOnto L), ?_, fun x => ?_⟩
  · refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have h1 : ‖U₀.toContinuousLinearMap‖ ≤ 1 := LinearIsometry.norm_toContinuousLinearMap_le U₀
    have h2 : ‖(Submodule.orthogonalProjectionOnto L : K →L[ℝ] L)‖ ≤ 1 := Submodule.orthogonalProjectionOnto_norm_le L
    nlinarith [norm_nonneg U₀.toContinuousLinearMap, norm_nonneg (Submodule.orthogonalProjectionOnto L : K →L[ℝ] L)]
  · have hmem : S x ∈ L := (LinearMap.range (S : K →ₗ[ℝ] K)).le_topologicalClosure ⟨x, rfl⟩
    simp only [ContinuousLinearMap.comp_apply]
    rw [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self ⟨S x, hmem⟩]
    exact LinearMap.extendOfIsometry_eq _ hdense hnorm x

end HRS.MS.FinNoise
