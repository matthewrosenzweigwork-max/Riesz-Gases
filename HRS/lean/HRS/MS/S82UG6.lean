import HRS.MS.S82UG5

/-!
# S8.2 A04 (S82U), part 6: slices of a function that is `C²` off collisions
`Phase2S82.configGrad F X i = ∇ (F ∘ L_i)`, `Δ_i F = ∑_k D²F(L_i b_k, L_i b_k)`, and the corresponding norm bounds.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.S82U
open HRS HRS.Whole HRS.MS.Phase2S82

section slices
variable {d N : ℕ}

lemma u4_coll_closed : IsClosed (eucCollisionSet d N) := by
  have : eucCollisionSet d N = ⋃ i : Fin N, ⋃ j : Fin N, ⋃ (_ : i ≠ j), {X : EucConfig d N | X i = X j} := by
    ext X; simp [eucCollisionSet]
  rw [this]
  exact isClosed_iUnion_of_finite fun i => isClosed_iUnion_of_finite fun j =>
    isClosed_iUnion_of_finite fun _ => isClosed_eq (continuous_apply i) (continuous_apply j)

lemma u4_D_open : IsOpen (eucCollisionSet d N)ᶜ := u4_coll_closed.isOpen_compl

/-- the embedding `y ↦ update 0 i y` as a continuous linear map -/
def u4L (d N : ℕ) (i : Fin N) : Euc d →L[ℝ] EucConfig d N :=
  ContinuousLinearMap.pi (Pi.single i (ContinuousLinearMap.id ℝ (Euc d)))

lemma u4L_norm_le (i : Fin N) (v : Euc d) : ‖u4L d N i v‖ ≤ ‖v‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg v)).2 fun j => ?_
  by_cases h : j = i
  · subst h; simp [u4L]
  · simp [u4L, h]

lemma u4_slice_hasFDerivAt {F : EucConfig d N → ℝ} (X : EucConfig d N) (i : Fin N) (y : Euc d)
    (hF : DifferentiableAt ℝ F (Function.update X i y)) :
    HasFDerivAt (fun y => F (Function.update X i y)) ((fderiv ℝ F (Function.update X i y)).comp (u4L d N i)) y :=
  hF.hasFDerivAt.comp y (hasFDerivAt_update (𝕜 := ℝ) X y)

lemma u4_configGrad_eq {F : EucConfig d N → ℝ} (hF : ContDiffOn ℝ 2 F (eucCollisionSet d N)ᶜ)
    {X : EucConfig d N} (hX : X ∉ eucCollisionSet d N) (i : Fin N) :
    Phase2S82.configGrad F X i = (InnerProductSpace.toDual ℝ (Euc d)).symm ((fderiv ℝ F X).comp (u4L d N i)) := by
  have hFd : DifferentiableAt ℝ F X :=
    (hF.differentiableOn (by norm_num)).differentiableAt (u4_D_open.mem_nhds hX)
  unfold Phase2S82.configGrad gradient
  have := (u4_slice_hasFDerivAt (F := F) X i (X i) (by rwa [Function.update_eq_self])).fderiv
  rw [this, Function.update_eq_self]

lemma u4_configGrad_norm_le {F : EucConfig d N → ℝ} (hF : ContDiffOn ℝ 2 F (eucCollisionSet d N)ᶜ)
    {X : EucConfig d N} (hX : X ∉ eucCollisionSet d N) (i : Fin N) :
    ‖Phase2S82.configGrad F X i‖ ≤ ‖fderiv ℝ F X‖ := by
  rw [u4_configGrad_eq hF hX i, LinearIsometryEquiv.norm_map]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
  simp only [ContinuousLinearMap.comp_apply]
  calc ‖fderiv ℝ F X (u4L d N i v)‖ ≤ ‖fderiv ℝ F X‖ * ‖u4L d N i v‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖fderiv ℝ F X‖ * ‖v‖ := mul_le_mul_of_nonneg_left (u4L_norm_le i v) (norm_nonneg _)

lemma u4_laplacian_eq {F : EucConfig d N → ℝ} (hF : ContDiffOn ℝ 2 F (eucCollisionSet d N)ᶜ)
    {X : EucConfig d N} (hX : X ∉ eucCollisionSet d N) (i : Fin N) :
    Laplacian.laplacian (fun y => F (Function.update X i y)) (X i) =
      ∑ k, fderiv ℝ (fderiv ℝ F) X (u4L d N i ((stdOrthonormalBasis ℝ (Euc d)) k))
        (u4L d N i ((stdOrthonormalBasis ℝ (Euc d)) k)) := by
  have hcd : ContDiffAt ℝ 2 F X := hF.contDiffAt (u4_D_open.mem_nhds hX)
  have hFd2 : DifferentiableAt ℝ (fderiv ℝ F) X :=
    (hcd.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hnhds' : ∀ᶠ y in 𝓝 (X i), Function.update X i y ∈ (eucCollisionSet d N)ᶜ := by
    have hc : ContinuousAt (Function.update X i) (X i) := (hasFDerivAt_update (𝕜 := ℝ) X (X i)).continuousAt
    have h1 : (eucCollisionSet d N)ᶜ ∈ 𝓝 (Function.update X i (X i)) := by
      rw [Function.update_eq_self]; exact u4_D_open.mem_nhds hX
    exact hc.preimage_mem_nhds h1
  have heq : fderiv ℝ (fun y => F (Function.update X i y)) =ᶠ[𝓝 (X i)]
      fun y => (fderiv ℝ F (Function.update X i y)).comp (u4L d N i) := by
    filter_upwards [hnhds'] with y hy
    exact (u4_slice_hasFDerivAt (F := F) X i y
      ((hF.differentiableOn (by norm_num)).differentiableAt (u4_D_open.mem_nhds hy))).fderiv
  have h1 : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) X) (Function.update X i (X i)) := by
    rw [Function.update_eq_self]; exact hFd2.hasFDerivAt
  have hι : HasFDerivAt (fun y => fderiv ℝ F (Function.update X i y))
      ((fderiv ℝ (fderiv ℝ F) X).comp (u4L d N i)) (X i) := by
    exact h1.comp (X i) (hasFDerivAt_update (𝕜 := ℝ) X (X i))
  have hΦ := ((ContinuousLinearMap.compL ℝ (Euc d) (EucConfig d N) ℝ).flip (u4L d N i)).hasFDerivAt.comp (X i) hι
  have hfd : fderiv ℝ (fderiv ℝ (fun y => F (Function.update X i y))) (X i) =
      (((ContinuousLinearMap.compL ℝ (Euc d) (EucConfig d N) ℝ).flip (u4L d N i)).comp
        ((fderiv ℝ (fderiv ℝ F) X).comp (u4L d N i))) := by
    rw [heq.fderiv_eq]
    exact hΦ.fderiv
  rw [show Laplacian.laplacian (fun y => F (Function.update X i y)) (X i) =
    ∑ k, iteratedFDeriv ℝ 2 (fun y => F (Function.update X i y)) (X i)
      ![(stdOrthonormalBasis ℝ (Euc d)) k, (stdOrthonormalBasis ℝ (Euc d)) k] from
    congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis (f := fun y => F (Function.update X i y))) (X i)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [iteratedFDeriv_two_apply, hfd]
  simp

lemma u4_laplacian_bound {F : EucConfig d N → ℝ} (hF : ContDiffOn ℝ 2 F (eucCollisionSet d N)ᶜ)
    {X : EucConfig d N} (hX : X ∉ eucCollisionSet d N) (i : Fin N) :
    |Laplacian.laplacian (fun y => F (Function.update X i y)) (X i)| ≤ d * ‖iteratedFDeriv ℝ 2 F X‖ := by
  rw [u4_laplacian_eq hF hX i]
  have hn : ‖fderiv ℝ (fderiv ℝ F) X‖ = ‖iteratedFDeriv ℝ 2 F X‖ := by
    have e := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := F) (x := X) (n := 1)
    rw [norm_iteratedFDeriv_one] at e
    exact e
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hb : ∀ k, |fderiv ℝ (fderiv ℝ F) X (u4L d N i ((stdOrthonormalBasis ℝ (Euc d)) k))
      (u4L d N i ((stdOrthonormalBasis ℝ (Euc d)) k))| ≤ ‖iteratedFDeriv ℝ 2 F X‖ := by
    intro k
    set v := u4L d N i ((stdOrthonormalBasis ℝ (Euc d)) k) with hv
    have hvn : ‖v‖ ≤ 1 := by
      refine (u4L_norm_le i _).trans ?_
      simp
    calc |fderiv ℝ (fderiv ℝ F) X v v| ≤ ‖fderiv ℝ (fderiv ℝ F) X v‖ * ‖v‖ := by
          rw [← Real.norm_eq_abs]; exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ (‖fderiv ℝ (fderiv ℝ F) X‖ * ‖v‖) * ‖v‖ := by
          gcongr; exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖iteratedFDeriv ℝ 2 F X‖ := by
          rw [← hn]
          have := norm_nonneg (fderiv ℝ (fderiv ℝ F) X)
          have := norm_nonneg v
          nlinarith [mul_nonneg ‹0 ≤ ‖fderiv ℝ (fderiv ℝ F) X‖› ‹0 ≤ ‖v‖›]
  calc ∑ k, |fderiv ℝ (fderiv ℝ F) X (u4L d N i ((stdOrthonormalBasis ℝ (Euc d)) k))
        (u4L d N i ((stdOrthonormalBasis ℝ (Euc d)) k))|
      ≤ ∑ k : Fin (Module.finrank ℝ (Euc d)), ‖iteratedFDeriv ℝ 2 F X‖ := by
        exact Finset.sum_le_sum fun k _ => hb k
    _ = d * ‖iteratedFDeriv ℝ 2 F X‖ := by simp [finrank_euclideanSpace]

end slices

end HRS.MS.S82U
