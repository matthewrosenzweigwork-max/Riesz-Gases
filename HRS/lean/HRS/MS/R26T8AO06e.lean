import HRS.MS.R26T8AO06d

/-!
# S8.2 T8A O06 (part e): the Itô drift of a `C²` function on the collision-free set is `∂_t + particleGenerator`
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MH.DualityRd

variable {d N : ℕ}

theorem r26t8a_o06_slice_lap_basis {F : EucConfig d N → ℝ} {U : Set (EucConfig d N)} (hU : IsOpen U)
    (hF : ContDiffOn ℝ 2 F U) {X : EucConfig d N} (hX : X ∈ U) (i : Fin N) :
    Laplacian.laplacian (fun y : Euc d => F (Function.update X i y)) (X i) =
      ∑ k : Fin d, fderiv ℝ (fderiv ℝ F) X (r26t8a_o03b_iota d N i ((EuclideanSpace.single k (1 : ℝ))))
        (r26t8a_o03b_iota d N i ((EuclideanSpace.single k (1 : ℝ)))) := by
  set ι := r26t8a_o03b_iota d N i with hι
  have hu : ∀ y : Euc d, HasFDerivAt (fun y : Euc d => Function.update X i y) ι y :=
    fun y => hasFDerivAt_update X y
  have hFc : ContDiffAt ℝ 2 F X := hF.contDiffAt (hU.mem_nhds hX)
  have hV : IsOpen {y : Euc d | Function.update X i y ∈ U} :=
    hU.preimage (continuous_const.update i continuous_id)
  have hXiV : X i ∈ {y : Euc d | Function.update X i y ∈ U} := by
    simpa [Function.update_eq_self] using hX
  have hD1 : ∀ᶠ y in 𝓝 (X i), fderiv ℝ (fun y : Euc d => F (Function.update X i y)) y =
      (fderiv ℝ F (Function.update X i y)).comp ι := by
    filter_upwards [hV.mem_nhds hXiV] with y hy
    have hFd : DifferentiableAt ℝ F (Function.update X i y) :=
      (hF.contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num)
    exact ((hFd.hasFDerivAt).comp y (hu y)).fderiv
  have hFd2 : DifferentiableAt ℝ (fderiv ℝ F) X :=
    (hFc.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  let L1 : (EucConfig d N →L[ℝ] ℝ) →L[ℝ] (Euc d →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ (Euc d) (EucConfig d N) ℝ).flip ι
  have h1 : HasFDerivAt (fun y : Euc d => fderiv ℝ F (Function.update X i y))
      ((fderiv ℝ (fderiv ℝ F) X).comp ι) (X i) :=
    (show HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) X) (Function.update X i (X i)) by
      rw [Function.update_eq_self]; exact hFd2.hasFDerivAt).comp (X i) (hu (X i))
  have hH : HasFDerivAt (fun y : Euc d => L1 (fderiv ℝ F (Function.update X i y)))
      (L1.comp ((fderiv ℝ (fderiv ℝ F) X).comp ι)) (X i) := L1.hasFDerivAt.comp (X i) h1
  have hD2 : fderiv ℝ (fderiv ℝ (fun y : Euc d => F (Function.update X i y))) (X i) =
      L1.comp ((fderiv ℝ (fderiv ℝ F) X).comp ι) := by
    have : HasFDerivAt (fderiv ℝ (fun y : Euc d => F (Function.update X i y)))
        (L1.comp ((fderiv ℝ (fderiv ℝ F) X).comp ι)) (X i) :=
      hH.congr_of_eventuallyEq (hD1.mono fun y hy => by rw [hy]; rfl)
    exact this.fderiv
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ (EuclideanSpace.basisFun (Fin d) ℝ)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [iteratedFDeriv_two_apply, hD2]
  simp [L1, EuclideanSpace.basisFun_apply]


theorem r26t8a_o06_drift_conv (D : WholeDyn d) (hnu : 0 ≤ D.invβ) {F : EucConfig d N → ℝ}
    (hF : ContDiffOn ℝ 2 F (eucCollisionSet d N)ᶜ) {X : EucConfig d N} (hX : X ∉ eucCollisionSet d N) :
    fderiv ℝ F X (particleDriftW D X) + (1 / 2) * ∑ k : Fin N × Fin d,
      fderiv ℝ (fderiv ℝ F) X (noiseDir D k) (noiseDir D k) = particleGenerator D F X := by
  have hU : IsOpen (eucCollisionSet d N)ᶜ := r26t8a_o03b_coll_closed.isOpen_compl
  have hFd : DifferentiableAt ℝ F X := (hF.contDiffAt (hU.mem_nhds hX)).differentiableAt (by norm_num)
  have hι : ∀ (i : Fin N) (v : Euc d), r26t8a_o03b_iota d N i v = Pi.single i v := by
    intro i v; funext k
    by_cases hk : k = i
    · subst hk; simp [r26t8a_o03b_iota]
    · simp [r26t8a_o03b_iota, Pi.single_apply, hk]
  have hdrift : fderiv ℝ F X (particleDriftW D X) =
      ∑ i, inner ℝ (particleDriftW D X i) (Phase2S82.configGrad F X i) := by
    have : particleDriftW D X = ∑ i, Pi.single i (particleDriftW D X i) :=
      (Finset.univ_sum_single (particleDriftW D X)).symm
    conv_lhs => rw [this]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hι, r26t8a_o03b_slice_grad hFd i, ]
  have hsq : Real.sqrt (2 * D.invβ) * Real.sqrt (2 * D.invβ) = 2 * D.invβ :=
    Real.mul_self_sqrt (by linarith)
  have hk : ∀ k : Fin N × Fin d, fderiv ℝ (fderiv ℝ F) X (noiseDir D k) (noiseDir D k) =
      (2 * D.invβ) * fderiv ℝ (fderiv ℝ F) X (r26t8a_o03b_iota d N k.1 (EuclideanSpace.single k.2 (1 : ℝ)))
        (r26t8a_o03b_iota d N k.1 (EuclideanSpace.single k.2 (1 : ℝ))) := by
    intro k
    unfold noiseDir
    rw [← hι]
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    linear_combination (fderiv ℝ (fderiv ℝ F) X (r26t8a_o03b_iota d N k.1 (EuclideanSpace.single k.2 (1 : ℝ)))
      (r26t8a_o03b_iota d N k.1 (EuclideanSpace.single k.2 (1 : ℝ)))) * hsq
  have hhess : (1 / 2) * ∑ k : Fin N × Fin d, fderiv ℝ (fderiv ℝ F) X (noiseDir D k) (noiseDir D k) =
      D.invβ * ∑ i, Laplacian.laplacian (fun y => F (Function.update X i y)) (X i) := by
    simp only [hk]
    rw [← Finset.mul_sum, Fintype.sum_prod_type]
    simp only [r26t8a_o06_slice_lap_basis hU hF hX]
    ring
  rw [hdrift, hhess]
  unfold particleGenerator
  ring

end HRS.MS.R26T8A

end
