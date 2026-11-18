import HRS.MS.R26T8AO03b14

/-!
# S8.2 T8A O03b (part 15): coordinate slices of a `C²` function of a configuration
For `F` that is `C²` on an open set `U` and `X ∈ U`: the Laplacian of the `i`-th slice at `X i` is the trace of the
second derivative of `F` along the `i`-th coordinate embedding, and the inner product of the slice gradient with `v`
is `fderiv F X (ι v)`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d N : ℕ}

/-- the `i`-th coordinate embedding -/
def r26t8a_o03b_iota (d N : ℕ) (i : Fin N) : Euc d →L[ℝ] EucConfig d N :=
  ContinuousLinearMap.pi (Pi.single i (ContinuousLinearMap.id ℝ (Euc d)))

theorem r26t8a_o03b_slice_lap {F : EucConfig d N → ℝ} {U : Set (EucConfig d N)} (hU : IsOpen U)
    (hF : ContDiffOn ℝ 2 F U) {X : EucConfig d N} (hX : X ∈ U) (i : Fin N) :
    Laplacian.laplacian (fun y : Euc d => F (Function.update X i y)) (X i) =
      ∑ k, fderiv ℝ (fderiv ℝ F) X (r26t8a_o03b_iota d N i (stdOrthonormalBasis ℝ (Euc d) k))
        (r26t8a_o03b_iota d N i (stdOrthonormalBasis ℝ (Euc d) k)) := by
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
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [iteratedFDeriv_two_apply, hD2]
  simp [L1]

theorem r26t8a_o03b_slice_grad {F : EucConfig d N → ℝ} {X : EucConfig d N} (hF : DifferentiableAt ℝ F X)
    (i : Fin N) (v : Euc d) :
    inner ℝ v (Phase2S82.configGrad F X i) = fderiv ℝ F X (r26t8a_o03b_iota d N i v) := by
  have hu : HasFDerivAt (fun y : Euc d => Function.update X i y) (r26t8a_o03b_iota d N i) (X i) :=
    hasFDerivAt_update X (X i)
  have hFd : HasFDerivAt F (fderiv ℝ F X) (Function.update X i (X i)) := by
    rw [Function.update_eq_self]; exact hF.hasFDerivAt
  have hc : fderiv ℝ (fun y : Euc d => F (Function.update X i y)) (X i) =
      (fderiv ℝ F X).comp (r26t8a_o03b_iota d N i) := (hFd.comp (X i) hu).fderiv
  unfold Phase2S82.configGrad gradient
  rw [real_inner_comm, InnerProductSpace.toDual_symm_apply, hc]
  rfl

end HRS.MS.R26T8A
