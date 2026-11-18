import HRS.MS.R26T8AO03b15
import HRS.MS.S113X2A1b

/-!
# S8.2 T8A O03b (part 16): the particle generator of a `C²` function is continuous off collisions
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d N : ℕ}

theorem r26t8a_o03b_drift_cont (a beta : ℝ) (i : Fin N) :
    ContinuousOn (fun X : EucConfig d N => particleDriftW (quadraticGradientDyn d (criticalS d) a beta) X i)
      (eucCollisionSet d N)ᶜ := by
  intro X hX
  have hne : ∀ j : Fin N, j ≠ i → X i - X j ≠ 0 := fun j hj h =>
    hX ⟨i, j, hj.symm, sub_eq_zero.1 h⟩
  have hκ : ∀ j : Fin N, j ≠ i → ContinuousAt (fun Y : EucConfig d N =>
      rieszKernelGrad d (criticalS d) (Y i - Y j)) X := by
    intro j hj
    have h1 : ContinuousAt (rieszKernelGrad d (criticalS d)) (X i - X j) :=
      ((HRS.MS.S113X2.s113a_rkg_contDiffOn (d := d) (criticalS d)).continuousOn.continuousAt
        (isOpen_ne.mem_nhds (hne j hj)))
    have hsub : Continuous (fun Y : EucConfig d N => Y i - Y j) := (continuous_apply i).sub (continuous_apply j)
    exact ContinuousAt.comp (f := fun Y : EucConfig d N => Y i - Y j) h1 hsub.continuousAt
  have hM : Continuous (Torus.matVec (quadraticGradientDyn d (criticalS d) a beta).M) :=
    LinearMap.continuous_of_finiteDimensional
      (Matrix.toEuclideanLin (quadraticGradientDyn d (criticalS d) a beta).M)
  have hG : Continuous (gradient (quadraticGradientDyn d (criticalS d) a beta).V) :=
    (HRS.MS.S113X2.s113a_gradient_conf_contDiff (d := d) a).continuous
  refine ContinuousAt.continuousWithinAt ?_
  unfold particleDriftW
  refine ContinuousAt.sub ?_ ((hG.comp (continuous_apply i)).continuousAt)
  have hsum : ContinuousAt (fun Y : EucConfig d N => ∑ j ∈ Finset.univ.erase i,
      Torus.matVec (quadraticGradientDyn d (criticalS d) a beta).M
        (rieszKernelGrad d (quadraticGradientDyn d (criticalS d) a beta).s (Y i - Y j))) X := by
    exact tendsto_finsetSum _ fun j hj => hM.continuousAt.comp (hκ j (Finset.ne_of_mem_erase hj))
  exact ContinuousAt.smul (continuousAt_const : ContinuousAt (fun _ : EucConfig d N => (1 / (N : ℝ))) X) hsum

theorem r26t8a_o03b_pG_contOn (a beta : ℝ) {F : EucConfig d N → ℝ}
    (hF : ContDiffOn ℝ 2 F (eucCollisionSet d N)ᶜ) :
    ContinuousOn (particleGenerator (quadraticGradientDyn d (criticalS d) a beta) F) (eucCollisionSet d N)ᶜ := by
  have hU : IsOpen (eucCollisionSet d N)ᶜ := (HRS.MS.S113X2.s113a_isClosed_collision d N).isOpen_compl
  have hD2c : ContinuousOn (fderiv ℝ (fderiv ℝ F)) (eucCollisionSet d N)ᶜ :=
    (hF.fderiv_of_isOpen hU (m := 1) (by norm_num)).continuousOn_fderiv_of_isOpen hU (by norm_num)
  have hD1c : ContinuousOn (fderiv ℝ F) (eucCollisionSet d N)ᶜ :=
    hF.continuousOn_fderiv_of_isOpen hU (by norm_num)
  set R : EucConfig d N → ℝ := fun X =>
    (quadraticGradientDyn d (criticalS d) a beta).invβ *
      (∑ i : Fin N, ∑ k, fderiv ℝ (fderiv ℝ F) X (r26t8a_o03b_iota d N i (stdOrthonormalBasis ℝ (Euc d) k))
        (r26t8a_o03b_iota d N i (stdOrthonormalBasis ℝ (Euc d) k))) +
    ∑ i : Fin N, fderiv ℝ F X (r26t8a_o03b_iota d N i
      (particleDriftW (quadraticGradientDyn d (criticalS d) a beta) X i)) with hR
  have hRc : ContinuousOn R (eucCollisionSet d N)ᶜ := by
    refine ContinuousOn.add (continuousOn_const.mul (continuousOn_finsetSum _ fun i _ =>
      continuousOn_finsetSum _ fun k _ => (hD2c.clm_apply continuousOn_const).clm_apply continuousOn_const))
      (continuousOn_finsetSum _ fun i _ => hD1c.clm_apply
        ((r26t8a_o03b_iota d N i).continuous.comp_continuousOn (r26t8a_o03b_drift_cont a beta i)))
  refine hRc.congr fun X hX => ?_
  have hFd : DifferentiableAt ℝ F X := (hF.contDiffAt (hU.mem_nhds hX)).differentiableAt (by norm_num)
  unfold particleGenerator
  rw [hR]
  simp only
  congr 1
  · congr 1
    exact Finset.sum_congr rfl fun i _ => r26t8a_o03b_slice_lap hU hF hX i
  · exact Finset.sum_congr rfl fun i _ => r26t8a_o03b_slice_grad hFd i _

end HRS.MS.R26T8A
