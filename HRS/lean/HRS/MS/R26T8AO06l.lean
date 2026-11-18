import HRS.MS.R26T8AO06k

/-!
# S8.2 T8A O06 (part l): the particle drift is Borel measurable
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

theorem r26t8a_o06_drift_meas (d N : ℕ) (a beta : ℝ) :
    Measurable (fun Y : EucConfig d N => particleDriftW (quadraticGradientDyn d (criticalS d) a beta) Y) := by
  refine measurable_pi_iff.2 fun i => ?_
  have hκ : Measurable (rieszKernelGrad d (criticalS d)) := by
    unfold rieszKernelGrad gradient
    exact (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.measurable.comp
      (measurable_fderiv ℝ (rieszKernel d (criticalS d)))
  have hM : Measurable (Torus.matVec (quadraticGradientDyn d (criticalS d) a beta).M) :=
    (LinearMap.continuous_of_finiteDimensional
      (Matrix.toEuclideanLin (quadraticGradientDyn d (criticalS d) a beta).M)).measurable
  have hG : Measurable (gradient (quadraticGradientDyn d (criticalS d) a beta).V) :=
    (HRS.MS.S113X2.s113a_gradient_conf_contDiff (d := d) a).continuous.measurable
  unfold particleDriftW
  have hs : Measurable (fun Y : EucConfig d N => ∑ j ∈ Finset.univ.erase i,
      Torus.matVec (quadraticGradientDyn d (criticalS d) a beta).M
        (rieszKernelGrad d (quadraticGradientDyn d (criticalS d) a beta).s (Y i - Y j))) :=
    Finset.measurable_sum _ fun j _ =>
      hM.comp (hκ.comp ((measurable_pi_apply i).sub (measurable_pi_apply j)))
  exact (hs.const_smul (1 / (N : ℝ))).sub (hG.comp (measurable_pi_apply i))

end HRS.MS.R26T8A

end
