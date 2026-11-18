import HRS.MS.PROS15dTiltConvergence
import HRS.MS.S21G2_S11aC

/-!
# R26-T3.S15d: all finite tilted spectral-coordinate vectors are centered Gaussian

The existing S15c tilt gives the exact finite-coordinate product law. We
verify that an arbitrary finite product of centered real Gaussians is a
centered Gaussian measure on Euclidean coordinate space, including singular
and zero variances.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3

theorem s15d_centered_gaussian_product (n : ℕ) (v : Fin n → ℝ≥0) :
    HRS.IsCenteredGaussian (Measure.pi (fun i : Fin n => gaussianReal 0 (v i))) := by
  classical
  let π : Measure (Fin n → ℝ) := Measure.pi (fun i => gaussianReal 0 (v i))
  letI : IsProbabilityMeasure π := inferInstance
  have hIndep : iIndepFun (fun (i : Fin n) (z : Fin n → ℝ) => z i) π :=
    iIndepFun_pi (μ := fun i : Fin n => gaussianReal 0 (v i))
      (X := fun _ => id) (fun _ => aemeasurable_id)
  have hCoord : ∀ i : Fin n, HasGaussianLaw (fun z : Fin n → ℝ => z i) π := by
    intro i
    have hmap : π.map (fun z : Fin n → ℝ => z i) = gaussianReal 0 (v i) := by
      rw [show (fun z : Fin n → ℝ => z i) = Function.eval i from rfl, Measure.pi_map_eval]
      simp
    exact ⟨(measurable_pi_apply i).aemeasurable, by rw [hmap]; infer_instance⟩
  have hjoint : HasGaussianLaw (fun z : Fin n → ℝ => (fun i => z i)) π :=
    hIndep.hasGaussianLaw hCoord
  have hmeani : ∀ i : Fin n, ∫ z : Fin n → ℝ, z i ∂π = 0 := by
    intro i
    calc
      ∫ z : Fin n → ℝ, z i ∂π =
        ∫ x : ℝ, x ∂(π.map (fun z : Fin n → ℝ => z i)) := by
          exact (integral_map (μ := π) (φ := fun z : Fin n → ℝ => z i)
            (f := fun x : ℝ => x) (measurable_pi_apply i).aemeasurable aestronglyMeasurable_id).symm
      _ = ∫ x : ℝ, x ∂(gaussianReal 0 (v i)) := by
        rw [show (fun z : Fin n → ℝ => z i) = Function.eval i from rfl, Measure.pi_map_eval]
        simp
      _ = 0 := by simp
  have hInt : ∀ i : Fin n, Integrable (fun z : Fin n → ℝ => z i) π := by
    intro i
    exact (hCoord i).integrable
  have hMean : ∀ L : StrongDual ℝ (Fin n → ℝ), ∫ z : Fin n → ℝ, L z ∂π = 0 := by
    intro L
    have hLin : ∀ z : Fin n → ℝ,
        L z = ∑ i : Fin n, L (fun j => if i = j then 1 else 0) * z i := by
      intro z
      have hh := L.toLinearMap.pi_apply_eq_sum_univ z
      change L z = ∑ i : Fin n, z i * L (fun j => if i = j then 1 else 0) at hh
      simpa only [mul_comm] using hh
    calc
      ∫ z : Fin n → ℝ, L z ∂π =
          ∫ z : Fin n → ℝ, ∑ i : Fin n,
            L (fun j => if i = j then 1 else 0) * z i ∂π :=
              integral_congr_ae (ae_of_all _ hLin)
      _ = ∑ i : Fin n, L (fun j => if i = j then 1 else 0) *
          ∫ z : Fin n → ℝ, z i ∂π := by
            rw [integral_finset_sum _ (fun i _ => (hInt i).const_mul _)]
            simp only [integral_const_mul]
      _ = 0 := by simp only [hmeani, mul_zero, Finset.sum_const_zero]
  change HRS.IsCenteredGaussian π
  constructor
  · have h : π.map (fun z : Fin n → ℝ => (fun i => z i)) = π := by
      simp only [show (fun z : Fin n → ℝ => (fun i => z i)) = id from rfl, Measure.map_id]
    rw [← h]
    exact hjoint.isGaussian_map
  · exact hMean

end HRS.MS.R26T3
