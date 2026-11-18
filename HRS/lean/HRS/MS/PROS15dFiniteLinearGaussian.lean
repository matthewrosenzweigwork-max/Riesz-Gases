import HRS.MS.PROS15dJointGaussian

/-!
# S15d: finite linear images of the exact tilted Gaussian spectral law

This is the finite-dimensional linear-change-of-observables step needed to
pass from the spectral coordinate law to finite spectral approximations of
arbitrary physical test functions. No rank or nonsingularity condition is
imposed on the linear map; zero eigenvalues and linearly dependent tests
are included.
-/
set_option autoImplicit false
noncomputable section
open HRS MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3

theorem s15d_finite_spectral_linear_gaussian
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n m : ℕ}
    (X : Fin n → Ω → ℝ)
    (hXm : ∀ i, AEMeasurable (X i) P)
    (v : Fin n → ℝ≥0)
    (hLaw : P.map (fun ω (i : Fin n) => X i ω) =
      Measure.pi (fun i : Fin n => gaussianReal 0 (v i)))
    (A : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ)) :
    HRS.IsCenteredGaussian
      (P.map (fun ω => A (fun i : Fin n => X i ω))) := by
  let π : Measure (Fin n → ℝ) :=
    Measure.pi (fun i : Fin n => gaussianReal 0 (v i))
  have hG : HRS.IsCenteredGaussian π :=
    s15d_centered_gaussian_product n v
  have hGA : HRS.IsCenteredGaussian (π.map A) := by
    letI : IsGaussian π := hG.1
    refine ⟨inferInstance, fun L => ?_⟩
    rw [integral_map A.continuous.measurable.aemeasurable
      L.continuous.aestronglyMeasurable]
    exact hG.2 (L.comp A)
  have hXvec : AEMeasurable (fun ω (i : Fin n) => X i ω) P :=
    AEMeasurable.of_eval hXm
  have hmap := AEMeasurable.map_map_of_aemeasurable
    A.continuous.measurable.aemeasurable hXvec
  change HRS.IsCenteredGaussian
    (P.map (A ∘ (fun ω (i : Fin n) => X i ω)))
  rw [← hmap, hLaw]
  exact hGA

#print axioms s15d_finite_spectral_linear_gaussian
end HRS.MS.R26T3
