import HRS.MS.PROS15dJointGaussian

/-!
# S15d: scalar linear combinations of a genuine finite Gaussian spectral law

The finite scalar output is kept as a real-valued law, avoiding an artificial
nondegeneracy assumption on the coefficient vector or on spectral variances.
-/
set_option autoImplicit false
noncomputable section
open HRS MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3

theorem s15d_finite_scalar_linear_gaussian
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ}
    (X : Fin n → Ω → ℝ)
    (hXm : ∀ i, AEMeasurable (X i) P)
    (v : Fin n → ℝ≥0)
    (hLaw : P.map (fun ω (i : Fin n) => X i ω) =
      Measure.pi (fun i : Fin n => gaussianReal 0 (v i)))
    (a : Fin n → ℝ) :
    HRS.IsCenteredGaussian
      (P.map (fun ω => ∑ i : Fin n, a i * X i ω)) := by
  classical
  let A : (Fin n → ℝ) →L[ℝ] ℝ :=
    ∑ i : Fin n, a i •
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i
  have hA (x : Fin n → ℝ) : A x = ∑ i : Fin n, a i * x i := by
    simp [A, smul_eq_mul]
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
  have hGA' :
      HRS.IsCenteredGaussian
        (P.map (fun ω => A (fun i : Fin n => X i ω))) := by
    change HRS.IsCenteredGaussian
      (P.map (A ∘ (fun ω (i : Fin n) => X i ω)))
    rw [← hmap, hLaw]
    exact hGA
  have hfun :
      (fun ω => A (fun i : Fin n => X i ω)) =
        (fun ω => ∑ i : Fin n, a i * X i ω) := by
    funext ω
    exact hA _
  rw [← hfun]
  exact hGA'

#print axioms s15d_finite_scalar_linear_gaussian
end HRS.MS.R26T3
