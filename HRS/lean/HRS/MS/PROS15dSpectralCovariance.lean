import HRS.MS.PROS15dSpectralMoments

/-!
# R26-T3.S15d: covariance of distinct Gaussian spectral coordinates

Given the exact finite-dimensional tilted law from S15c, this verifies the
covariance matrix as a genuine mixed-moment integral on the tilted space.
This does not yet identify susceptibility for arbitrary L2 observables.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R26T3

theorem s15d_pi_gaussian_covariance
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} (X : Fin n → Ω → ℝ)
    (hX : ∀ i, AEMeasurable (X i) P)
    (v : Fin n → ℝ≥0)
    (hLaw : P.map (fun ω i => X i ω) = Measure.pi (fun i => gaussianReal 0 (v i)))
    (i j : Fin n) :
    ∫ ω, X i ω * X j ω ∂P = if i = j then v i else 0 := by
  by_cases hij : i = j
  · subst j
    simp only [if_pos rfl, ← pow_two]
    exact s15d_pi_gaussian_coord_second X hX v hLaw i
  · let π : Measure (Fin n → ℝ) := Measure.pi (fun k => gaussianReal 0 (v k))
    have hvec : AEMeasurable (fun ω (k : Fin n) => X k ω) P :=
      AEMeasurable.of_eval hX
    have hmean : ∀ k : Fin n, ∫ z : Fin n → ℝ, z k ∂π = 0 := by
      intro k
      have hm : AEMeasurable (fun z : Fin n → ℝ => z k) π :=
        (measurable_pi_apply k).aemeasurable
      calc
        ∫ z : Fin n → ℝ, z k ∂π =
          ∫ x : ℝ, x ∂(π.map (fun z : Fin n → ℝ => z k)) := by
            exact (integral_map hm aestronglyMeasurable_id).symm
        _ = ∫ x : ℝ, x ∂(gaussianReal 0 (v k)) := by
          rw [show (fun z : Fin n → ℝ => z k) = Function.eval k from rfl, Measure.pi_map_eval]
          simp
        _ = 0 := by simp
    have hIndep : iIndepFun (fun k (z : Fin n → ℝ) => z k) π :=
      iIndepFun_pi (μ := fun k : Fin n => gaussianReal 0 (v k))
        (X := fun _ => id) (fun _ => aemeasurable_id)
    have hCross : ∫ z : Fin n → ℝ, z i * z j ∂π = 0 := by
      have h := (hIndep.indepFun hij).integral_mul_eq_mul_integral
        ((measurable_pi_apply i).aestronglyMeasurable)
        ((measurable_pi_apply j).aestronglyMeasurable)
      simpa [Pi.mul_apply, hmean] using h
    have hmap : ∫ ω, X i ω * X j ω ∂P = ∫ z : Fin n → ℝ, z i * z j ∂π := by
      have hfun : AEStronglyMeasurable (fun z : Fin n → ℝ => z i * z j) π :=
        ((measurable_pi_apply i).mul (measurable_pi_apply j)).aestronglyMeasurable
      calc
        ∫ ω, X i ω * X j ω ∂P =
          ∫ z : Fin n → ℝ, z i * z j ∂(P.map (fun ω (k : Fin n) => X k ω)) := by
            exact (integral_map hvec (by rw [hLaw]; exact hfun)).symm
        _ = _ := by rw [hLaw]
    simpa [hij] using hmap.trans hCross

end HRS.MS.R26T3
