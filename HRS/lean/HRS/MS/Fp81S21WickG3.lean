import HRS.MS.Fp81S21WickG2
import HRS.MS.R2ChaosAux3
import HRS.MC.E213U18e

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace HRS.Fp81.S21

/-- Coordinate functions of a centered jointly Gaussian vector form a finite
Gaussian family in the sense used by the finite Wick estimates. -/
theorem fp81s21_wickG_joint_to_s94_family
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} (Z : Ω → EuclideanSpace ℝ (Fin n)) (hZm : AEMeasurable Z P)
    (hZ : HRS.IsCenteredGaussian (P.map Z)) :
    HRS.MS.R2Chaos.S94GFam P
      (fun i ω => (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (Z ω)) := by
  classical
  refine ⟨?_, ?_⟩
  · intro i
    exact ((EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).continuous.aemeasurable.comp_aemeasurable hZm)
  · intro α
    let L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := ∑ i, α i • EuclideanSpace.proj i
    let Y : Ω → ℝ := fun ω => ∑ i, α i *
      (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (Z ω)
    have hYeq : Y = fun ω => L (Z ω) := by
      funext ω
      simp [Y, L, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
        smul_eq_mul, mul_comm]
    have hgl : HasGaussianLaw Z P := ⟨hZm, hZ.1⟩
    have hYlaw : HasGaussianLaw Y P := by
      rw [hYeq]
      exact hgl.map_fun L
    have hYmean : ∫ ω, Y ω ∂P = 0 := by
      rw [hYeq]
      calc
        ∫ ω, L (Z ω) ∂P = ∫ z, L z ∂(P.map Z) := by
          exact (integral_map hZm L.continuous.aestronglyMeasurable).symm
        _ = 0 := hZ.2 L
    refine ⟨Var[Y; P].toNNReal, ?_⟩
    calc
      P.map Y = gaussianReal (∫ ω, Y ω ∂P) Var[Y; P].toNNReal := hYlaw.map_eq_gaussianReal
      _ = gaussianReal 0 _ := by rw [hYmean]

/-- The finite-dimensional covariance estimate for a symmetric centered
quadratic form.  The covariance domination constant `Λ` is the bound on the
quadratic covariance form, so the Wick polynomial has variance at most
`2 Λ²` times the coefficient Frobenius norm squared. -/
theorem fp81s21_wickG_symmetric_quadratic_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} {g : Fin n → Ω → ℝ}
    (hg : HRS.MS.R2Chaos.S94GFam P g) {Λ : ℝ} (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ α : Fin n → ℝ,
      HRS.MS.R2Chaos.s94q P g α ≤ Λ * ∑ i, α i ^ 2)
    (d : Fin n → Fin n → ℝ) (hds : ∀ i j, d i j = d j i) :
    ∫ ω, (∑ i, ∑ j, d i j *
      (g i ω * g j ω - ∫ ω', g i ω' * g j ω' ∂P)) ^ 2 ∂P ≤
      2 * Λ ^ 2 * ∑ i, ∑ j, d i j ^ 2 := by
  exact hg.quad_var hΛ0 hΛ d hds

#print axioms fp81s21_wickG_joint_to_s94_family
#print axioms fp81s21_wickG_symmetric_quadratic_bound

end HRS.Fp81.S21

end
