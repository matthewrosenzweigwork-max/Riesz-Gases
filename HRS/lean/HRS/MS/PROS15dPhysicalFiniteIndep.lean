import HRS.MS.PROS15dPhysicalTiltConvergence
import HRS.MS.S21T4ProdF

/-!
# R26-T3.S15d: independent physical Gaussian tests with orthonormal covariance

A finite family of arbitrary spatial L2 tests with Kronecker-delta covariance
under the original Gaussian field gives jointly independent Gaussian random
variables. No smooth test assumption is imposed.
-/
set_option autoImplicit false
noncomputable section
open HRS MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3

theorem s15d_physical_finite_indep_orthogonal
    {d : ℕ} {μ : Measure (HRS.Euc d)} [IsProbabilityMeasure μ]
    (I : ProductGaussian μ) (n : ℕ)
    (e : Fin n → HRS.Euc d → ℝ)
    (he : ∀ i, MemLp (e i) 2 μ)
    (hOrtho : ∀ i j, ∫ x, HRS.Whole.projMean μ (e i) x *
        HRS.Whole.projMean μ (e j) x ∂μ = if i = j then 1 else 0) :
    iIndepFun (fun i => I.η (e i)) I.P := by
  letI := I.mΩ
  letI := I.prob
  let X : I.Ω → (Fin n → ℝ) := fun ω i => I.η (e i) ω
  have hXm : AEMeasurable X I.P :=
    AEMeasurable.of_eval (fun i => (I.meas (e i) (he i)).aemeasurable)
  have hG : HRS.IsCenteredGaussian (I.P.map X) := by
    simpa only [HRS.law, X] using I.gaussian n e he
  have hHas : HasGaussianLaw X I.P := ⟨hXm, hG.1⟩
  have hL2 : ∀ i, MemLp (I.η (e i)) 2 I.P :=
    fun i => s21t4_eta_memLp I (e i) (he i)
  have hMean : ∀ i, ∫ ω, I.η (e i) ω ∂I.P = 0 := by
    intro i
    obtain ⟨v, hLaw⟩ := s15d_physical_centered_gaussian_law I (e i) (he i)
    calc
      ∫ ω, I.η (e i) ω ∂I.P =
          ∫ x : ℝ, x ∂(I.P.map (I.η (e i))) := by
            exact (integral_map (I.meas (e i) (he i)).aemeasurable
              aestronglyMeasurable_id).symm
      _ = ∫ x : ℝ, x ∂(gaussianReal 0 v) := by rw [hLaw]
      _ = 0 := by simp
  have hCov : ∀ i j, i ≠ j →
      cov[I.η (e i), I.η (e j); I.P] = 0 := by
    intro i j hij
    rw [covariance_eq_sub (hL2 i) (hL2 j)]
    rw [hMean i, hMean j]
    simp only [mul_zero, sub_zero]
    have hC := I.covariance (e i) (e j) (he i) (he j)
    rw [hOrtho i j, if_neg hij] at hC
    simpa using hC
  exact hHas.iIndepFun_of_covariance_eq_zero hCov

end HRS.MS.R26T3
