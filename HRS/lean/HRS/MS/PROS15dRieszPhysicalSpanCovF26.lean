import HRS.MS.PROS15dPhysicalSpanCovF26
import HRS.MS.PROS15dPhysicalRieszProjectionP21

/-!
# S15d: genuine finite physical Riesz first-chaos susceptibility matrices

The mixed covariance concerns actual first-chaos evaluations of *spatial*
linear combinations, not only sums of Gaussian coordinates. It is on the
same ProductGaussian space with the same normalized Hilbert--Schmidt tilt;
no smoothness of the spectral eigenfunctions is required.
-/
set_option autoImplicit false
noncomputable section
open HRS MeasureTheory ProbabilityTheory Filter Topology RealInnerProductSpace
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3

theorem s15d_physical_riesz_spatial_span_covariance
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) (I : ProductGaussian (r26t3_mu R 0))
    (γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ (lam : ℕ → ℝ) (e : ℕ → HRS.Euc p.d → ℝ)
      (Q : I.Ω → ℝ),
      (∀ j, 0 ≤ lam j ∧ HRS.Whole.MemL2Zero (r26t3_mu R 0) (e j)) ∧
      Summable (fun j => lam j ^ 2) ∧
      Tendsto (fun n => eLpNorm (fun z : HRS.Euc p.d × HRS.Euc p.d =>
        HRS.Whole.r2CenterKernel (r26t3_mu R 0)
          (fun x y => HRS.Whole.rieszKernel p.d p.s (x-y)) z.1 z.2 -
          ∑ j ∈ Finset.range n, lam j * e j z.1 * e j z.2) 2
        ((r26t3_mu R 0).prod (r26t3_mu R 0))) atTop (𝓝 0) ∧
      HRS.TendstoL2 I.P (fun n ω =>
        (1 / 2 : ℝ) * ∑ j ∈ Finset.range n,
          lam j * (I.η (e j) ω ^ 2 - 1)) Q ∧
      Integrable (fun ω => Real.exp (-γ * Q ω)) I.P ∧
      Integrable (fun ω => Real.exp (-(2 * γ) * Q ω)) I.P ∧
      ∀ n (a b : Fin n → ℝ),
        (∫ ω,
            I.η (fun x => ∑ j : Fin n, a j * e j x) ω *
            I.η (fun x => ∑ j : Fin n, b j * e j x) ω
            ∂(r26t3_tilt I.P (fun ω => γ * Q ω))) =
        ∑ i : Fin n, a i * b i *
          (Real.toNNReal ((1 + γ * lam i)⁻¹) : ℝ) := by
  letI : IsProbabilityMeasure (r26t3_mu R 0) :=
    s21h2_mu_prob hδ hδh R
  letI := I.mΩ
  letI := I.prob
  obtain ⟨lam, e, Q, he, _b, hlam, _hon, hsum, hKernel,
    hQ, hExp1, hExp2, hLaw, _hb, _hProj⟩ :=
    s15d_physical_riesz_alltest_spectral_tilt_projection hδ hδh R I γ hγ
  have hW : AEMeasurable (fun ω => γ * Q ω) I.P :=
    (hQ.1.const_mul γ).aemeasurable
  have hExp1' : Integrable (fun ω => Real.exp (-(γ * Q ω))) I.P := by
    simpa only [neg_mul] using hExp1
  have hExp2' : Integrable (fun ω => Real.exp (-(2 * (γ * Q ω)))) I.P := by
    convert hExp2 using 1
    funext ω
    ring
  refine ⟨lam, e, Q, (fun j => ⟨hlam j, he j⟩), hsum,
    hKernel, hQ, hExp1, hExp2, ?_⟩
  intro n a b
  have hGaussian : (r26t3_tilt I.P (fun ω => γ * Q ω)).map
      (fun ω (i : Fin n) => I.η (e i) ω) =
      Measure.pi (fun i : Fin n =>
        gaussianReal 0 (Real.toNNReal ((1 + γ * lam i)⁻¹))) := by
    simpa only [HRS.law] using hLaw n
  exact s15d_physical_finite_span_scalar_covariance I
    (fun ω => γ * Q ω) hW hExp1' hExp2'
    e (fun j => (he j).1) n
    (fun i : Fin n => Real.toNNReal ((1 + γ * lam i)⁻¹))
    hGaussian a b

#print axioms s15d_physical_riesz_spatial_span_covariance
end HRS.MS.R26T3
