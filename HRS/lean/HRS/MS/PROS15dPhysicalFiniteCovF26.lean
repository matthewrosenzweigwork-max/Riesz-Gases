import HRS.MS.PROS15dFiniteScalarCovF26
import HRS.MS.PROS15dPhysicalRieszProjectionP21
import HRS.MS.PROS15dPhysicalFirstChaos

/-!
# S15d: finite scalar susceptibility coordinates of the actual physical Riesz tilt

This specializes the nondegenerate-or-degenerate finite Gaussian covariance
identity to the physical Riesz Hilbert--Schmidt quadratic, the original
isonormal ProductGaussian field, and its actual normalized Gibbs tilt. The
quadratic and the finite spectral variables remain on the same probability
space. No identification with the frozen susceptibility resolvent is assumed.
-/
set_option autoImplicit false
noncomputable section
open HRS MeasureTheory ProbabilityTheory Filter Topology RealInnerProductSpace
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3

theorem s15d_physical_riesz_finite_scalar_covariance
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
        (∫ ω, (∑ i : Fin n, a i * I.η (e i) ω) *
          (∑ j : Fin n, b j * I.η (e j) ω)
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
  let Pt := r26t3_tilt I.P (fun ω => γ * Q ω)
  have hW : AEMeasurable (fun ω => γ * Q ω) I.P :=
    (hQ.1.const_mul γ).aemeasurable
  have hExp1' : Integrable (fun ω => Real.exp (-(γ * Q ω))) I.P := by
    simpa only [neg_mul] using hExp1
  have hExp2' : Integrable (fun ω => Real.exp (-(2 * (γ * Q ω)))) I.P := by
    convert hExp2 using 1
    funext ω
    ring
  letI : IsProbabilityMeasure Pt :=
    r26t3_tilt_isProb I.P hW hExp1'
  refine ⟨lam, e, Q, (fun j => ⟨hlam j, he j⟩), hsum,
    hKernel, hQ, hExp1, hExp2, ?_⟩
  intro n a b
  have hX : ∀ i : Fin n, MemLp (I.η (e i)) 2 Pt := by
    intro i
    exact s15d_physical_first_chaos_tilt_L2 I (e i) (he i).1
      (fun ω => γ * Q ω) hW hExp1' hExp2'
  have hGaussian : Pt.map (fun ω (i : Fin n) => I.η (e i) ω) =
      Measure.pi (fun i : Fin n =>
        gaussianReal 0 (Real.toNNReal ((1 + γ * lam i)⁻¹))) := by
    simpa only [Pt, HRS.law] using hLaw n
  exact s15d_finite_spectral_scalar_covariance
    (fun i : Fin n => I.η (e i)) hX
    (fun i : Fin n => Real.toNNReal ((1 + γ * lam i)⁻¹))
    hGaussian a b

#print axioms s15d_physical_riesz_finite_scalar_covariance
end HRS.MS.R26T3
