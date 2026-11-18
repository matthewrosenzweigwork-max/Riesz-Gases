import HRS.MS.PROS15dPhysicalSpectralStd
import HRS.MS.S21H2_S14a

/-!
# R26-T3.S15d: exact Hilbert–Schmidt spectral tilt in the physical Riesz Gaussian field

This combines the actual Riesz-kernel spectral decomposition (S14a),
the exact ProductGaussian isonormal standard Gaussian sequence for its
possibly nonsmooth eigenfunctions, and the infinite Hilbert–Schmidt Gaussian
tilt (S15c). The resulting quadratic and tilted finite-vector Gaussian laws
live on the SAME physical Gaussian probability space. The original S15d
still requires identifying this quadratic with the arbitrarily supplied
all-smooth-ONB Wick representative and the full susceptibility covariance.
-/
set_option autoImplicit false
noncomputable section
open HRS MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3

theorem s15d_physical_riesz_spectral_tilt
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) (I : ProductGaussian (r26t3_mu R 0))
    (γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ (lam : ℕ → ℝ) (e : ℕ → HRS.Euc p.d → ℝ) (Q : I.Ω → ℝ),
      (∀ j, 0 ≤ lam j ∧ HRS.Whole.MemL2Zero (r26t3_mu R 0) (e j)) ∧
      (∀ i j, ∫ x, e i x * e j x ∂(r26t3_mu R 0) =
        if i = j then 1 else 0) ∧
      Summable (fun j => lam j ^ 2) ∧
      Tendsto (fun n => eLpNorm (fun z : HRS.Euc p.d × HRS.Euc p.d =>
        HRS.Whole.r2CenterKernel (r26t3_mu R 0)
          (fun x y => HRS.Whole.rieszKernel p.d p.s (x-y)) z.1 z.2 -
          ∑ j ∈ Finset.range n, lam j * e j z.1 * e j z.2) 2
        ((r26t3_mu R 0).prod (r26t3_mu R 0))) atTop (𝓝 0) ∧
      HRS.TendstoL2 I.P (fun n ω =>
        (1/2 : ℝ) * ∑ j ∈ Finset.range n,
          lam j * ((I.η (e j) ω)^2-1)) Q ∧
      Integrable (fun ω => Real.exp (-γ*Q ω)) I.P ∧
      ∀ n, HRS.law (r26t3_tilt I.P (fun ω => γ*Q ω))
        (fun ω (j : Fin n) => I.η (e j) ω) =
        Measure.pi (fun j : Fin n =>
          gaussianReal 0 ((1+γ*lam j)⁻¹).toNNReal) := by
  letI : IsProbabilityMeasure (r26t3_mu R 0) := s21h2_mu_prob hδ hδh R
  letI := I.mΩ
  letI := I.prob
  obtain ⟨lam, e, he, hon, hsum, hKernel, _hFull⟩ :=
    r26t3_kernel_spectral hδ hδh R
  have hStd : HRS.IsStdGaussianSeq I.P (fun j => I.η (e j)) :=
    s15d_physical_spectral_standard_gaussian_seq I e
      (fun j => (he j).2) hon
  obtain ⟨Q, hQ, hInt, _hZ, hLaw⟩ :=
    r26t3_hs_gaussian_tilt I.P (fun j => I.η (e j)) hStd
      lam (fun j => (he j).1) hsum γ hγ
  exact ⟨lam, e, Q, he, hon, hsum, hKernel, hQ, hInt, hLaw⟩

end HRS.MS.R26T3
