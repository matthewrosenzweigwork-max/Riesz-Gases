import HRS.MS.PROS15dPhysicalRieszTilt
import HRS.MS.PROS15dActualSpectral

/-!
Independent R54 mathematical consumer of the physical S15d source.

Combines the *original* physical Riesz spectral theorem, the newly proved
smoothness-free Gaussian orthogonality result, and the already integrated
Hilbert--Schmidt tilt covariance theorem. The output involves actual
physical Gaussian variables and their actual common tilted law.
No conditional Wick or spectral identifications are substituted.
-/
set_option autoImplicit false
noncomputable section
open HRS MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3

theorem r54_physical_riesz_tilt_spectral_covariance
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
      (∀ i j : ℕ,
        ∫ ω, I.η (e i) ω * I.η (e j) ω
          ∂(r26t3_tilt I.P (fun ω => γ * Q ω)) =
        if i = j then
          (Real.toNNReal ((1 + γ * lam i)⁻¹) : ℝ)
        else 0) := by
  letI : IsProbabilityMeasure (r26t3_mu R 0) := s21h2_mu_prob hδ hδh R
  letI := I.mΩ
  letI := I.prob
  obtain ⟨lam, e, he, hon, hsum, hKernel, _hFull⟩ :=
    r26t3_kernel_spectral hδ hδh R
  have hStd : HRS.IsStdGaussianSeq I.P (fun j => I.η (e j)) :=
    s15d_physical_spectral_standard_gaussian_seq I e
      (fun j => (he j).2) hon
  obtain ⟨Q, hQ, hCov⟩ :=
    s15d_actual_spectral_covariance I.P (fun j => I.η (e j))
      hStd lam (fun j => (he j).1) hsum γ hγ
  exact ⟨lam, e, Q, he, hon, hsum, hKernel, hQ, hCov⟩

end HRS.MS.R26T3
