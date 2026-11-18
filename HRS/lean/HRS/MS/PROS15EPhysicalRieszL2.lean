import HRS.MS.PROS15EChaosHS
import HRS.MS.PROS15dPhysicalSpectralStd
import HRS.MS.S21H2_S14a

/-!
# Physical Riesz spectral Wick quadratic: L² convergence under its own tilt

This is an unconditional specialization of the reviewed Hilbert--Schmidt
second-chaos estimate to the actual ProductGaussian field associated to the
initial Riesz trajectory. All spectral objects come from the physical kernel,
including the possibly nonsmooth eigenfunctions. The theorem does not
identify the prescribed smooth-basis Wick representative and therefore does
not close the frozen R26-T3.S15e statement.
-/
set_option autoImplicit false
noncomputable section
open HRS MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3

theorem s15e_physical_riesz_spectral_tilted_L2
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) (I : ProductGaussian (r26t3_mu R 0))
    (γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ (lam : ℕ → ℝ) (e : ℕ → HRS.Euc p.d → ℝ)
      (Q : I.Ω → ℝ),
      (∀ j, 0 ≤ lam j ∧ HRS.Whole.MemL2Zero (r26t3_mu R 0) (e j)) ∧
      (∀ i j, ∫ x, e i x * e j x ∂(r26t3_mu R 0) =
        if i = j then 1 else 0) ∧
      Summable (fun j => lam j ^ 2) ∧
      Tendsto (fun n => eLpNorm (fun z : HRS.Euc p.d × HRS.Euc p.d =>
        HRS.Whole.r2CenterKernel (r26t3_mu R 0)
          (fun x y => HRS.Whole.rieszKernel p.d p.s (x-y)) z.1 z.2 -
          ∑ j ∈ Finset.range n, lam j * e j z.1 * e j z.2) 2
        ((r26t3_mu R 0).prod (r26t3_mu R 0))) atTop (𝓝 0) ∧
      HRS.TendstoL2 I.P
        (s21h2_s15c_Qn (fun j => I.η (e j)) lam) Q ∧
      Integrable (fun ω => Real.exp (-γ * Q ω)) I.P ∧
      Integrable (fun ω => Real.exp (-(2 * γ) * Q ω)) I.P ∧
      Tendsto (fun n => ∫ ω,
        (s21h2_s15c_Qn (fun j => I.η (e j)) lam n ω - Q ω)^2
        ∂(r26t3_tilt I.P (fun ω => γ * Q ω))) atTop (𝓝 0) := by
  letI : IsProbabilityMeasure (r26t3_mu R 0) :=
    s21h2_mu_prob hδ hδh R
  letI := I.mΩ
  letI := I.prob
  obtain ⟨lam, e, he, hon, hsum, hKernel, _hFull⟩ :=
    r26t3_kernel_spectral hδ hδh R
  have hStd : HRS.IsStdGaussianSeq I.P (fun j => I.η (e j)) :=
    s15d_physical_spectral_standard_gaussian_seq I e
      (fun j => (he j).2) hon
  obtain ⟨Q, hQ, _hChaos, hExp, hExp2, hTilt⟩ :=
    s15e_hs_spectral_tilted_sections_L2 I.P
      (fun j => I.η (e j)) hStd lam
      (fun j => (he j).1) hsum γ hγ
  exact ⟨lam, e, Q, he, hon, hsum, hKernel, hQ, hExp, hExp2, hTilt⟩

#print axioms s15e_physical_riesz_spectral_tilted_L2
end HRS.MS.R26T3
