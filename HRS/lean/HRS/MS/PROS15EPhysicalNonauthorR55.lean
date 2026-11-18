import HRS.MS.PROS15EPhysicalRieszL2

/-!
# Independent consumer of the physical Riesz spectral tilted-L² theorem

The statement is repeated with the original physical trajectory, actual Gaussian
probability space, single quadratic witness, precise factor in the Wick sections,
all original parameter restrictions, kernel approximation, and the normalized
law. No assumed smooth eigenbasis or additional moment hypotheses.
-/
set_option autoImplicit false
noncomputable section
open HRS MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3

theorem s15e_physical_nonauthor_exact_contract_r55
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
  exact s15e_physical_riesz_spectral_tilted_L2 hδ hδh R I γ hγ

#print axioms s15e_physical_nonauthor_exact_contract_r55
#print axioms s15e_physical_riesz_spectral_tilted_L2
end HRS.MS.R26T3
