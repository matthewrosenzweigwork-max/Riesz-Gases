import HRS.MC.S7S7dAux16

/-!
# Packet `s7_S7d_uniform_limits`, helper 17: the pair estimate for (R2)

For a fixed smooth `w` (a drift observable `w_{kl}`), with `t_j = ∫ a_j w dμ` and `|t_j| ≤ τ_j` (`τ` summable):
uniformly over the Stein class and the unit ball,
`E[Y_w D²f(W_N)[u,u']] → Σ_j t_j ∫ D³f(F)[u,u',ε_j] dG`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7d

open HRS HRS.Sec7 HRS.MC.SEdge HRS.StaticLimitAux

variable {d : ℕ} {s : ℝ} {r : ℝ}

theorem s7d_gauss_to_G (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {γ : ℝ} (hγ : 0 ≤ γ)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ)
    {a : NonzeroLattice d → Torus d → ℝ} {v : NonzeroLattice d → Fin d → Torus d → ℝ} {C₀ : ℝ}
    (hmode : s7_ModeData d s γ ρ r a v C₀) (K : Finset (NonzeroLattice d))
    (G : Measure (NegSobolev d r)) [IsProbabilityMeasure G]
    (hG : IsCenteredGaussianWithCov r G fun φ ψ =>
      ∫ x, φ x * responseRep (periodicRiesz d s) (withDensityReal ρ) γ ψ x ∂(withDensityReal ρ))
    {Θ : NegSobolev d r → ℝ} (hΘ : Continuous Θ) :
    ∫ z, Θ (HRS.MC.Sec7.S7c.s7c_iota r (HRS.MC.Sec7.S7c.s7c_kap K) z)
        ∂(multivariateGaussian 0 (sed_Cmat d s γ ρ
          (fun a => s7_phi r (HRS.MC.Sec7.S7c.s7c_kap K a)))) =
      ∫ F, Θ (truncE K F) ∂G := by
  rw [← s7d_law_G hd hs0 hs hγ hρ hmode (HRS.MC.Sec7.S7c.s7c_kap K) G hG]
  have hfm : AEStronglyMeasurable
      (fun z => Θ (HRS.MC.Sec7.S7c.s7c_iota r (HRS.MC.Sec7.S7c.s7c_kap K) z))
      (G.map (s7d_Wmap r (HRS.MC.Sec7.S7c.s7c_kap K))) :=
    (hΘ.comp (HRS.MC.Sec7.S7c.s7c_iota r (HRS.MC.Sec7.S7c.s7c_kap K)).continuous).aestronglyMeasurable
  rw [integral_map (s7d_Wmap r (HRS.MC.Sec7.S7c.s7c_kap K)).continuous.measurable.aemeasurable hfm]
  refine integral_congr_ae (Eventually.of_forall fun F => ?_)
  show Θ (HRS.MC.Sec7.S7c.s7c_iota r (HRS.MC.Sec7.S7c.s7c_kap K)
    (s7d_Wmap r (HRS.MC.Sec7.S7c.s7c_kap K) F)) = _
  rw [s7d_iota_Wmap]

end HRS.MC.Sec7.S7d

end
