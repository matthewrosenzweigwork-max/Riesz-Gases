import HRS.MC.S7S7fAux2

/-!
# Packet S7f, helper 3: the Stein equation along the modes and the exact identity at level `N`

For `f = steinSolG G Φ` (`Φ` in the `C_b^5` unit ball) the Stein equation reads, after expanding the Gaussian
contraction (`s7f_gauss_expand`), `∑_{kl} C_{kl} D²f(x)[ε_k,ε_l] - Df(x)[x] = Φ(x) - E Φ(G)`.  Integrating against
`Q_{N,γ}` and inserting the Hilbert-space Stein identity `S7c`:

`√N (E Φ(W_N) - E Φ(G)) = R1 - T_A + γ T_B`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7f

open HRS HRS.Sec7 HRS.MC.SEdge HRS.StaticLimitAux HRS.MC.Sec7.S7d HRS.MC.Sec7.S7c

variable {d : ℕ} {s : ℝ} {r : ℝ}

theorem s7f_D2_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℝ) (x u w : E) :
    iteratedFDeriv ℝ 2 f x ![u, w] = fderiv ℝ (fderiv ℝ f) x u w := by
  rw [iteratedFDeriv_two_apply]; rfl

theorem s7f_stein_expand (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (hr : r = 2 * (d : ℝ) + 6)
    {γ : ℝ} (hγ : 0 ≤ γ) {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ)
    {a : NonzeroLattice d → Torus d → ℝ} {v : NonzeroLattice d → Fin d → Torus d → ℝ} {C₀ : ℝ}
    (hmode : s7_ModeData d s γ ρ r a v C₀)
    (G : Measure (NegSobolev d r)) [IsProbabilityMeasure G]
    (hG : IsCenteredGaussianWithCov r G fun φ ψ =>
      ∫ x, φ x * responseRep (periodicRiesz d s) (withDensityReal ρ) γ ψ x ∂(withDensityReal ρ))
    {Φ : NegSobolev d r → ℝ} (hΦ : Φ ∈ CbUnitBall (NegSobolev d r) 5) (x : NegSobolev d r) :
    ∑' k, ∑' l, s7_Cmode r ρ a k l * iteratedFDeriv ℝ 2 (steinSolG G Φ) x ![s7_eps r k, s7_eps r l] -
        fderiv ℝ (steinSolG G Φ) x x = Φ x - ∫ F, Φ F ∂G := by
  have hmem : MemCb 5 Φ := ⟨hΦ.1, hΦ.2.1⟩
  have h := HRS.stein_core hG.1 hmem x
  have e := s7f_gauss_expand hd hs0 hs hr hγ hρ hmode G hG (fderiv ℝ (fderiv ℝ (steinSolG G Φ)) x)
  simp_rw [s7f_D2_eq] at h ⊢
  rw [← e]
  exact h

end HRS.MC.Sec7.S7f

end
