import HRS.MC.L2C0Aux2

/-!
# Packet L2C-0: smoothness of the adjoint propagator of a smooth test function

Relocated proof of `HRS.MC.L2Cov.l2cs_propagator_smooth` (the frozen statement stays `sorry` in
`HRS/MC/L2CovSpec.lean`; the tie `example` is in `HRS/MC/L2C0Tie.lean`).

Route: the hypotheses of Proposition 3.9 (`AdjointData`) hold at every Sobolev level `m` and horizon (the
`C^{m+3}` bounds of `ρ^t` are the proved `Regime.reg`, `HRS.MC.RegSet.reg_proof`); at level `m`, the propagator
is `toFun` of the level-`m` forward solution (`ClassicalPart.propagator_eq_toFun`, which uses
`classical_adjoint_unique` to identify the junk-valued `propagator` with it), hence in `H^m ⊂ C^n` for `n < m - d/2`
(Sobolev embedding `toFun_isCk_le`).  The junk case `r = t = 0` is trivial.
-/

noncomputable section

open MeasureTheory Filter Topology
open HRS HRS.Sec7

namespace HRS.MC.L2C0

variable {d : ℕ}

/-- The density path `ρ^t` of the regime satisfies the pairing-continuity hypothesis. -/
theorem l2c0_rho_prob_cont (R : Regime d) :
    (∀ r : ℝ, 0 ≤ r → IsProbDensity (R.ρ r)) ∧
    ∀ T : ℝ, ∀ ψ : Torus d → ℝ, Continuous ψ →
      ContinuousOn (fun r => ∫ x, ψ x * R.ρ r x) (Set.Icc 0 T) := by
  obtain ⟨K, ρc, hK1, hK2, hsol, hρ⟩ := HRS.MC.RegSet.rgs_sol R 0
  have hH := R.finiteRegHyp K hK2
  have hd : 1 ≤ d := by have := R.hd; omega
  have hreal := PDE.MFGlobal.isRealCoeff_of_isMFSolutionHK hd R.D.s R.β R.β K R.D.V R.ρ₀ hH R.β
    ⟨le_rfl, le_rfl⟩ ρc hsol
  refine ⟨fun r hr => ?_, fun T ψ hψ => ?_⟩
  · rw [hρ r hr]
    exact PDE.MFWeak.isProbDensity_mfPath hd R.D.s R.β R.β K R.D.V R.ρ₀ hH R.β ⟨le_rfl, le_rfl⟩ ρc
      hsol r hr
  · have hK3 : (d : ℝ) / 2 + 2 < K := by
      have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
      linarith
    have h := (PDE.MFWeak.continuousOn_pairings hd R.D.s R.D.hs0 R.D.hsd K hK3 R.D.V R.ρ₀ hH.hV
      R.β⁻¹ ρc (T := T) ⟨PDE.MFApriori.IsMFSolutionHK.toSolOn hsol T, fun τ hτ => hreal τ hτ.1⟩
      ψ hψ).1
    refine h.congr fun r hr => ?_
    simp only [hρ r hr.1]

/-- The frozen density path `ρ_β` satisfies the hypotheses on the path. -/
theorem l2c0_frozen_hyps (R : Regime d) :
    (∀ r : ℝ, 0 ≤ r → IsProbDensity ((fun _ : ℝ => R.ρβ) r)) ∧
    (∀ j : ℕ, ∃ Λ : ℝ, ∀ T : ℝ, IsRegularMF j Λ T (fun _ : ℝ => R.ρβ)) ∧
    ∀ T : ℝ, ∀ ψ : Torus d → ℝ, Continuous ψ →
      ContinuousOn (fun r => ∫ x, ψ x * (fun _ : ℝ => R.ρβ) r x) (Set.Icc 0 T) := by
  obtain ⟨hth, hsm, -⟩ := R.thermal
  refine ⟨fun _ _ => hth.1, fun j => ⟨Torus.cbNorm j R.ρβ, fun T t _ =>
    ⟨PDE.ClassicalAux.isCk_of_le (WithTop.coe_le_coe.2 le_top) hsm, le_rfl⟩⟩, ?_⟩
  intro T ψ hψ
  exact continuousOn_const

/-- (Packet L2C-0, `l2cs_propagator_smooth`.)  For a smooth test function `φ` the adjoint propagators `U^{r,t}φ` along
`ρ^t` and along the frozen `ρ_β` are smooth in `x`. -/
theorem l2c0_proof (R : Regime d) (φ : Torus d → ℝ) (hφ : Torus.IsSmooth φ) :
    ∀ r t : ℝ, 0 ≤ r → r ≤ t →
      Torus.IsSmooth (propagator R.D R.ρ r t φ) ∧
      Torus.IsSmooth (propagator R.D (fun _ => R.ρβ) r t φ) := by
  intro r t hr hrt
  have hd : 1 ≤ d := by have := R.hd; omega
  have hν : 0 < R.D.invβ := by rw [R.hDβ]; exact inv_pos.2 R.hβ
  obtain ⟨hprob, hcont⟩ := l2c0_rho_prob_cont R
  obtain ⟨hprob', hreg', hcont'⟩ := l2c0_frozen_hyps R
  refine ⟨?_, ?_⟩
  · exact l2c0_smooth_of_adjointData hd R.D R.ρ
      (l2c0_adjointData_generic R.D R.hM R.hV hν R.ρ hprob (fun j => HRS.MC.RegSet.reg_proof R j)
        hcont) φ hφ r t hr hrt
  · exact l2c0_smooth_of_adjointData hd R.D (fun _ => R.ρβ)
      (l2c0_adjointData_generic R.D R.hM R.hV hν (fun _ => R.ρβ) hprob' hreg' hcont') φ hφ r t hr hrt

end HRS.MC.L2C0

end
