import HRS.MC.L2C1Aux2

/-!
# Packet L2C-1: the equilibrium `L²` Lyapunov functional (stationary part)

Relocated proof of `HRS.MC.L2Cov.l2cs_equilibrium_L2` (the frozen statement stays `sorry` in
`HRS/MC/L2CovSpec.lean`; the tie is `HRS/MC/L2C1Tie.lean`).

## Plan (route actually used)

Write `μ = ρ_β dx`, `ν = β⁻¹`, `A = I + βKP` on `L²(μ)` (so that the generator `-A_β L_β` of the TeX is
`-ν A (L_β ·)`), and `R = A⁻¹` (a bounded, self-adjoint, coercive operator,
`HRS.PDE.MFLinear.exists_inverse`).  For `y_v = [S_β(v)ψ] ∈ L²(μ)` consider the `A⁻¹`-Lyapunov functional

  `F(v) = ⟨y_v, R y_v⟩_{L²(μ)}`.

* Everything about differentiating `F` along the classical frozen solution is already in the repository:
  `HRS.PDE.MFLinear.frozen_F_props` gives `F` continuous on `[0,∞)`, `F' = -2ν ∫ ρ_β |∇S_β(v)ψ|²` and `F → 0`
  (this is `Q_β𝓛_β = -A_β L_β` = `HRS.PDE.equilibrium_operator_order`, used inside `inner_R_eqGen`).
* `l2c1_form_bounds` (Aux1): since `A` is bounded and coercive, `⟨y,Ry⟩ ≍ ‖y‖²_{L²(μ)}`.
* Weighted Poincaré (`MFAdjoint.exists_weighted_poincare`) on the centered `S_β(v)ψ`:
  `∫ρ|∇S|² ≥ c_P ‖y_v‖² ≥ (c_P/κ₂) F(v)`, hence `F' ≤ -a F`, and `l2c1_gronwall` gives `F(τ) ≤ e^{-aτ}F(0)`.
  With `c₀ ≤ ρ_β ≤ Λ₀` (`l2c1_l2Inner_bounds`) this is the `L²(dx)` decay (1), with `F(0) ≤ κ₂Λ₀ ‖Q_βψ‖²`.
* The integrated gradient bound (2) is the integrated Lyapunov identity: `susceptibilityCov_eq_integral`
  (improper FTC for `F`, `F(0) = C_β(ψ,ψ)`) gives `2ν ∫_0^∞ ∫ρ_β|∇S|² = C_β(ψ,ψ)`, and
  `susceptibilityCov_bounds` gives `C_β(ψ,ψ) ≲ ‖Q_βψ‖²_{L²(μ)}`; `ρ_β ≥ c₀` removes the weight.
* The abstract statement at the level of `FrozenHyp` data is `l2c1_frozen` (Aux2).  Here it is instantiated for a
  `Regime` (`frozenHyp_of_smooth`; `R.D = mfData …` because `R.D.M = -1`, `R.D.invβ = β⁻¹`) and smooth `ψ`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

namespace MC

namespace L2C1

open HRS.Sec7

variable {d : ℕ}

theorem l2c1_dyn_eq (R : Regime d) :
    R.D = PDE.mfData d R.D.s R.D.hs0 R.D.hsd R.D.V R.β R.hβ := by
  have hM := R.hM
  have hi := R.hDβ
  unfold PDE.mfData
  generalize R.D = D at *
  cases D
  simp_all

theorem l2c1_proof (R : Regime d) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ ψ : Torus d → ℝ, Torus.IsSmooth ψ → ∀ τ : ℝ, 0 ≤ τ →
      PDE.l2NormSq (PDE.equilibriumSemigroup R.D R.ρβ τ ψ) ≤
        C * Real.exp (-c * τ) * PDE.l2NormSq (projMean (withDensityReal R.ρβ) ψ) ∧
      ∫ v in Set.Icc (0 : ℝ) τ, ∫ x, ‖Torus.grad (PDE.equilibriumSemigroup R.D R.ρβ v ψ) x‖ ^ 2 ≤
        C * PDE.l2NormSq (projMean (withDensityReal R.ρβ) ψ) := by
  obtain ⟨hth, hsm, hpos⟩ := R.thermal
  obtain ⟨c₀, Λ₀, H⟩ := PDE.MFPair.frozenHyp_of_smooth (d := d) R.D.s R.D.hs0 R.D.hsd R.β R.hβ
    R.D.V R.hV R.ρβ hth hsm hpos (2 * PDE.mStar d + 4)
  obtain ⟨C, c, hC, hc, hmain⟩ := l2c1_frozen R.hd H
  refine ⟨C, c, hC, hc, fun ψ hψ τ hτ => ?_⟩
  have hD := l2c1_dyn_eq R
  have hcont : Continuous ψ :=
    Torus.continuous_of_continuous_lift (PDE.MFPair.isCk_of_smooth_ps hψ 0).continuous
  have hmem : MemSobolev ((PDE.mStar d : ℝ) + 4) ψ :=
    PDE.MFSemigroup.memSobolev_of_isSmooth hψ _
  rw [hD]
  exact hmain ψ hcont hmem τ hτ

end L2C1

end MC

end HRS
