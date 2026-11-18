import HRS.Main.GFFinal
import HRS.Main.A33Aux14
import HRS.Stochastic.Particle

/-!
# Packet DET22, part 1: Example 2.2 (`deterministic_comparison`, `deterministic_comparison_matrix`)

## Statement check (spec flag 8 of the 2026-10-17 headline-chain plan)

* `energyMoment P N X = ⨆ t, ∫ 𝓔_N^t(X^t(ω)) dP` is a real number (an `iSup` of integrals over `ω`), not a
  function of `ω`; the right-hand side `C (‖initial error‖ + κ_N 𝔈_N)` is therefore a constant, and
  `EnergyMomentFinite` is part of the hypotheses (no junk `0`).  `energyMoment ≥ 0`: `gff_energyMoment_nonneg`.
* The `∀ᵐ ω, ∀ t ∈ [0,T]` form is correct only because `X` is deterministic when `invβ = 0`: the integrated
  equation has noise coefficient `√(2·0) = 0`, so `X(·,ω)` solves the zero-noise ODE from the same initial
  point `x₀`, collision-free (`IsStrongSolution.no_collision`).  Pathwise uniqueness among collision-free strong
  solutions is `HRS.pathwiseUnique_of_locLipschitz` (locally Lipschitz lifted drift off the collision set,
  `liftedDrift_locLipschitz`, valid for every `d ≥ 2`, `0 ≤ s < d`, `V ∈ C²`).  The deterministic competitor
  `X'(t, ω) := X(t, ω₀)` for one good `ω₀` is again a collision-free strong solution (noise term is `0`), hence
  `X(t, ω) = X(t, ω₀)` for a.e. `ω` and all `t ≤ T`.
* No junk value: `flucPath` is continuous for a.e. `ω` (`gf_fluc_continuous_proof`), so `flucPath ω` is the genuine path
  and `toPath` of the deterministic `Y` is genuine (`IsLinearFluctuationSolution.cont`); the sup in `𝒳_{γ,T}` is the
  sup norm of `C([0,T]; E_γ)`.  The statements are corollaries of Theorem 2.1 (the `W₁` clause) and are TRUE as
  written.  For `invβ = 0`: `σ = κ`, `A = 1`, `q = 0`.

## Plan (all of it proved; Theorem 2.1 enters only through `general_fluctuation_proof`, `_matrix_proof`)

1. `det22_deterministic`: determinism of `X` (above).
2. `det22_linearSol`: with `EV` from `gf_ev_grad_proof` / `gf_ev_mat_proof` (dual evolution, `VE t t = 1`, strong
   continuity), `Y^t := V^{t,0} y₀` (deterministic) is an `IsLinearFluctuationSolution` at `q = 0` with initial value
   `y₀` (the Gaussian part is the Dirac mass at `0`), and `V^{t,0} y₀ = transportField t (y₀)`.
3. `det22_dirac_bound`: a `W₁` bound between the laws of a.e.-constant paths gives the sup-norm bound of the
   constants.
4. `det22_core`: assembly, for a general level `m` (`m = γ` gradient, `m = γ+2` matrix).
5. `Det22Final`: `deterministic_comparison_proof`, `deterministic_comparison_matrix_proof` with `example` ties.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Det22

variable {d : ℕ}

/-- DET22 step 1: for `invβ = 0` a collision-free strong solution started at the deterministic point `x₀` is
a.s. equal (for all `t ≤ T`) to the path of one fixed good sample point `ω₀`. -/
theorem det22_deterministic {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (P : Measure Ω)
    [IsProbabilityMeasure P] (D : DynData d)
    (hb : IsLocLipschitzDrift (liftedFree d N) (fun _ Z => liftedDrift D Z)) (hβ : D.invβ = 0)
    (T : ℝ) (x₀ : Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (hW : IsVectorBrownian P W)
    (X : ℝ≥0 → Ω → Config d N) (hX : IsStrongSolution P D T (fun _ => x₀) W X) :
    ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ) ≤ T → X t ω = X t ω₀ := by
  obtain ⟨Y, hYae, hXY⟩ := hX.lift
  have hU := pathwiseUnique_of_locLipschitz P D hb T (fun _ => x₀) W hW
  filter_upwards [hYae, hX.init, hX.cont, hX.no_collision] with ω₀ h1 h2 h3 h4
  have hX' : IsStrongSolution P D T (fun _ => x₀) W (fun t _ => X t ω₀) := by
    refine ⟨⟨fun t _ => Y t ω₀, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    · refine Eventually.of_forall fun ω t ht => ?_
      obtain ⟨hi, he⟩ := h1 t ht
      refine ⟨hi, fun i => ?_⟩
      have := he i
      simp only [hβ, mul_zero, Real.sqrt_zero, zero_smul, add_zero] at this ⊢
      exact this
    · funext t ω
      exact congrFun (congrFun hXY t) ω₀
    · exact Eventually.of_forall fun ω => h2
    · exact Eventually.of_forall fun ω => h3
    · exact fun t => measurable_const
    · exact Eventually.of_forall fun ω => h4
  exact hU X _ hX hX'

end HRS.Det22
