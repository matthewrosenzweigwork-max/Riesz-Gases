import HRS.Energy.MFEFinal
import HRS.PDE.MovFinalConsumers
import HRS.Sections.DynConvFinal

/-!
# G336: Proposition 3.36 `M:B:prop:gronwall-catalog` (helper file 1)

## Statement check (2026-10-17, packet G336)

Row declarations: `gronwall_zero_temperature` (C1), `gronwall_zero_temperature_moment` (C1, consequence),
`gronwall_gradient_flow` (C2), `lowtemp_coulomb_threshold` (C3; also Prop 3.37's consequence).

* `gronwall_gradient_flow` (C2): statement OK.  `C₀ C` are chosen after `d, s, T, Λ, lam₀, ΛV, σ₀` and before
  `D, N, P, ρ, ...` (so no small-`C₀` defect: `C₀` is existential, `∃ C₀ C` comes first; `correctedEnergy` uses the chosen
  `C₀`).  No junk values: `MFEHyp` supplies `0 < invβ`, `Λ ≥ 1`, `lam₀ > 0`, `V ∈ C^{m*+2}`, finite entropies.
  PROOF (done, `G336Final.lean`): `mfe_uniform_proof` (3.41) + `transport_bound_uniform_proof` (constant `K t = C_tb`,
  `‖u_V^t‖_* ≤ C_tb` since `lam₀ ≤ ρ t`, `‖ρ t‖_{C^{m*+2}} ≤ Λ`, `‖V‖ ≤ ΛV`, `0 < invβ ≤ σ₀`) give
  `𝖤(f^t,μ^t) + o_N ≤ e^{C₁ C_tb T}(𝖤(f^0,μ°) + o_N)`; `C := e^{C₁ C_tb T}`; `C₀ := max (C₀ of 3.41) (C₀ of nonnegativity)`
  (the `o_N`-monotonicity `oNΛ_mono_C₀` and `e^{..} ≥ 1` absorb the change of `C₀`); `β⁻¹ 𝖧 ≥ 0` so
  `E[F_t + o] ≤ 𝖤_t + o`; push-forward `P.map X_t` (`integral_map`, `lintegral` of `ofReal` of a.e.-nonnegative integrable).

* `gronwall_zero_temperature` / `_moment` (C1): the ONLY THING WRONG is a missing regularity hypothesis on `D.V`.
  The `∃ C₀ C` prefix is fine (`C₀` existential, taken from `commutator_coercivity_common_proof`; no SPEC-C0 defect).
  But `D.V : Torus d → ℝ` is an arbitrary function: `D.V` enters the statement only through `Torus.grad D.V` (junk `0` where
  `lift D.V` is not differentiable), so the hypotheses (`HasTransportBound` of `u^t = M∇g*ρ^t - ∇V`, `IsMeanFieldSolution`,
  `IsStrongSolution`) constrain only the junk field `w = Torus.grad D.V` (Lipschitz by `HasTransportBound`), not a `C²`
  potential.  The energy identity of Prop 3.38 (`comparison_kernel_identity_proof`, `KIDAux*`) needs `Torus.IsCk 2 D.V`
  (ISSUES "SPEC-C0", Defect 2: same defect, repaired for 3.38 by `hV : Torus.IsCk 2 D.V`), and the TeX has `V ∈ C^{m_V}`
  as standing assumption (B:sec:conv-confinement).  Minimal repair: add `Torus.IsCk 2 D.V →` (or `(hV : ...)`) right after
  `Torus.SymNonpos D.M →` in both statements.  With it the chain is:
    1. a probability space with a filtered Brownian family (`exists_isBrownianFiltration_type`) carrying the deterministic
       collision-free path `x(t) = X t ω₀` (`IsStrongSolution` with `invβ = 0`, `IsFilteredSolution` trivial);
    2. `comparison_kernel_identity_proof` for smooth even `h = g_ε` (pathwise, since the path is deterministic) with
       `invβ = 0`: `F_{h}(t) - F_{h}(0) = ∫_0^t (½ Comm_{h}(u; x, ρ) + micro_h) dr`;
    3. `ε → 0` (dominated convergence on the compact collision-free set; `∇g_ε → ∇g` locally uniformly off `0`,
       `|(u(x)-u(y))·∇g_ε(x-y)| ≤ L C |x-y|^{-s}`): `F(t) - F(0) = ∫_0^t (½ Comm_g(u) + N⁻¹ ∑ a_iᵀ M a_i) dr`
       (`microTerm_self_kernel`, `SymNonpos`: second term `≤ 0`);
    4. `|Comm| ≤ C Λ' (F + o)` (`commutator_coercivity_common_proof`) and integral Grönwall;
    5. `_moment`: integrate the a.s. bound (`lintegral_mono_ae`, `ofReal_integral_eq_lintegral_ofReal`).
  Size: M-L (step 3 and the smooth kernels `g_ε` with uniform bounds are the bulk).

* `lowtemp_coulomb_threshold` (C3): statement as `lowtemp_coulomb_bound`; its proof is "`lowtemp_coulomb_bound` + `o_N ≥ c N^{-2/d}`",
  and `lowtemp_coulomb_bound` (Prop 3.37, Itô with stopped smooth kernels) has no proof in the repository: BLOCKED on 3.37.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {d N : ℕ}

/-- Push-forward bookkeeping: `∫⁻ ofReal (f (Z ω) + o) dP = ofReal (∫ f d(P.map Z) + o)` for an integrable `f` under
`P.map Z` with `f (Z ω) + o ≥ 0` a.s. -/
theorem g336_lintegral_map {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → Config d N) (hZ : AEMeasurable Z P) (f : Config d N → ℝ) (o : ℝ)
    (hf : Integrable f (P.map Z)) (hnn : ∀ᵐ ω ∂P, 0 ≤ f (Z ω) + o) :
    ∫⁻ ω, ENNReal.ofReal (f (Z ω) + o) ∂P = ENNReal.ofReal (∫ x, f x ∂(P.map Z) + o) := by
  have h1 : Integrable (fun ω => f (Z ω)) P :=
    (integrable_map_measure hf.aestronglyMeasurable hZ).1 hf
  have h2 : Integrable (fun ω => f (Z ω) + o) P := h1.add (integrable_const o)
  rw [← ofReal_integral_eq_lintegral_ofReal h2 hnn, integral_add h1 (integrable_const o),
    integral_const, integral_map hZ hf.aestronglyMeasurable]
  simp

/-- `∫ (f (Z ω) + o) dP = ∫ f d(P.map Z) + o`. -/
theorem g336_integral_map {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → Config d N) (hZ : AEMeasurable Z P) (f : Config d N → ℝ) (o : ℝ)
    (hf : Integrable f (P.map Z)) :
    ∫ ω, (f (Z ω) + o) ∂P = ∫ x, f x ∂(P.map Z) + o := by
  have h1 : Integrable (fun ω => f (Z ω)) P :=
    (integrable_map_measure hf.aestronglyMeasurable hZ).1 hf
  rw [integral_add h1 (integrable_const o), integral_const, integral_map hZ hf.aestronglyMeasurable]
  simp

end HRS
