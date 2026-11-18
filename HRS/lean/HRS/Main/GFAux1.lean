import HRS.Dynamics.Setup
import HRS.Stochastic.DualityProof
import HRS.Energy.Commutator.Assembly
import HRS.Uniform.Q45Smooth
import HRS.Uniform.Q45Max
import HRS.Uniform.TransportCoupling
import HRS.Uniform.RelativeCoupling
import HRS.Uniform.Q54cAux59

/-!
# Packet GF-ASM, part 1: the TeX-to-Lean chain plan for Theorem 2.1 (`M:H:thm:general`)

STATUS (2026-10-16).  Work STOPPED at the statement check, as instructed, because of the statement defect
**D1** below.  No declaration of this file is proved; the file only records the plan, the defect and the
inventory of the available inputs (the `#check`s at the end verify that every named input exists with the
quoted name).

Targets (frozen, sorried, `HRS/Dynamics/Setup.lean`): `HRS.GeneralSetup.general_fluctuation`,
`general_fluctuation_transport`, `general_fluctuation_matrix`.  Final names (planned, namespace `HRS.GF`,
file `HRS/Main/GFFinal.lean`): `general_fluctuation_proof` etc., each followed by
`example := (@general_fluctuation_proof : type_of% @HRS.GeneralSetup.general_fluctuation)`.

## 0. Statement check against the TeX (M L538-620)

Checked and faithful: `γ > 2d+10` (`hγ`), regularity order `γ+2d+12` (`MFHyp`, `IsRegularMF`), `sup β_N⁻¹ < ∞`
(`invβ_bdd`, `Within`), `inf ρ > 0` assumed only in the gradient assertions (TeX L541: "In the first, gradient,
assertion assume also inf ρ > 0"; the matrix clause has no `PosDensityWith`, correct), scales `σ_N, A_N, q_N`
(`sigmaScale`, `Ascale`, `qScale`, with the `β = ∞` convention), `ε_{N,p}` (`initialError`), independence of
`(X₀, η°)` from the noise, the three estimates (d₂ with `N^{-2/d}`, W₁/W₂ with `√q (𝔈^{1/4}+N^{-1/d})`), the
transport minimum with exponent `1/max{2,d-s}` (= `a_{d,s}` of L2461), the `E_{γ+2}` setting of the matrix
clause with initial errors in `E_γ`.  `Ω : Type` matches `smooth_path_comparison`/`maximal_estimate_meas`
(`Type`), so no universe obstruction arises (the enlargements stay in `Type`).

**D1 (statement defect, STOP).**  `GeneralSetup.C₀` is only constrained by `energy_nonneg`
(`0 ≤ F_N + o_N(C₀)`), i.e. by *nonnegativity* of the completion.  The TeX does NOT mean that: the proof of
Lemma 3.22 (L2279-2299, `U:lem:filtered`) says "These are exactly the costs included in the fixed
heat-kernel completion.  Increasing its constant once suffices; an arbitrary smaller nonnegative completion is
not being substituted", and L546-555 says the constant `C₀` "includes the uniform density-bound factors".  The
proved Lean inputs have exactly this shape: `filtered_coercivity`, `energy_W2` are
`∃ C₀min, ∀ C₀ ≥ C₀min, …` (constant `C₀min = C₀min(d,s,Λ[,m₀])`), and `commutator_estimate` bounds the
commutator by `C K (F_N + oNΛ d s C₀* Λ N)` with its own `C₀*(d,s)`.  For a setup whose `C₀` satisfies
`energy_nonneg` but `oN d s C₀ N < oNΛ d s C₀* Λ N` (or `C₀ < C₀min`) none of these inputs applies, and the
remainder estimate `E‖R_N‖ ≤ C σ_N ∫𝓔_N` of `U:eq:quantitative-drift` acquires an additive error
`C σ_N T (C₀*Λ^{s/d} - C₀)₊ N^{s/d-1}` which is not dominated by any term of the right-hand sides (e.g. it
survives for `q_N = 0`, `ε = 0`, `𝔈 → 0`).  Hence `general_fluctuation`, `_transport`, `_matrix` as stated are
at best unprovable from the inputs, and plausibly false for `C₀` just above the nonnegativity threshold.
Recommended repair (statement-level, to be done by the orchestrator; I do not edit statements): put the
threshold before the setup, i.e. `∀ b, ∃ C₀min C, 0 < C ∧ ∀ S, S.Within b → C₀min ≤ S.C₀ → …` (keeping
`energy_nonneg` as a hypothesis, or deriving it from `C₀min ≤ C₀` via `energy_add_oN_nonneg`, Coerc0.lean).
Everything below is independent of this choice except the final bookkeeping of step (4).

## 1. The chain (TeX step → Lean name / precisely stated missing helper)

Notation: `H = E_γ = NegSobolev d γ` (matrix clause: `E = E_{γ+2}`), `V(t,u)` the dual evolution
`⟨V(t,u)z, φ⟩ = ⟨z, U^{u,t}φ⟩`, `Ξ = σ_N(μ_N-μ)`, `M` the `E_γ`-valued particle martingale of covariance
`C_N^t = covForm γ q_N (empirical X_t)`, `C̄_N^t = covForm γ q_N ρ_N^t`.

(1) **Mild identity as a field path** `Ξ^t = V(t,0)Ξ^0 + Z^t + R^t` (U:eq:quantitative-mild, TeX L2447-2451).
    * scalar identity for every test and `τ ≤ t`: `HRS.duality_identity_all` (Stochastic/DualityProof.lean).
    * (small, routine) `duality_identity_all` takes `IsContactStrongSolution` and
      `hocc : D.M = 0 ∨ NullContactOccupation P T X`: from `IsStrongSolution` use
      `IsStrongSolution.toContact` and `no_collision` (a.s. collision-free on `[0,T]` ⟹ the contact set has
      measure `0`); `hρ : IsMeanFieldSolution`, `hreg : IsRegularMF 3 Λ T ρ` from `MFHyp` by monotonicity of `C^k`;
      `IsClassicalAdjointSolution` for `f = propagator …` from `adjoint_torus_classical` (regimes R1/R2b).
    * MISSING helper GF-PM (particle martingale): `M : ℝ → Ω → E_γ`, with
      `IsHilbertMartingaleWithCovariation P ℱ T M (fun r ω => covForm γ q (empirical (X r ω)))`
      (no construction of this object exists in the repository: Lemmas 3.24/3.31 *assume* it; build it as
      `IsHilbertItoIntegral` over `κ = Fin N × Fin d` with integrand `σ√(2β⁻¹)/N · bVec γ j (X_r i)`,
      `hsCovForm = covForm γ q (empirical X_r)`, `q = σ²β⁻¹/N`).
    * MISSING helper GF-PAIR (pairing identification, stochastic Fubini): for `f_r = U^{r,t}φ`
      (`C¹([0,t]; H^γ)` for `φ ∈ H^{γ+2}`) and `Z_t = IsStochConv … M`: a.s.
      `⟨Z_t,φ⟩ = ⟨M_t,f_t⟩ - ∫_0^t⟨M_r,∂_r f_r⟩ dr = empiricalMartingale … t` (Abel summation of the
      Riemann sums of `IsStochConv`: Q54cAux5 `Itô sums` is the deterministic half; the Itô-integral half
      `∫⟨dM_r,f_r⟩ = ⟨M_t,f_t⟩-∫⟨M_r,f'_r⟩dr` for deterministic `C¹` `f` is new).
    * MISSING helper GF-CONT: a.s. continuity and measurability of `t ↦ σ ofMeasureDiff γ (emp X_t)(ρ_t)` in
      `E_γ` (needed so that `flucPath` is not the junk path `0`): continuity of `x ↦ δ_x ∈ E_γ`
      (`γ > d/2`), norm-continuity of `t ↦ ρ_t ∈ E_γ` from weak continuity (`IsMeanFieldSolution`) plus the
      uniform `C^{γ+2d+12}` bounds (Arzelà–Ascoli).
    * MISSING helper GF-INIT: `η°` is only independent of the noise, it need not be `ℱ_0`-measurable for the
      given Brownian filtration `ℱ` (the hypothesis is `∃ ℱ`).  `smooth_path_comparison_proof` needs
      `X₀' = A η°` `ℱ_0`-measurable.  Route: enlarge `Ω × E_γ` with the regular conditional law of `η°` given
      `X₀` (`ProbabilityTheory.condDistrib`; `E_γ` and `Config d N` are standard Borel), `ℱ'_t = ℱ_t ⊗ σ(η')`;
      `W` stays Brownian (conditional independence given `X₀ ∈ ℱ_0`); `ε_{N,p}`, `law Y_N`, `law Ξ_N` depend on
      the law of `(X₀,η°)` only.
(2) **Remainder** `‖R_N‖_{C_t H^{-γ}} ≤ C σ_N ∫_0^T 𝓔_N^t dt` (U:eq:quantitative-drift, L2452-2455).
    `R^t(φ) = σ ∫_0^t flucInteraction(U^{r,t}φ)dr`; pathwise bound by
    `HRS.Commutator.commutator_estimate_of_packets` (Prop 3.32; `type_of%` tie with `HRS.commutator_estimate`)
    applied with `v = ∇U^{r,t}φ` (`HasTransportBound d s v K`, `K ≲ ‖U^{r,t}φ‖_{H^{γ}}`: Sobolev embedding
    `H^γ ⊂ C^{2}` plus the fractional `L^{2d/(d-1)}` term for `s < d-2`), uniformly in `φ` in the unit ball of `H^γ`
    (propagator bound `‖U^{r,t}‖_{γ→γ} ≤ K`); then Minkowski/Fubini for `E`.  MISSING helper GF-REM
    (includes the identification of `flucInteraction` with `Comm_N` and the `C₀` bookkeeping, see D1).
(3) **Evolution with `MaxHyp`** (both for `Z` and `Z̄`).  THE CRUX.  No `EvolData` instance exists anywhere in the
    repository (all of Q45, Q48e, Q54 work with the lighter `IsPlainEvolution + quasi-contractive` interface;
    `Q54.evolution_estimates_proof` is at fixed `β > 0` through `propagator_quasi/prop_hold`, which need
    `ν₀ > 0` (regime R3), so it is NOT an input for the varying `β_N ∈ [0,B_β]` of Theorem 2.1; it is not used).
    * gradient clause (path space `E_γ`, one level): `EvolData.Dissipative` on `E_γ` is forced
      (`H_- = H`, TeX L2034-2037 + `U:lem:gradient-energy`): core `D = E_{γ-2}`, `A_r = forward linearisation`
      (`forwardLinCoeff`), quasi-dissipativity `2⟨z,A_r z⟩ ≤ K‖z‖²` from `HRS.Uniform.gradient_energy`
      (Q13; proved, uniform in `ν ∈ [0,ν_max]`; `Spec.lean` L735), `‖V‖ ≤ e^{K(t-u)/2}` from
      `adjoint_torus` in regimes R1 (`s ≤ d-2`) / R2b (`ρ ≥ c`, which is `PosDensityWith`), both uniform in `β`,
      strong continuity of `V` on `E_γ` (`IsEvolution.cont_H/cont_E`), the forward equation
      `∂_t V(t,u)x = A_t V(t,u)x` on the invariant core, and the Galerkin conjunct (finite-rank `P_n`,
      Galerkin evolutions `V_n → V`: energy/Grönwall for `e = P_nV x - u_n`, using `A: E_{γ-2} → E_γ`).
      MISSING helper GF-EV-GRAD.
    * matrix clause (`H = E_γ`, `E = E_{γ+2}`, `TwoLevel`): from `AdjointInput M K` (it is exactly the bounds of
      `TwoLevel`), still needs `IsEvolution` (cocycle from `classical_adjoint_unique`, strong continuity on `E_γ`
      — NOT implied by the bounds alone: needs `𝓛_r^* e_k ∈ E_γ` from the explicit structure of `forwardGen`
      with smooth coefficients — and the derivative identity in `E_{γ+2}`).  MISSING helper GF-EV-MAT.
(4) **Covariance error** (U:eq:trace-error with `L = 1`): MISSING helper GF-TE:
    `‖covForm γ q (emp X) - covForm γ q ρ‖_{𝔖₁} ≤ C q (𝓔^{1/2} + N^{-2/d})` pointwise, by trace duality with
    `φ_A(x) = Σ_j ⟨A b_{x,j}, b_{x,j}⟩` (uniform `Ḣ^{q/2}` and `Δφ_A` bounds in `‖A‖ ≤ 1`, `γ > max{d+4, …}`),
    input `HRS.Uniform.Q12.filtered_coercivity_proof` (`L = 1`), then Jensen for `E ∫`.  (Q14Aux6/7, Q48cCov have
    the Lipschitz/Fourier-feature analogues for `bures2`; the trace-norm version is new.)
(5) **Smooth metric**: `HRS.Uniform.smooth_path_comparison_proof` (Q45Smooth; the frozen `smooth_path_comparison`
    must not be named) with `S = (3)`, `X₀ = Ξ^0`, `X₀' = Aη°`, `Cb = covForm γ q ρ_N` (`IsDetCovDensity`:
    measurability in `r` via `Q54c.covDens_continuousOn` and `Q54c.weak_continuity`), `G` the Gaussian martingale
    (`Q45.exists_gaussian_martingale`), `R` from (2).  Gives `d₂ ≤ C E‖X₀-X₀'‖ + E‖R‖ + C E∫‖Sg-Cb‖₁`; with
    (4) and the law identification (6) this is the first estimate.
(6) **Law identification** `law P (toPath γ T Y_N) = law (windowPath 0 T (V Aη° + conv G))`
    (`IsLinearFluctuationSolution` ⟹ finite-dimensional Gaussian laws; `Q54c.toPath_law_eq`,
    `Q54c.noise_gaussian`, `Q54c.PdeSetup.Data.fdd_eq` are the analogues at level `n+4`); at level `γ` it needs
    GF-PAIR for the Gaussian side (Wiener integral of `U^{r,t}φ` against `G`).  MISSING helper GF-LAW.
(7) **Wasserstein** (L2457-2459): single adapted coupling of the entire martingales.  Inputs:
    `HRS.Uniform.polar_coupling_cost` (3.19; proved in place in Spec.lean, via `hilbert_polar_coupling`) or
    `relative_covariance_coupling_proof` (3.29; cost `𝔟(Sg,Db)²`), `HRS.Uniform.Q45.maximal_estimate_meas`
    (3.17 with measurable version; for `M∘π - Ḡ`, with `Sd` trace `≤ ‖Sg-Cb‖₁`), linearity/uniqueness of
    `IsStochConv`, transport of `IsStochConv` along the measure-preserving `π`.  `W_p ≤ (E sup‖X'-X̄'‖^p)^{1/p}`
    for the coupling `(X', X̄')` on the enlargement.  MISSING helper GF-WP (abstract: the single-window,
    `EvolData`-based version of the sorried `comparison_wasserstein`, p = 1, 2).
(8) **Transport variant** (L2459-2465): `HRS.Uniform.transport_noise_coupling_proof` (3.24; trace density
    `≤ C q_N W₂(μ_N,μ)²`) + `HRS.Uniform.Q12.energy_W2_proof` (3.23; `W₂(μ_N,μ) ≤ C(N^{-1/d} + 𝓔^{1/max(2,d-s)})`,
    needs `ρ ≥ c`, C₀ ≥ C₀min: D1 again) + `maximal_estimate_meas`; `2a_{d,s} ≤ 1` and Jensen give
    `E∫W₂² ≤ C(𝔈^{2a}+N^{-2/d})` (U:eq:transport-moment); take the minimum of the two couplings.
    MISSING helper GF-TR (assembly, after GF-WP).
(9) **Gradient energy / no path loss** (`U:lem:gradient-energy`): `HRS.Uniform.gradient_energy` (proved), feeds (3).

## 2. Inventory notes (verified by grep in this worktree)

* Oleans missing from the shared build for the closure of `Q12Final` (27 files `Q12W*/Q12P*`) and of
  `Q54Aux24` (13 files `Q54Aux1,15-24`): they are needed only for (8) resp. not at all; compile them when (8)
  is reached (`missing_order.py` lists them).
* `PathSpace d γ T` (`Torus/Sobolev.lean`) and `Uniform.PathSp T (NegSobolev d γ)` are two separate `def`s of
  `C(Set.Icc 0 T, NegSobolev d γ)` with `inferInstanceAs` instances; `smooth_path_comparison_proof` produces
  laws on `windowPath 0 T`/`PathSp`, the theorem is stated on `PathSpace` (`toPath`/`flucPath`): a transport
  lemma (identity on the underlying type) is needed; `Q54c` already handles the same translation for
  `coefficient_comparison_proof`.
* Do not name the sorried frozen statements (`maximal_estimate`, `smooth_path_comparison`, `energy_W2`,
  `transport_noise_coupling`, `comparison_smooth`, `comparison_wasserstein`, `relative_covariance_cost`,
  `relative_covariance_coupling`, `covariance_measure`); use the `_proof` variants.
-/

noncomputable section

namespace HRS.GF

-- name checks of the inputs (all proved)
#check @HRS.duality_identity_all
#check @HRS.Commutator.commutator_estimate_of_packets
#check @HRS.Uniform.smooth_path_comparison_proof
#check @HRS.Uniform.Q45.maximal_estimate_meas
#check @HRS.Uniform.transport_noise_coupling_proof
#check @HRS.Uniform.relative_covariance_coupling_proof
#check @HRS.Uniform.polar_coupling_cost
#check @HRS.Uniform.gradient_energy
#check @HRS.Uniform.coefficient_comparison_proof

end HRS.GF
