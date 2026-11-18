import HRS.MP.SelfSimSpec

/-!
# MP-SSP4PLAN: decomposition of packet P4 `ss_P4_entropy_free` (statement-only interface + proved assembly)

Target: `HRS.MP.SelfSim.ss_P4_entropy_free` (`HRS/MP/SelfSimSpec.lean:282`), the self-similar entropy inequality
`𝓗_{Ḡ^τ}(f^τ) + β⁻¹∫_0^τ 𝓘_{Ḡ^r}(f^r) dr ≤ 𝓗_{Ḡ^0}(f^0)` for a collision-free solution `Y` of the self-similar
equation `dY = -∇Ū^τ(Y) dτ + √(2θ) dW̄` (`θ = invβ`, `Ū^τ = a_s(τ)/(2N)∑_{i≠j}g(ξ_i-ξ_j) + ¼|ξ|²`).  This file holds
the vocabulary (definitions, no `sorry`), ten interface lemmas (statement only, `sorry`) and the assembly
`ss_P4_entropy_free_proof`, **proved** from them and tied to the frozen statement by
`example := (@ss_P4_entropy_free_proof : type_of% @HRS.MP.SelfSim.ss_P4_entropy_free)`.

## Verdict

The statement is true; no interface lemma below is suspected false (each was checked on its degenerate cases:
`N ≤ 1`, `𝓗 = ⊤`, `⊥ + ⊤` in `EReal`, Bochner junk avoided by `lintegral`s).  Two representation points:
* `EucConfig d N = Fin N → Euc d` carries the **sup norm** and is not an inner-product space, so `gradient` is not
  available on it.  `∇V = -b` is written `HasFDerivAt (V τ) (-(p4InnerL (b τ x))) x`, the Gaussian uses the Euclidean
  square `∑_i ‖x_i‖²`, and Lipschitz constants/second moments are in the sup norm (equivalent; only constants move).
* The regularisation is done **in self-similar variables** with a kernel truncated at the fixed scale `1/(M+1)`
  (`p4Pot (gM M)`), as the spec docstring requires (truncating in original variables gives `∂_τŪ_ε` the wrong sign).

## Route (the P4 paragraph of the spec, made precise)

`gM` (1) → regularised strong solutions `Y^M` equal to `Y` on `[0,S]` for `M ≥ M(ω)`, hence `Law(Y^M_τ) → Law(Y_τ)`
setwise (3) → the laws `μ^M` satisfy the weak FP equation with non-compactly supported tests, second moments, narrow
continuity (4) → level-`M` inequality by the CepH2 route "mollify the law, not the equation": mollified dissipation
inequality (5), initial Jensen bound (6), lsc as the mollification is removed (7), `ε`/`δ` bookkeeping (8) →
`M → ∞`: lsc of `𝓗` and `𝓘` with moving reference (9), Fatou/`EReal` bookkeeping (10).  The initial term is
controlled by `𝓗_{Ḡ_M^0} ≤ 𝓗_{Ḡ^0}` (2), which also gives the initial second moment.

## Interface lemmas (size: S < 300, M 300-1000, L 1000-3000, XL > 3000 Lean lines)

Module status: `HRS/Appendix/*`, `HRS/Stochastic/*`, `HRS/Whole/*` are in the shared build; `HRS/MC/Cep*` and
`HRS/MP/*` are **not** (compile with `wcheck.sh` in dependency order if a definition must be imported; every CepH2
result below is used as a *template*, since CepH2 lives on `Ch N = EuclideanSpace ℝ (Fin N)` with a periodic,
time-independent potential and its statements do not apply verbatim).

**(1) `p4_kernel` — M (~700).**  Truncated kernels and the potential hypotheses.  `gM M x = Φ_s(√(q_M(‖x‖²)))` with
`Φ_s(r) = r^{-s}` (`s > 0`) or `-log r` (`s = 0`) and `q_M` smooth, nondecreasing, `q_M(t) ≥ t`, `q_M(t) = t` for
`t ≥ r₀²`, `q_M ≥ r₀²/4` (built from `Real.smoothTransition`, as `h2_rho`, `HRS/MC/CepH2Aux14.lean:21`).  Then `gM ≤ g`
off `0` (`Φ_s` decreasing), `gM = g` on `‖x‖ ≥ r₀`, evenness, `C²`, bounded Hessian ⇒ Lipschitz gradient (template
`h2_lipschitz_gradient`, `CepH2Freeze1.lean:44`), `gM ≥ 0` for `s > 0`, `gM ≥ -log(1+‖x‖)` (uses `r₀ ≤ 1`).  The
`P4PotHyp` part: `D p4Pot = -p4InnerL p4Drift` (evenness makes `∇gM` odd; pair-sum reindexing), joint continuity,
uniform Lipschitz (`a_s ≤ 1` on `τ ≥ 0`), `∂_τ p4Pot = -(s/2)a_s/(2N)∑gM ≤ 0`, quadratic growth of `|∂_τ p4Pot|`,
confinement `‖x‖²/8 - C ≤ p4Pot` (`log(1+r) ≤ εr² + C_ε`).  Uses: `q09_rkg_eq` (`Whole/AppendixAAdjoint.lean:619`,
shared), `ssp2_riesz_grad_smul` (`MP/SelfSimP2.lean:106`, not shared).  Dependencies: none.

**(2) `p4_gibbs` — M (~600).**  Gibbs references on `ℝ^{dN}`: `0 < Z < ∞` for `selfSimWeight` and for the regularised
weights (Gaussian majorant from `k ≥ -log(1+‖x‖)`; positivity: weight `> 0` off the Lebesgue-null collision set,
which needs `d ≥ 1`), replacing `b15_gibbsPartition_pos_lt_top` (`Appendix/B15Aux2.lean:220`, torus, shared);
monotonicity `𝓗_{G'} ≤ 𝓗_G` for `G ≤ G'` (both are `KL(μ | G dx)` without normalisation; the negative part of the
`llr` is integrable since `-log f ≤ 1/f - 1`); finite entropy ⇒ finite second moment (Gibbs inequality against
`e^{c‖x‖²}`, `c < β/8`).  Templates: `h2_partition_lt_top`/`h2_partition_pos` (`CepH2Mom2.lean:54,61`),
`cepH2_moment_init_proof` (`CepH2Mom3.lean:54`), `h2_entropy_mono` (`CepH2Mov2.lean:111`).  Dependencies: none.

**(3) `p4_regularised_flow` — M (~650).**  For each `M`, `exists_sde_solution_global_nonneg`
(`Stochastic/SDE.lean:1050`, shared; time-dependent globally Lipschitz drift `p4Drift (gM M)`, noise `√(2θ)e_k`,
initial value `Y 0`, which is `ℱ_t`-measurable for `t < 0` by `hY.filtered.progressive`, as in `ss_P3_fke_proof`,
`MP/SelfSimP3.lean:292`) gives `Y^M`; re-index by `ℝ≥0`, progressive by continuity + adaptedness.  Equality with `Y`:
for a.e. `ω` the continuous collision-free path has minimal pair distance `δ(ω) > 0` on `[0,S]`; for
`1/(M+1) < δ(ω)` the two drifts agree along `Y`, and deterministic uniqueness (`ode_additive_unique`,
`Stochastic/SDE.lean:127`, or `h2_path_eq`, `CepH2Loc1.lean:22`) gives `Y^M = Y` on `[0,S]` — exactly the template
`b15c_regularised_eq_strong_proof` (`Appendix/B15CAux3.lean:346`, shared), without the torus lift.  Setwise
convergence of the laws: dominated convergence of indicators.  Dependencies: (1) (kernel shape only).

**(4) `p4_flow_hyp` — M (~900).**  Laws of an additive-noise solution with continuous, uniformly Lipschitz drift:
(i) weak FP with tests `P4Test` (bounded, `‖∇g‖(1+‖x‖)` and `∇²g` bounded; Gaussians `G_v(x-·)` are such tests): the
Itô skeleton of `ss_P3_fke_proof` for `g(Y_r)` (`ito_formula_additive`, `Stochastic/Ito.lean:3632`;
`integral_itoIntegral`, `Stochastic/Integral.lean:1451`), the Itô drift `p4Gen` is bounded because `b` has linear
growth; (ii) `sup_{[0,S]} E‖Y_t‖² < ∞` by forced Gronwall (`h2_gronwall_forced`, `CepH2Sde4.lean:18`;
`cepH2_moment_flow_proof`, `CepH2Sde6.lean:19`); (iii) narrow continuity from path continuity (`cepH2_narrow_of_paths`,
`CepH2Sde3.lean:211`).  Dependencies: none.  **Shared with P5** (stated for any `d`, drift, `ν`).

**(5) `p4_mollified_ineq` — L (~3000; split below).**  The transplant of `cepH2_mollified_full`
(`CepH2Core1.lean:60`) and of the `H2Set` machinery (`CepH2Aux7`-`Aux31`): `u_r = G_v * μ_r`,
`F_r(u) = ∫ u log u + uV_r/θ`, `D_r(u) = ∫ u|∇log u + ∇V_r/θ|²`,
`F_t(u_t) + θ(1-δ)∫_0^t D_r(u_r) dr ≤ F_0(u_0) + t·Cv/δ`.  **What transplants:** the commutator
`r(x) = ∫G(x-y)(∇V(y)-∇V(x))dμ`, `∫|r|²/u ≤ K²nv` (`h2_C`, `h2_integral_C_le`, `CepH2Aux16.lean:120`), the Young step
(`h2_pointwise_diss`, `CepH2Aux15.lean:82`), the cut-off `χ_R(‖x‖)`-then-`R → ∞` argument (`h2_chi`, `H2Set.tendsto_Fchi`,
`H2Set.E_tail`, `H2Set.result2`, `CepH2Aux14,25,28,30`), the bounds `|log u| ≤ C(1+‖x‖²)` (`h2_mu_log_lower`,
`CepH2Aux10.lean:104`), the time derivative of `u` from the weak FP with the Gaussian test (`h2_mu_time`,
`CepH2Aux19.lean:93`), the clamping to `[0,T]` (`cepH2_clampSet`, `CepH2Core1.lean:19`).  **What changes:** (a) no
periodisation: `h2_per`/`tsum` over `ℤ`, the fundamental cell, `h2_lintegral_unfold`, `h2_isFD`, the tube/cell bounds
(`CepH2Aux2,3,5,6` periodisation part, ~1100 lines) disappear; integrals are over `ℝ^{dN}`, and the cut-off is radial
in the full variable instead of transverse (`‖P⊥x‖` ↦ `‖x‖`); (b) Pi-type coordinates (`configBasis`) instead of
`EuclideanSpace.single`; (c) **time dependence of the weight**: the FTC for `F_t(u_t)` acquires
`∫ u_t ∂_tV_t/θ ≤ 0` (sign from `P4PotHyp.dtime`; integrable by the quadratic bound on `∂_tV` and second moments),
which is dropped; (d) second moments come from `P4FlowHyp.mom` (from the quadratic confinement through (2)/(4)) instead
of the transverse moment.  Suggested split: (5a) mollifier calculus on `ℝ^{dN}` (`u` smooth, `> 0`, derivative and
log bounds, joint continuity in `(r,x)`, ~1000), (5b) `∂_t u` from the weak FP + pointwise FTC (~600),
(5c) cut-off free-energy computation, commutator, Young, `R → ∞` (~1400).  Dependencies: (4) (shape of `P4FlowHyp`).
**Shared with P5** (stated for any `d` and any `V` satisfying `P4PotHyp`, `V' = 0` allowed).

**(6) `p4_initial_jensen` — M (~450).**  `F_0(G_v * μ_0) ≤ 𝓗_{G_0}(μ_0) + e(v)`, `e(v) = O(v)`: Jensen for `s log s`
under the probability kernel `G_v` and the descent lemma `V(x+w) ≤ V(x) + ⟨∇V,w⟩ + K‖w‖²/2` (the linear term vanishes
by symmetry of `G_v`).  Templates: `cepH2_initial_bound` (`CepH2Init4.lean:23`), `h2_jensen_pointwise`,
`h2_entropy_term_le` (`CepH2Init1.lean:118,160`), `h2_U_term` (`CepH2Init2.lean:25`), `h2_U_quad` (`CepH2Aux13.lean:36`).
No periodic unfolding.  Dependencies: (2) (moment from entropy, same proof).  **Shared with P5.**

**(7) `p4_mollify_lsc` — M (~800).**  `v → 0`: `𝓗(μ) ≤ liminf F(G_v * μ)` and `𝓘(μ) ≤ liminf D(G_v * μ)`.  Entropy:
`𝓗(u dx) = F(u)` (`h2_klDiv_density`, `CepH2Ent2.lean:91`), Donsker-Varadhan lsc on a compact space
(`b15b_klDiv_liminf_le`, `Appendix/B15BAux1.lean:82`, shared, needs `CompactSpace`) **through the coordinatewise
embedding `ℝ^{dN} → [-1,1]^{dN}`** (`h2_sq`/`h2_isq`, `CepH2Comp1.lean:27,39`; the cylinder version
`h2_klDiv_liminf_cell`, `CepH2Comp1.lean:120`, also embeds the `S¹` factor, which is dropped), narrow convergence
`G_v * μ ⇀ μ` (`h2_molMeas_tendsto`, `CepH2Comp3.lean:66`, without periodicity).  Fisher: each `ζ`-functional is a
bounded continuous integrand, and for smooth positive `u` it is `≤ D(u)` by integration by parts against the compactly
supported `ζ` (`h2_fint_le_D1`, `CepH2Fish2.lean:38`; `cepH2_fisher_lsc`, `CepH2Fish3.lean:18`).  The compact-cube
embedding helper `p4_klDiv_liminf` is reused by (9).  Dependencies: (2).  **Shared with P5.**

**(8) `p4_level_bookkeeping` — S (~250).**  Pure `ℝ`/`EReal` bookkeeping: `D := liminf_n D_{v_n}` (AEMeasurable),
Fatou in `r`, `liminf` of the mollified inequality, `e(v_n) → 0`, then `δ → 0`.  Template: `cepH2_core'`
(`CepH2Core3.lean:23`), `h2_liminf_add_le`, `h2_delta_limit` (`CepH2Core2.lean:40,55`).  Dependencies: none.

**(9) `p4_lsc_M` — M (~700).**  `M → ∞` at fixed `τ`, moving reference: `𝓗_{Ḡ^τ}(μ) ≤ liminf 𝓗_{Ḡ_M^τ}(μ^M)` and
`𝓘_{Ḡ^τ}(μ) ≤ liminf 𝓘_{Ḡ_M^τ}(μ^M)` under setwise convergence `μ^M → μ`.  Entropy: `Z_M → Z` by dominated
convergence (Gaussian majorant uniform in `M` from `gM ≥ -log(1+‖x‖)`, pointwise eventual equality off the null
collision set), normalised references converge in total variation (Scheffé), `klDiv` lsc by `p4_klDiv_liminf` of (7)
(setwise convergence gives the convergence of every bounded continuous test); template `h2_entropy_lsc_moving`,
`h2_klDiv_liminf_moving`, `h2_ref_tendsto`, `h2_weight_lintegral_tendsto` (`CepH2Mov2.lean:23`, `CepH2Mov1.lean:107,63,24`).
Fisher: a test field `ζ` is supported in a compact `K ⊂ Ω_N` with minimal pair distance `δ_K > 0`; for
`1/(M+1) < δ_K/2` the two log-weights coincide near `K`, so the `ζ`-functionals have the same bounded integrand and
converge (template `h2_fisher_lsc_moving`, `CepH2Mov2.lean:75`).  Dependencies: (1), (2), (7) (helper).

**(10) `p4_limit_bookkeeping` — S (~250).**  Fatou in `r` for the majorants `D_M` (`lintegral_liminf_le'`),
`liminf` of the level inequalities in `EReal` (no `⊥ + ⊤` issue: the Fisher terms are `≥ 0`).  Templates:
`b15e_limit_core` (`Appendix/B15EAux5.lean:157`, shared), `b15e_step4_limit` (`Appendix/B15EAux8.lean:80`, shared),
`cepH2_freeze_limit` (`CepH2Mov3.lean:19`).  Dependencies: none.

**Total**: ≈ 700 + 600 + 650 + 900 + 3000 + 450 + 800 + 250 + 700 + 250 ≈ **8300 lines** (the spec's 4500 was too
low: CepH2's mollified-inequality machinery alone is ~4700 lines with periodisation, ~3000 without).

## Order of attack

(10), (8) (pure bookkeeping, S, remove `EReal` risk early) → (2) → (1) → (4) → (5a), (5b), (5c) (main risk:
integrability on the non-compact `ℝ^{dN}`, exactly the CepH2 risk; the radial cut-off replaces the transverse one) →
(7) (with the helper `p4_klDiv_liminf`) → (6) → (3) → (9).

## Sharing with P5 (Cépa-Lépingle on the line)

(4)-(8) are stated for an arbitrary `d`, potential `V` and drift `b` with `P4PotHyp` (time independence is the case
`V' = 0`), so the level dissipation inequality on `ℝ^N` with quadratic confinement needed by P5 (Yosida-regularised
chamber potential + `ξ²/4`) is the case `d = 1` of (4)+(5)+(6)+(7)+(8), provided the Yosida envelope satisfies
`P4PotHyp` (C¹ with Lipschitz gradient, confinement).  Caveat: the CepE/CepH5 chain works in chamber coordinates
`Ch N = EuclideanSpace ℝ (Fin N)`; P5 needs a transport along the linear isometry `EucConfig 1 N ≃ Ch N`
(measure-preserving), ~200 lines.  (2), (9), (10) are also reusable with `d = 1`, `s = 0` and the Yosida family in
place of `gM`.

## Points where the TeX is incomplete / compactness is used essentially

* TeX S L10969-10982 asserts the level-`ε` identity "at the smooth level" on `ℝ^{dN}` without any Fokker-Planck
  theory there; (5) replaces it by the mollified inequality (no FP existence/regularity), and the left side must
  carry the regularised weight (spec docstring).
* The torus proof uses compactness essentially in: the FP chain behind B.15 (Fourier on `𝕋^n`; replaced by (5));
  Donsker-Varadhan with `C(α, ℝ)` tests (`b15b_klDiv_eq_iSup`, `[CompactSpace α]`; replaced by the cube embedding
  in (7)/(9)); `0 < Z < ∞` (free on the torus; (2)); the bound on `V''` (replaced by the Lipschitz gradient of the
  truncated kernel plus the exact quadratic confinement).  Not essential: separation of a continuous collision-free
  path on the compact `[0,S]` (used in (3)).
* Nothing found false.  The only hypotheses of the interface lemmas that are not in `ss_P4_entropy_free` are
  produced by earlier interface lemmas.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.SelfSim HRS
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MP.SelfSimP4

variable {d : ℕ}

/-! ### Vocabulary -/

/-- The self-similar potential with an arbitrary pair kernel `k`:
`a_s(τ)/(2N) ∑_i ∑_{j≠i} k(ξ_i-ξ_j) + ¼ ∑_i ‖ξ_i‖²` (`selfSimPotential` is the case `k = g`). -/
def p4Pot (k : Euc d → ℝ) (s : ℝ) (N : ℕ) (τ : ℝ) (Ξ : EucConfig d N) : ℝ :=
  (aSelfSim s τ / (2 * N)) * ∑ i, ∑ j ∈ Finset.univ.erase i, k (Ξ i - Ξ j) +
    (1 / 4) * ∑ i, ‖Ξ i‖ ^ 2

/-- The self-similar drift with an arbitrary pair kernel `k` (`ssDrift` is the case `k = g`). -/
def p4Drift (k : Euc d → ℝ) (s : ℝ) (N : ℕ) (τ : ℝ) (Ξ : EucConfig d N) : EucConfig d N :=
  fun i => -((aSelfSim s τ / N) • ∑ j ∈ Finset.univ.erase i, gradient k (Ξ i - Ξ j) + (1 / 2 : ℝ) • Ξ i)

theorem p4Pot_riesz (s : ℝ) (N : ℕ) : p4Pot (rieszKernel d s) s N = selfSimPotential d s N := rfl

theorem p4Drift_riesz (s : ℝ) (N : ℕ) : p4Drift (rieszKernel d s) s N = ssDrift d s N := rfl

/-- The Gibbs weight `e^{-V/θ}` of a potential (no collision indicator). -/
def p4GibbsOf {N : ℕ} (θ : ℝ) (V : EucConfig d N → ℝ) (x : EucConfig d N) : ℝ :=
  Real.exp (-(θ⁻¹) * V x)

/-- The linear form `v ↦ ∑_i ⟨y_i, v_i⟩` (the Euclidean pairing on `(ℝ^d)^N`, whose norm is the sup norm). -/
def p4InnerL {N : ℕ} (y : EucConfig d N) : EucConfig d N →L[ℝ] ℝ :=
  ∑ i : Fin N, (innerSL ℝ (y i)).comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) i)

/-- A truncated kernel at scale `r₀ ∈ (0,1]`. -/
structure IsP4Kernel (d : ℕ) (s r₀ : ℝ) (k : Euc d → ℝ) : Prop where
  scale : 0 < r₀ ∧ r₀ ≤ 1
  smooth : ContDiff ℝ 2 k
  even : ∀ x, k (-x) = k x
  lipGrad : ∃ L : ℝ≥0, LipschitzWith L (gradient k)
  le_riesz : ∀ x, x ≠ 0 → k x ≤ rieszKernel d s x
  eq_far : ∀ x, r₀ ≤ ‖x‖ → k x = rieszKernel d s x
  lower : ∀ x, -Real.log (1 + ‖x‖) ≤ k x
  nonneg : 0 < s → ∀ x, 0 ≤ k x

/-- Hypotheses on a time-dependent potential `V` with `∇_x V = -b`, used on `[0,T]`. -/
structure P4PotHyp {N : ℕ} (V : ℝ → EucConfig d N → ℝ) (b : ℝ → EucConfig d N → EucConfig d N) (T : ℝ) :
    Prop where
  grad : ∀ τ x, HasFDerivAt (V τ) (-(p4InnerL (b τ x))) x
  cont_b : Continuous (Function.uncurry b)
  lip : ∃ K : ℝ≥0, ∀ τ ∈ Set.Icc (0 : ℝ) T, LipschitzWith K (b τ)
  cont_V : Continuous (Function.uncurry V)
  dtime : ∃ V' : ℝ → EucConfig d N → ℝ, Continuous (Function.uncurry V') ∧
    (∀ τ x, HasDerivAt (fun σ => V σ x) (V' τ x) τ) ∧
    (∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ x, V' τ x ≤ 0) ∧
    ∃ C : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ x, |V' τ x| ≤ C * (1 + ‖x‖ ^ 2)
  conf : ∃ c C : ℝ, 0 < c ∧ ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ x, c * ‖x‖ ^ 2 - C ≤ V τ x

/-- Test functions of the non-compact weak Fokker-Planck equation (the class `H2Test` of CepH2 without periodicity). -/
structure P4Test {N : ℕ} (g : EucConfig d N → ℝ) : Prop where
  smooth : ContDiff ℝ 2 g
  bdd : ∃ C : ℝ, ∀ x, |g x| ≤ C ∧ ‖fderiv ℝ g x‖ * (1 + ‖x‖) ≤ C ∧ ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ C

/-- The generator `θΔg + Dg[b(r,·)]` of `dY = b(r,Y)dr + √(2θ) dW`. -/
def p4Gen {N : ℕ} (θ : ℝ) (b : ℝ → EucConfig d N → EucConfig d N) (r : ℝ) (g : EucConfig d N → ℝ)
    (x : EucConfig d N) : ℝ :=
  θ * ∑ k : Fin N × Fin d, fderiv ℝ (fderiv ℝ g) x (configBasis d N k) (configBasis d N k) +
    fderiv ℝ g x (b r x)

/-- What the probabilistic side provides for the level-`M` analysis: probability laws, bounded second moments, narrow
continuity and the weak Fokker-Planck equation with `P4Test` tests, on `[0,T]`. -/
structure P4FlowHyp {N : ℕ} (θ : ℝ) (b : ℝ → EucConfig d N → EucConfig d N) (T : ℝ)
    (μ : ℝ → Measure (EucConfig d N)) : Prop where
  prob : ∀ t, IsProbabilityMeasure (μ t)
  mom : ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ t ∈ Set.Icc (0 : ℝ) T, ∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂(μ t) ≤ C
  narrow : ∀ g : EucConfig d N → ℝ, Continuous g → (∃ C : ℝ, ∀ x, |g x| ≤ C) →
    ContinuousOn (fun t => ∫ x, g x ∂(μ t)) (Set.Icc (0 : ℝ) T)
  fp : ∀ g : EucConfig d N → ℝ, P4Test g → ∀ t ∈ Set.Icc (0 : ℝ) T,
    ∫ x, g x ∂(μ t) = ∫ x, g x ∂(μ 0) + ∫ r in Set.Icc (0 : ℝ) t, ∫ x, p4Gen θ b r g x ∂(μ r)

/-- `SSAddSol` without the collision clauses (for the regularised solutions, which may meet the diagonal). -/
structure P4AddSol {Ω : Type*} [mΩ : MeasurableSpace Ω] {N : ℕ} (P : Measure Ω) (ν : ℝ)
    (b : ℝ → EucConfig d N → EucConfig d N) (S : ℝ) (ℱ : Filtration ℝ mΩ)
    (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (W : ℝ≥0 → Ω → (Fin N → Euc d))
    (Y : ℝ≥0 → Ω → EucConfig d N) : Prop where
  filtered : IsWholeFilteredSolution P ℱ W' W Y
  cont : ∀ ζ, Continuous fun t => Y t ζ
  eqn : ∀ᵐ ζ ∂P, ∀ t : ℝ≥0, (t : ℝ) ≤ S →
    (∀ i, IntegrableOn (fun r : ℝ => b r (Y (Real.toNNReal r) ζ) i) (Set.Icc 0 (t : ℝ))) ∧
    ∀ i, Y t ζ i = Y 0 ζ i + (∫ r in Set.Icc (0 : ℝ) t, b r (Y (Real.toNNReal r) ζ) i) +
      Real.sqrt (2 * ν) • (W t ζ i - W 0 ζ i)

/-- The centred Gaussian density on `(ℝ^d)^N` with variance `v` per coordinate. -/
def p4Gauss (d N : ℕ) (v : ℝ) (w : EucConfig d N) : ℝ :=
  (2 * Real.pi * v) ^ (-((N * d : ℕ) : ℝ) / 2) * Real.exp (-(∑ i, ‖w i‖ ^ 2) / (2 * v))

/-- The mollified density `u = G_v * μ`. -/
def p4Mol {N : ℕ} (v : ℝ) (μ : Measure (EucConfig d N)) (x : EucConfig d N) : ℝ :=
  ∫ y, p4Gauss d N v (x - y) ∂μ

/-- The free energy `∫ u log u + uV/θ` of a density. -/
def p4Free {N : ℕ} (θ : ℝ) (V : EucConfig d N → ℝ) (u : EucConfig d N → ℝ) : ℝ :=
  ∫ x, (u x * Real.log (u x) + u x * V x / θ)

/-- The dissipation `∫ u |∇log u + ∇V/θ|²` of a density, as a `lintegral`. -/
def p4Diss {N : ℕ} (θ : ℝ) (V : EucConfig d N → ℝ) (u : EucConfig d N → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (u x * ∑ k : Fin N × Fin d,
    ((u x)⁻¹ * fderiv ℝ u x (configBasis d N k) + θ⁻¹ * fderiv ℝ V x (configBasis d N k)) ^ 2)

/-! ### Interface lemmas (statement only) -/

/-- **(1) M.**  Truncated kernels at scale `1/(M+1)`, and the potential hypotheses for the regularised self-similar
potentials on every `[0,T]`. -/
theorem p4_kernel (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (N : ℕ) :
    ∃ gM : ℕ → Euc d → ℝ, ∀ M : ℕ, IsP4Kernel d s (1 / ((M : ℝ) + 1)) (gM M) ∧
      ∀ T : ℝ, 0 ≤ T → P4PotHyp (p4Pot (gM M) s N) (p4Drift (gM M) s N) T := by
  sorry

/-- **(2) M.**  Gibbs references on `ℝ^{dN}`: `0 < Z < ∞` for the self-similar and the regularised weights; the
regularised entropy is below the true one; finite entropy forces a finite second moment. -/
theorem p4_gibbs (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (N : ℕ) (invβ : ℝ) (hβ : 0 < invβ) (τ : ℝ)
    {r₀ : ℝ} {k : Euc d → ℝ} (hk : IsP4Kernel d s r₀ k) :
    (0 < gibbsPartitionW (selfSimWeight d s invβ N τ) ∧ gibbsPartitionW (selfSimWeight d s invβ N τ) < ⊤) ∧
    (0 < gibbsPartitionW (p4GibbsOf invβ (p4Pot k s N τ)) ∧
      gibbsPartitionW (p4GibbsOf invβ (p4Pot k s N τ)) < ⊤) ∧
    ∀ (μ : Measure (EucConfig d N)) [IsProbabilityMeasure μ],
      gibbsEntropyW (p4GibbsOf invβ (p4Pot k s N τ)) μ ≤ gibbsEntropyW (selfSimWeight d s invβ N τ) μ ∧
      (gibbsEntropyW (selfSimWeight d s invβ N τ) μ < ⊤ → ∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂μ < ⊤) := by
  sorry

/-- **(3) M.**  Regularised global strong solutions, equal to `Y` at time `0` and on `[0,S]` for `M ≥ M(ω)`; hence
setwise convergence of the laws on `[0,S]`. -/
theorem p4_regularised_flow (s : ℝ) {N : ℕ} (invβ : ℝ) (hβ : 0 < invβ) {S : ℝ} (hS : 0 < S)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {Y : ℝ≥0 → Ω → EucConfig d N}
    (hY : SSAddSol P invβ (ssDrift d s N) S ℱ W' W Y) (hnc : SSNoCollision P S Y)
    {gM : ℕ → Euc d → ℝ} (hgM : ∀ M : ℕ, IsP4Kernel d s (1 / ((M : ℝ) + 1)) (gM M)) :
    ∃ YM : ℕ → ℝ≥0 → Ω → EucConfig d N,
      (∀ M, P4AddSol P invβ (p4Drift (gM M) s N) S ℱ W' W (YM M)) ∧
      (∀ M ζ, YM M 0 ζ = Y 0 ζ) ∧
      ∀ τ ∈ Set.Icc (0 : ℝ) S, ∀ A : Set (EucConfig d N), MeasurableSet A →
        Tendsto (fun M => law P (YM M (Real.toNNReal τ)) A) atTop
          (𝓝 (law P (Y (Real.toNNReal τ)) A)) := by
  sorry

/-- **(4) M.**  The laws of an additive-noise solution with continuous, uniformly Lipschitz drift and square-integrable
initial value satisfy `P4FlowHyp` (weak FP with non-compact tests, moments, narrow continuity).  Shared with P5. -/
theorem p4_flow_hyp {N : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {ν : ℝ} (hν : 0 ≤ ν) {S : ℝ} (hS : 0 < S) {b : ℝ → EucConfig d N → EucConfig d N}
    (hbc : Continuous (Function.uncurry b)) (hbl : ∃ K : ℝ≥0, ∀ τ ∈ Set.Icc (0 : ℝ) S, LipschitzWith K (b τ))
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {Y : ℝ≥0 → Ω → EucConfig d N} (hY : P4AddSol P ν b S ℱ W' W Y)
    (hm0 : ∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂(law P (Y 0)) < ⊤) :
    P4FlowHyp ν b S (fun r => law P (Y (Real.toNNReal r))) := by
  sorry

/-- **(5) L.**  Mollified dissipation inequality on `ℝ^{dN}` with a time-dependent potential (CepH2 route, no
periodisation, extra term `∫u∂_tV/θ ≤ 0` dropped).  Shared with P5. -/
theorem p4_mollified_ineq {N : ℕ} {θ : ℝ} (hθ : 0 < θ) {V : ℝ → EucConfig d N → ℝ}
    {b : ℝ → EucConfig d N → EucConfig d N} {T : ℝ} (hT : 0 ≤ T) (hV : P4PotHyp V b T)
    {μ : ℝ → Measure (EucConfig d N)} (hμ : P4FlowHyp θ b T μ) :
    ∃ C : ℝ, ∀ v : ℝ, 0 < v →
      AEMeasurable (fun r => p4Diss θ (V r) (p4Mol v (μ r))) (volume.restrict (Set.Icc (0 : ℝ) T)) ∧
      ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ t ∈ Set.Icc (0 : ℝ) T,
        ∫⁻ r in Set.Icc (0 : ℝ) t, p4Diss θ (V r) (p4Mol v (μ r)) ≠ ⊤ ∧
        p4Free θ (V t) (p4Mol v (μ t)) +
            θ * (1 - δ) * (∫⁻ r in Set.Icc (0 : ℝ) t, p4Diss θ (V r) (p4Mol v (μ r))).toReal ≤
          p4Free θ (V 0) (p4Mol v (μ 0)) + t * (C * v / δ) := by
  sorry

/-- **(6) M.**  Initial Jensen bound `F(G_v * μ₀) ≤ 𝓗(μ₀) + e(v)`, `e(v) → 0`.  Shared with P5. -/
theorem p4_initial_jensen {N : ℕ} {θ : ℝ} (hθ : 0 < θ) {V : ℝ → EucConfig d N → ℝ}
    {b : ℝ → EucConfig d N → EucConfig d N} {T : ℝ} (hT : 0 ≤ T) (hV : P4PotHyp V b T)
    {μ₀ : Measure (EucConfig d N)} [IsProbabilityMeasure μ₀]
    (hfin : gibbsEntropyW (p4GibbsOf θ (V 0)) μ₀ < ⊤) :
    ∃ e : ℝ → ℝ, Tendsto e (𝓝[>] 0) (𝓝 0) ∧ ∀ v : ℝ, 0 < v →
      ((p4Free θ (V 0) (p4Mol v μ₀) : ℝ) : EReal) ≤ gibbsEntropyW (p4GibbsOf θ (V 0)) μ₀ + ((e v : ℝ) : EReal) := by
  sorry

/-- **(7) M.**  Removing the mollification: lower semicontinuity of the entropy and of the Fisher information
(non-compact Donsker-Varadhan through the cube embedding; integration by parts for the `ζ`-functionals).
Shared with P5. -/
theorem p4_mollify_lsc {N : ℕ} {θ : ℝ} (hθ : 0 < θ) {V : ℝ → EucConfig d N → ℝ}
    {b : ℝ → EucConfig d N → EucConfig d N} {T : ℝ} (hT : 0 ≤ T) (hV : P4PotHyp V b T)
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) T) {μ : Measure (EucConfig d N)} [IsProbabilityMeasure μ]
    (hmom : ∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂μ < ⊤) {v : ℕ → ℝ} (hv : ∀ n, 0 < v n)
    (hv0 : Tendsto v atTop (𝓝 0)) :
    gibbsEntropyW (p4GibbsOf θ (V τ)) μ ≤
        liminf (fun n => ((p4Free θ (V τ) (p4Mol (v n) μ) : ℝ) : EReal)) atTop ∧
      fisherInfoW (p4GibbsOf θ (V τ)) μ ≤ liminf (fun n => p4Diss θ (V τ) (p4Mol (v n) μ)) atTop := by
  sorry

/-- **(8) S.**  `ε → 0`, Fatou, `δ → 0`: the level dissipation inequality with a measurable majorant of the Fisher
information, from the conclusions of (5), (6), (7).  Pure bookkeeping. -/
theorem p4_level_bookkeeping {θ T C : ℝ} (hθ : 0 < θ)
    {F : ℝ → ℝ → ℝ} {Dv : ℝ → ℝ → ℝ≥0∞} {H : ℝ → EReal} {I : ℝ → ℝ≥0∞} {e : ℝ → ℝ}
    (hDm : ∀ v : ℝ, 0 < v → AEMeasurable (Dv v) (volume.restrict (Set.Icc (0 : ℝ) T)))
    (hmol : ∀ v : ℝ, 0 < v → ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∫⁻ r in Set.Icc (0 : ℝ) t, Dv v r ≠ ⊤ ∧
      F v t + θ * (1 - δ) * (∫⁻ r in Set.Icc (0 : ℝ) t, Dv v r).toReal ≤ F v 0 + t * (C * v / δ))
    (he : Tendsto e (𝓝[>] 0) (𝓝 0))
    (hinit : ∀ v : ℝ, 0 < v → ((F v 0 : ℝ) : EReal) ≤ H 0 + ((e v : ℝ) : EReal))
    (hlscH : ∀ t ∈ Set.Icc (0 : ℝ) T,
      H t ≤ liminf (fun n : ℕ => ((F (1 / ((n : ℝ) + 1)) t : ℝ) : EReal)) atTop)
    (hlscI : ∀ r ∈ Set.Icc (0 : ℝ) T, I r ≤ liminf (fun n : ℕ => Dv (1 / ((n : ℝ) + 1)) r) atTop) :
    ∃ D : ℝ → ℝ≥0∞, AEMeasurable D (volume.restrict (Set.Icc (0 : ℝ) T)) ∧
      (∀ r ∈ Set.Icc (0 : ℝ) T, I r ≤ D r) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) T,
        H t + ((ENNReal.ofReal θ * ∫⁻ r in Set.Icc (0 : ℝ) t, D r : ℝ≥0∞) : EReal) ≤ H 0 := by
  sorry

/-- **(9) M.**  `M → ∞` at a fixed time: lower semicontinuity of the entropy and of the Fisher information with the
moving references `Ḡ_M^τ → Ḡ^τ`, under setwise convergence of the laws. -/
theorem p4_lsc_M (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (N : ℕ) (invβ : ℝ) (hβ : 0 < invβ) (τ : ℝ)
    {gM : ℕ → Euc d → ℝ} (hgM : ∀ M : ℕ, IsP4Kernel d s (1 / ((M : ℝ) + 1)) (gM M))
    {μ : Measure (EucConfig d N)} {μM : ℕ → Measure (EucConfig d N)}
    [IsProbabilityMeasure μ] [∀ M, IsProbabilityMeasure (μM M)]
    (htv : ∀ A : Set (EucConfig d N), MeasurableSet A → Tendsto (fun M => μM M A) atTop (𝓝 (μ A))) :
    gibbsEntropyW (selfSimWeight d s invβ N τ) μ ≤
        liminf (fun M => gibbsEntropyW (p4GibbsOf invβ (p4Pot (gM M) s N τ)) (μM M)) atTop ∧
      fisherInfoW (selfSimWeight d s invβ N τ) μ ≤
        liminf (fun M => fisherInfoW (p4GibbsOf invβ (p4Pot (gM M) s N τ)) (μM M)) atTop := by
  sorry

/-- **(10) S.**  `M → ∞`: Fatou for the majorants and `liminf` of the level inequalities in `EReal`. -/
theorem p4_limit_bookkeeping {θ S : ℝ} {H : ℝ → EReal} {HM : ℕ → ℝ → EReal} {I : ℝ → ℝ≥0∞}
    {D : ℕ → ℝ → ℝ≥0∞} {R : EReal}
    (hDm : ∀ M, AEMeasurable (D M) (volume.restrict (Set.Icc (0 : ℝ) S)))
    (hlscH : ∀ τ ∈ Set.Icc (0 : ℝ) S, H τ ≤ liminf (fun M => HM M τ) atTop)
    (hlscI : ∀ r ∈ Set.Icc (0 : ℝ) S, I r ≤ liminf (fun M => D M r) atTop)
    (hlev : ∀ M, ∀ τ ∈ Set.Icc (0 : ℝ) S,
      HM M τ + ((ENNReal.ofReal θ * ∫⁻ r in Set.Icc (0 : ℝ) τ, D M r : ℝ≥0∞) : EReal) ≤ R) :
    ∀ τ ∈ Set.Icc (0 : ℝ) S,
      H τ + ((ENNReal.ofReal θ * ∫⁻ r in Set.Icc (0 : ℝ) τ, I r : ℝ≥0∞) : EReal) ≤ R := by
  sorry

/-! ### The assembly (proved from the interface lemmas) -/

/-- **P4**, assembled from (1)-(10) (statement verbatim from `HRS.MP.SelfSim.ss_P4_entropy_free`). -/
theorem ss_P4_entropy_free_proof (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (N : ℕ)
    (hN : 2 ≤ N) (invβ : ℝ) (hβ : 0 < invβ) (S : ℝ) (hS : 0 < S)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {Y : ℝ≥0 → Ω → EucConfig d N}
    (hY : SSAddSol P invβ (ssDrift d s N) S ℱ W' W Y) (hnc : SSNoCollision P S Y)
    (hH0 : gibbsEntropyW (selfSimWeight d s invβ N 0) (law P (Y 0)) < ⊤) :
    SSEntropyIneq d s invβ N S P Y := by
  obtain ⟨gM, hgM⟩ := p4_kernel (N := N) hd s hs0
  obtain ⟨YM, hYM, hYM0, htv⟩ := p4_regularised_flow s invβ hβ hS P hY hnc (fun M => (hgM M).1)
  have hYm : ∀ t, Measurable (Y t) := fun t => (hY.filtered.adapted t).mono (ℱ.le t) le_rfl
  have hμp : ∀ r : ℝ, IsProbabilityMeasure (law P (Y (Real.toNNReal r))) := fun r =>
    (Measure.isProbabilityMeasure_map_iff (hYm _).aemeasurable).2 inferInstance
  have hμ0 : IsProbabilityMeasure (law P (Y 0)) := (Measure.isProbabilityMeasure_map_iff (hYm _).aemeasurable).2 inferInstance
  have hlaw0 : ∀ M, law P (YM M (Real.toNNReal 0)) = law P (Y 0) := fun M => by
    rw [Real.toNNReal_zero]
    exact congrArg (law P) (funext (hYM0 M))
  have hG : ∀ M τ, _ := fun M τ => p4_gibbs hd s hs0 N invβ hβ τ (hgM M).1
  have hm0 : ∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂(law P (Y 0)) < ⊤ := (((hG 0 0).2.2 (law P (Y 0))).2 hH0)
  -- the level-`M` dissipation inequality, with a measurable majorant of the Fisher information
  have hlev : ∀ M, ∃ D : ℝ → ℝ≥0∞, AEMeasurable D (volume.restrict (Set.Icc (0 : ℝ) S)) ∧
      (∀ r ∈ Set.Icc (0 : ℝ) S, fisherInfoW (p4GibbsOf invβ (p4Pot (gM M) s N r))
        (law P (YM M (Real.toNNReal r))) ≤ D r) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) S,
        gibbsEntropyW (p4GibbsOf invβ (p4Pot (gM M) s N t)) (law P (YM M (Real.toNNReal t))) +
          ((ENNReal.ofReal invβ * ∫⁻ r in Set.Icc (0 : ℝ) t, D r : ℝ≥0∞) : EReal) ≤
        gibbsEntropyW (p4GibbsOf invβ (p4Pot (gM M) s N 0)) (law P (YM M (Real.toNNReal 0))) := by
    intro M
    have hV := (hgM M).2 S hS.le
    have hF : P4FlowHyp invβ (p4Drift (gM M) s N) S (fun r => law P (YM M (Real.toNNReal r))) :=
      p4_flow_hyp P hβ.le hS hV.cont_b hV.lip (hYM M) (by
        have e : law P (YM M 0) = law P (Y 0) := congrArg (law P) (funext (hYM0 M))
        rw [e]; exact hm0)
    obtain ⟨C, h5⟩ := p4_mollified_ineq hβ hS.le hV hF
    have hFp := hF.prob
    have hfin0 : gibbsEntropyW (p4GibbsOf invβ (p4Pot (gM M) s N 0))
        (law P (YM M (Real.toNNReal 0))) < ⊤ := by
      rw [hlaw0 M]
      exact lt_of_le_of_lt (((hG M 0).2.2 (law P (Y 0))).1) hH0
    have : IsProbabilityMeasure (law P (YM M (Real.toNNReal 0))) := hF.prob 0
    obtain ⟨e, he, hinit⟩ := p4_initial_jensen hβ hS.le hV hfin0
    obtain ⟨Cm, hCm, hmom⟩ := hF.mom
    have hv : ∀ n : ℕ, 0 < 1 / ((n : ℝ) + 1) := fun n => by positivity
    have hv0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h7 : ∀ t ∈ Set.Icc (0 : ℝ) S, _ := fun t ht => by
      have : IsProbabilityMeasure (law P (YM M (Real.toNNReal t))) := hF.prob t
      exact p4_mollify_lsc hβ hS.le hV ht (lt_of_le_of_lt (hmom t ht) hCm) hv hv0
    exact p4_level_bookkeeping (θ := invβ) (T := S) (C := C)
      (F := fun v t => p4Free invβ (p4Pot (gM M) s N t) (p4Mol v (law P (YM M (Real.toNNReal t)))))
      (Dv := fun v r => p4Diss invβ (p4Pot (gM M) s N r) (p4Mol v (law P (YM M (Real.toNNReal r)))))
      (H := fun t => gibbsEntropyW (p4GibbsOf invβ (p4Pot (gM M) s N t)) (law P (YM M (Real.toNNReal t))))
      (I := fun r => fisherInfoW (p4GibbsOf invβ (p4Pot (gM M) s N r)) (law P (YM M (Real.toNNReal r))))
      hβ (fun v hv => (h5 v hv).1) (fun v hv => (h5 v hv).2) he hinit
      (fun t ht => (h7 t ht).1) (fun r hr => (h7 r hr).2)
  choose D hDm hDI hDE using hlev
  -- `M → ∞`
  refine p4_limit_bookkeeping (θ := invβ) (S := S)
    (H := fun τ => gibbsEntropyW (selfSimWeight d s invβ N τ) (law P (Y (Real.toNNReal τ))))
    (HM := fun M τ => gibbsEntropyW (p4GibbsOf invβ (p4Pot (gM M) s N τ)) (law P (YM M (Real.toNNReal τ))))
    (I := fun r => fisherInfoW (selfSimWeight d s invβ N r) (law P (Y (Real.toNNReal r))))
    (D := D) (R := gibbsEntropyW (selfSimWeight d s invβ N 0) (law P (Y 0))) hDm ?_ ?_ ?_
  · intro τ hτ
    have : ∀ M, IsProbabilityMeasure (law P (YM M (Real.toNNReal τ))) := fun M =>
      (Measure.isProbabilityMeasure_map_iff (((hYM M).filtered.adapted _).mono (ℱ.le _) le_rfl).aemeasurable).2 inferInstance
    exact (p4_lsc_M hd s hs0 N invβ hβ τ (fun M => (hgM M).1) (htv τ hτ)).1
  · intro r hr
    have : ∀ M, IsProbabilityMeasure (law P (YM M (Real.toNNReal r))) := fun M =>
      (Measure.isProbabilityMeasure_map_iff (((hYM M).filtered.adapted _).mono (ℱ.le _) le_rfl).aemeasurable).2 inferInstance
    refine ((p4_lsc_M hd s hs0 N invβ hβ r (fun M => (hgM M).1) (htv r hr)).2).trans ?_
    exact liminf_le_liminf (Eventually.of_forall fun M => hDI M r hr)
  · intro M τ hτ
    refine (hDE M τ hτ).trans ?_
    rw [hlaw0 M]
    exact ((hG M 0).2.2 (law P (Y 0))).1

example := (@ss_P4_entropy_free_proof : type_of% @HRS.MP.SelfSim.ss_P4_entropy_free)

end HRS.MP.SelfSimP4
