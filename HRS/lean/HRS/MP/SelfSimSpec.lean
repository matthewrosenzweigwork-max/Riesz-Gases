import HRS.Whole.AppendixALemmas2

/-!
# MP-SSPLAN: proof plan for S.A.28 `selected_law_selfsimilar` (statement-only interface + proved assembly)

Target: the frozen `HRS.Whole.AppendixALemmas.selected_law_selfsimilar` (`HRS/Whole/AppendixALemmas2.lean:782`;
TeX S L10931-10956, proof text S L10962-10985).  This file contains

* the definitions of the interface (`ssDrift`, `ssPath`, `SSAddSol`, `SSNoCollision`, `SSOrdered`, `SSEntropyIneq`);
* seven interface packets `ss_P1` ... `ss_P7` (statement only, `sorry`, except `ss_P6`, which is proved here);
* the assembly `selected_law_selfsimilar_proof` (statement verbatim, **proved** from the packets), tied to the frozen
  statement by `example := (@selected_law_selfsimilar_proof : type_of% @selected_law_selfsimilar)`.

## Verdict on the frozen statement

True as written (agreeing with the ISSUES review "MP: statement review for the whole-space clauses of S.A.22-S.A.28").
One point the review did not list, which costs a packet: **the statement carries no Brownian filtration.**  Every torus
input (B.3 `selected_law_fke`, `HRS/Stochastic/SelectedLawFKE.lean:813`; B.14/B.15, `HRS/Appendix/CepaFlow.lean:282,312`)
assumes `hF : IsFilteredSolution P ℱ W' W X`, and the other whole-space theorems receive it through
`RdStanding.filtered` (`HRS/Whole/AppendixA.lean:420`, added 2026-10-15, ISSUES §I).  `SelectedFlowRd` only says that each
`X t` is measurable.  The statement stays true because adaptedness is *derivable*: the integrated equation is uniquely
solvable path by path (locally Lipschitz drift off the diagonal in the collision-free branch; monotone drift
`-∇U`, `U` convex on the Weyl chamber, in the Cépa-Lépingle branch), so `X_t` is a.s. a function of
`(X₀, W|[0,t])`.  Packet P1 proves this.  (If the orchestrator prefers, a technical hypothesis
`∃ ℱ W', IsWholeFilteredSolution P ℱ W' W X` as in `RdStanding.filtered` would delete most of P1; I did not change
anything.)  `hdens0` is redundant (finite entropy implies `≪ vol`, packet P6), and the case `M = 0` of
`SelectedFlowRd` is void here (`M = -1 ≠ 0`, `d ≥ 1`).

## Representation of the interface

* `ssPath X τ = selfSimProcess X τ` re-indexed by `τ : ℝ≥0` (so that `IsWholeFilteredSolution` applies);
* `SSAddSol P ν b S ℱ W' W Y`: `Y` has everywhere continuous paths, is a filtered solution (Brownian `W'` for `ℱ`,
  coordinates of `W`, adapted, progressive), starts collision-free, satisfies the integrated additive-noise equation
  `Y_t = Y_0 + ∫_0^t b(r, Y_r) dr + √(2ν)(W_t - W_0)` on `[0,S]` componentwise (the exact shape of
  `IsWholeContactStrongSolution.eqn`, with a time-dependent drift), and has Lebesgue-null contact occupation;
* the branch information is kept separately: `SSNoCollision` (collision-free on `[0,S]`) or `SSOrdered` (the
  ordering clause of `IsWholeCepaLepingleFlow`).

## Packets (size: S < 300, M 300-1000, L 1000-3000, XL > 3000 Lean lines)

**P1 `ss_P1_filtered_version` (c) new probability, L.**  From `SelectedFlowRd` produce an everywhere-continuous
modification `X'` (`X' t = X t` a.s. for `t ≤ T`, `X' 0 = X₀` a.s.) which is an `SSAddSol` for the original drift on
`[0,T]`, with the branch information.  `X'` must be frozen after `T` (`X'_t := X'_{min t T}`): beyond `T` the given `X_t`
is only measurable, so it need not be adapted to any Brownian filtration of `W`, and `IsWholeFilteredSolution.adapted`
is required for all `t`.  Route: `exists_isBrownianFiltration_of_isVectorBrownian` (`Stochastic/Bridge.lean:75`)
gives the augmented filtration of `(X₀, W')` and the continuous modification `W'`.  Set `X' := X` on a measurable
full-measure set where the paths are continuous and the equation holds, `0` elsewhere.  Collision-free branch:
regularised drifts `b_M` (= `b` on `{min_{i≠j}|x_i-x_j| ≥ 1/M}`, globally Lipschitz) give adapted global solutions
(`exists_sde_solution_global_nonneg`, `Stochastic/SDE.lean:1050`) which equal `X'` on `[0,T]` for `M ≥ M(ω)` by
deterministic uniqueness, exactly as `b15c_regularised_eq_strong_proof` (`Appendix/B15CAux3.lean:346`); hence
`X'_t` is an a.s. limit of `ℱ_t`-measurable maps (`IsCompleteFiltration.measurable_of_ae_eq`).  Cépa branch
(`d = 1`, `s = 0`, `a = 1`): **deterministic** uniqueness of ordered null-occupation solutions of the integral equation
for a fixed driving path (the ordering permutation is forced by the distinct initial point; the noise cancels in the
difference, which is absolutely continuous; `-∇U` is monotone on the open chamber, where both paths are for a.e. `r`;
so `|x_r-y_r|²` is nonincreasing; template CepK2/CepU2 of `HRS/MC/CepaPlan.md` §1 "B.2 uniqueness", on the line).  Hence
the solution relation `Γ_t ⊂ (x₀, w|[0,t], x|[0,t])` (Borel: parametric integrals, ordering and occupation are Borel
conditions, quantifiers over rational times by continuity) is the graph of a map `F_t` on its analytic projection, `F_t`
is relatively Borel by Souslin separation (`AnalyticSet.measurablySeparable`,
`Mathlib/MeasureTheory/Constructions/Polish/Basic.lean:512`), and `X_t = ev_t ∘ F_t (X₀, W'|[0,t])` a.s. is
measurable for the completed `σ(X₀, W'|[0,t]) ⊆ ℱ_t`.  The same solution-map argument also covers the free branch
(locally Lipschitz uniqueness off the diagonal), so one may skip the regularisation there.  No Yamada-Watanabe or
Yosida step is needed.  Progressive measurability: continuity + adaptedness.  Dependencies: none.  ~600 lines (free
branch by regularisation) + ~900 (solution map, Souslin, Cépa uniqueness).

**P2 `ss_P2_time_change` (b) time change, L.**  `X̄^τ = e^{-τ/2} X'^{e^τ-1}` is an `SSAddSol` for the self-similar drift
`ssDrift` on `[0, log(1+T)]` for `ℱ̄_τ = ℱ_{e^τ-1}` and `W̄_τ = e^{-τ/2}W_{e^τ-1} + ½∫_0^τ e^{-r/2} W_{e^r-1} dr`
(`= ∫_0^{e^τ-1}(1+u)^{-1/2} dW_u`).  Route: (i) pathwise integration by parts with the `C¹` factor `e^{-τ/2}` and the
change of variables `t = e^r - 1` in `∫ b(X_t) dt` (integrability transfers since `e^{r/2} ≤ √(1+T)`); (ii) the
homogeneity `∇g(λy) = λ^{-s-1}∇g(y)` (`λ > 0`, also at `y = 0` where both sides are the junk `0`), which turns
`e^{τ/2} b(e^{τ/2}ξ)` into `-(a_s(τ)/N)∑∇g(ξ_i-ξ_j)`; (iii) `W̄` is Brownian for `ℱ̄`: continuous martingale with
`⟨W̄^k, W̄^l⟩_τ = δ_{kl}τ` and `levy_characterization` (`Stochastic/DDS.lean:1449`); (iv) adaptedness, occupation
(the time change is a diffeomorphism), collision-freeness and ordering are scale invariant.  This is the
"deterministic change of variables" of TeX L10963; the TeX does not prove (iii).  Dependencies: P1 (for its output
only).  Uses: `levy_characterization`, `ito_formula_additive` (`Stochastic/Ito.lean:3632`) or a direct moment
computation.  ~1000 lines.

**P3 `ss_P3_fke` (a) port of B.3, M.**  For any `SSAddSol` with a drift jointly measurable and continuous on
`[0,S] × Ω_N`, the laws solve `SolvesFKEW`.  Port of `selected_law_fke_FKE` (`Stochastic/SelectedLawFKE.lean:623`):
Itô (`ito_formula_additive`) for `Φ(r, Y_r)`, expectation of the Itô integral `0`, Fubini, `Φ(S, ·) = 0`.  What
transfers verbatim: the Itô/Fubini skeleton, the shifted filtration `ℱ (max t 0)` (`b15e_shiftFil`), the treatment of
contact times (`∇Φ = 0` off `K`).  What changes: no periodic lift (`fderiv_periodic_add`, `repC`, lattice
invariance disappear), `V ≡ 0`, the drift is time dependent (the Itô drift is `∂_rΦ + νΔΦ + DΦ[b(r,·)]`); compactness
of the torus was used only to bound `V` and the lifted test (`SelectedLawFKE.lean` "Bounds" section, ~L200-260);
here the compact support `K ⊂ Ω_N` and continuity of `b` on `[0,S] × K` give the bounds.  Used twice: original
variables (clause 4) and self-similar variables (clause 2).  Dependencies: none.  ~700 lines.

**P4 `ss_P4_entropy_free` (c) new analysis, XL.**  Entropy inequality `SSEntropyIneq` for a collision-free
self-similar solution.  Route (TeX L10969-10982, made precise): (1) truncated kernels `g_M` (smooth, `g_M ≤ g`,
`g_M = g` on `{|x| ≥ 1/M}`, radially nonincreasing, `∇g_M` bounded Lipschitz; for `s > 0` also `g_M ≥ 0`), self-similar
regularised drift `-∇Ū_M^τ`, `Ū_M^τ = a_s(τ)/(2N)∑g_M + ¼|ξ|²`; global strong solutions for `(ℱ̄, W̄)`
(`exists_sde_solution_global_nonneg`); they equal `Y` on `[0,S]` for `M ≥ M(ω)` (template
`b15c_regularised_eq_strong_proof`), so `Law(Y^M_τ) → Law(Y_τ)` in total variation, uniformly in `τ`.  (2) Level-`M`
inequality `𝓗_{Ḡ_M^τ}(f_M^τ) + β⁻¹∫_0^τ 𝓘_{Ḡ_M^r}(f_M^r) dr ≤ 𝓗_{Ḡ_M^0}(f^0) ≤ 𝓗_{Ḡ^0}(f^0)` (last step: `Ū_M ≤ Ū`):
**not** by the torus Fokker-Planck chain (see "compactness" below) but by the CepH2 route "mollify the law, not the
equation" (`HRS/MC/CepH2Plan.md`; proved as `cep_H2_cylinder_entropy_proof`, `HRS/MC/CepH2.lean:50`), transplanted
from the cylinder `S¹ × ℝ^{N-1}` to `ℝ^{dN}` (plain Gaussian mollifier, no periodisation, second moments from the
quadratic confinement), with one new term: `β∫∂_τŪ_M u ≤ 0` (`∂_τŪ_M = -(s/2)a_s(τ)/(2N)∑g_M ≤ 0` for `s > 0` since
`g_M ≥ 0`; `= 0` for `s = 0` since `a_0 ≡ 1`).  The weak FP for the regularised laws with Gaussian tests comes from P3's
Itô skeleton with non-compactly supported tests (CepH2 class `H2Test`).  (3) `M → ∞`: lower semicontinuity of `𝓗`
(monotone in `M` because `Ū_M ↑ Ū`, then lsc for a fixed reference under TV convergence; the Donsker-Varadhan step must
use the non-compact version, CepH2 `cepH2_entropy_lsc`, `HRS/MC/CepH2Ent3.lean:37`, not `b15b_klDiv_liminf_le`, which
needs `CompactSpace`, `Appendix/B15BAux1.lean:82`); of `𝓘` (each test field `ζ` has compact support in `Ω_N`, where
`Ū_M = Ū` for large `M`, so each `ζ`-functional converges; template `cepH2_fisher_lsc`, `HRS/MC/CepH2Fish3.lean:18`);
Fatou in `r`; `EReal` bookkeeping (template `b15e_step4_limit`, B15EAux8).  New lemma: `0 < Z_{Ḡ^τ} < ∞` on `ℝ^{dN}`
(Gaussian majorant for `s > 0`; polynomial pair factor `∏|ξ_i-ξ_j|^{β/(2N)}` times Gaussian for `s = 0`; the collision set
is Lebesgue-null), replacing `b15_gibbsPartition_pos_lt_top` (`Appendix/B15Aux2.lean:220`).  Dependencies: P2's output
shape, P3 (skeleton).  ~4500 lines (CepH2 was ~9000 on the cylinder including periodisation and the freezing of a `C²`
potential; here the potential is smooth after truncation and no freezing is needed, but time dependence is new).

**P5 `ss_P5_entropy_cepa` (a) port of B.14 to the line, XL.**  The same inequality for `d = 1`, `s = 0`, ordered
contact solutions.  In self-similar variables the drift is time independent (`a_0 ≡ 1`): it is the Cépa-Lépingle flow
with `a = 1` and confinement `V(ξ) = ξ²/4` on `ℝ` (TeX L10969 "so B.14 applies"; but B.14 is proved on the circle only).
Port of the proved chain `HRS.MC.CepH5Fin.cep_H5_entropy_confined_proof` (`HRS/MC/CepH5FinProof.lean`): conditioning on
the order class of `X₀` (CepH0 additivity, CepH5 mixture), Yosida regularisation in chamber coordinates (CepE), the
regularised dissipation inequality (CepH2, now on the Weyl chamber `ℝ^N` with quadratic confinement: simpler than the
cylinder, no transverse periodicity), limit by lsc (CepH3), identification with `Y` by per-ω uniqueness (CepU2 analogue,
shared with P1).  What changes: chamber/alcove geometry (no lattice anchor), `V` unbounded with `V'' = ½`
(the torus used `‖V''‖_∞ < ∞` from compactness, `Appendix/CepaFlow.lean:274`, docstring of B.14), a priori moment bounds from confinement
instead of compactness.  Dependencies: P1 (uniqueness lemma), P2's output shape.  ~5000 lines.

**P6 `ss_P6_absCont_of_entropy` (b) elementary, S.  PROVED here.**  `gibbsEntropyW G μ < ⊤ → μ ≪ vol`
(`klDiv_of_not_ac`, `smul_absolutelyContinuous`, `withDensity_absolutelyContinuous`).

**P7 `ss_P7_drift_regular` (b) elementary, S.**  Joint measurability of both drifts and continuity on
`[0,S] × Ω_N`.  Route: `rieszKernel d s` is smooth on `{x ≠ 0}` (explicit formula; or reuse the whole-space kernel
facts in `HRS/Whole/Basic.lean`), `gradient` measurable (`measurable_fderiv`), finite sums.  ~150 lines.

**Assembly** (this file, proved): P1 → P2 → (P4 or P5 by the branch) → law congruences (`Measure.map_congr`, the
modification), clause 1 from clause 3 and P6, clauses 2 and 4 from P3 (+ P7) and `ss_solvesFKEW_congr`.

## Order of attack

P7, P6 (done) → P3 (M, low risk, unblocks clauses 2 and 4) → P1 free branch → P2 → P4 (main risk: integrability on
`ℝ^{dN}` in the mollified entropy computation, exactly the CepH2 risk) → P1 Cépa branch and P5 together (shared
per-ω uniqueness on the Weyl chamber).

## Points where the TeX is incomplete / torus compactness is essential

* TeX L10973: the left side should be `𝓗_{Ḡ_{N,ε}^τ}` (the regularised weight), not `𝓗_{Ḡ_N^τ}`; the identity at
  "the smooth level" on `ℝ^{dN}` is asserted without the integrability justification (no torus FP theory there).
* TeX L10969: "B.14 applies" — B.14 (`M:B:prop:cepa-entropy-confined`) is a statement on `𝕋`; the needed statement on
  `ℝ` with quadratic confinement is P5, not in the manuscript.
* TeX L10963-10969: "use the same Brownian motions" in self-similar time presupposes that `W̄` is a Brownian motion for
  `ℱ_{e^τ-1}` (P2 (iii)), not proved in the TeX.  Note that the regularisation must be done in self-similar variables
  (or with a self-similarly rescaled cut-off): regularising `g` in the original variables makes, for `s = 0`, the
  regularised self-similar potential decrease the cut-off scale like `e^{-τ/2}`, and then `∂_τŪ_ε` has the wrong sign
  in the region `|ξ_i-ξ_j| ≲ ε e^{-τ/2}`.
* Strong-solution adaptedness is implicit in "canonical selected particle process" (TeX) but absent from
  `SelectedFlowRd` (P1, see the verdict).
* Compactness used essentially by the torus proofs (not portable):
  - the whole Fokker-Planck chain behind B.15: `adjoint_torus_classical` (`PDE/WellPosed.lean:532`, Fourier on `𝕋^n`),
    `d1_fp_exists`/`d1_fp_smooth`/`d1_fp_comparison`/`d1_fp_entropy` (`PDE/TorusFPSpec.lean:412,427,464,488`), used by
    `b15e_law_entropy` (`Appendix/B15EAux4.lean:162`) and `b15e_regularised_entropy` (`Appendix/B15EAux7.lean:21`);
    replaced in P4 by the CepH2 route;
  - Donsker-Varadhan with `C(α, ℝ)` tests: `b15b_klDiv_eq_iSup`, `b15b_klDiv_liminf_le` (`Appendix/B15BAux1.lean:71,82`,
    `[CompactSpace α]`); replaced by the non-compact lsc of CepH2 (`HRS/MC/CepH2Ent3.lean:37`);
  - `0 < Z_G < ∞` for free on the torus (`b15_gibbsPartition_pos_lt_top`, `Appendix/B15Aux2.lean:220`); on `ℝ^{dN}` a
    new Gaussian-majorant lemma (inside P4/P5).
  Not essential: the torus B.3 proof (bounds on `V`, periodic lift) and the separation/stabilisation argument
  (`particle_uniform_separation`, `Stochastic/Particle.lean:4777`, uses only compactness of `[0,T]`).

## Status (coverage.tsv, checked 2026-10-19)

Proved: B.3 `selected_law_fke` (row M:B:prop:selected-law-fke), B.14 `cepa_entropy_confined` (via
`cep_H5_entropy_confined_proof`), B.15 `sde_entropy_law` (via `sde_entropy_law_proof`), `cep_H2_cylinder_entropy_proof`,
`levy_characterization`, `ito_formula_additive`, `exists_sde_solution_global_nonneg`,
`exists_isBrownianFiltration_of_isVectorBrownian`.  `#print axioms` (2026-10-19, standard three only):
`levy_characterization`, `ito_formula_additive`, `exists_sde_solution_global_nonneg`,
`exists_isBrownianFiltration_of_isVectorBrownian`, `selected_law_fke`, `selected_law_fke_FKE`,
`b15c_regularised_eq_strong_proof`, `b15e_step4_limit`, `b15_gibbsPartition_pos_lt_top`; the `HRS/MC/Cep*` results are
proved per coverage.tsv but their modules are not in the shared build, so not re-checked here.  In this file
`ss_P6_absCont_of_entropy` and `ss_solvesFKEW_congr` are sorry-free, and `selected_law_selfsimilar_proof` depends on
`sorryAx` only through the packets P1-P5, P7.  Stated (sorry): S.A.28 itself.  No whole-space Fokker-Planck,
Gibbs-entropy or Fisher-information result exists yet (`SolvesFKEW`, `gibbsEntropyW`, `fisherInfoW` are used nowhere else).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MP.SelfSim

variable {d : ℕ}

/-! ### Interface definitions -/

/-- The self-similar drift `b̄_i(τ, Ξ) = -(a_s(τ)/N ∑_{j≠i} ∇g(ξ_i-ξ_j) + ½ξ_i)` (TeX S L10965-10967), literally the
drift of the second conclusion of `selected_law_selfsimilar`. -/
def ssDrift (d : ℕ) (s : ℝ) (N : ℕ) (τ : ℝ) (Ξ : EucConfig d N) : EucConfig d N :=
  fun i => -((aSelfSim s τ / N) • ∑ j ∈ Finset.univ.erase i,
    rieszKernelGrad d s (Ξ i - Ξ j) + (1 / 2 : ℝ) • Ξ i)

/-- The self-similar process indexed by `τ : ℝ≥0`. -/
def ssPath {Ω : Type*} {N : ℕ} (X : ℝ≥0 → Ω → EucConfig d N) (τ : ℝ≥0) (ζ : Ω) : EucConfig d N :=
  selfSimProcess X (τ : ℝ) ζ

/-- A filtered, everywhere-continuous, collision-free-started solution on `[0,S]` of the additive-noise equation
`Y_t = Y_0 + ∫_0^t b(r, Y_r) dr + √(2ν)(W_t - W_0)` (componentwise, the shape of `IsWholeContactStrongSolution.eqn`)
with Lebesgue-null contact occupation. -/
structure SSAddSol {Ω : Type*} [mΩ : MeasurableSpace Ω] {N : ℕ} (P : Measure Ω) (ν : ℝ)
    (b : ℝ → EucConfig d N → EucConfig d N) (S : ℝ) (ℱ : Filtration ℝ mΩ)
    (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (W : ℝ≥0 → Ω → (Fin N → Euc d))
    (Y : ℝ≥0 → Ω → EucConfig d N) : Prop where
  filtered : IsWholeFilteredSolution P ℱ W' W Y
  cont : ∀ ζ, Continuous fun t => Y t ζ
  init_distinct : ∀ᵐ ζ ∂P, Y 0 ζ ∉ eucCollisionSet d N
  eqn : ∀ᵐ ζ ∂P, ∀ t : ℝ≥0, (t : ℝ) ≤ S →
    (∀ i, IntegrableOn (fun r : ℝ => b r (Y (Real.toNNReal r) ζ) i) (Set.Icc 0 (t : ℝ))) ∧
    ∀ i, Y t ζ i = Y 0 ζ i + (∫ r in Set.Icc (0 : ℝ) t, b r (Y (Real.toNNReal r) ζ) i) +
      Real.sqrt (2 * ν) • (W t ζ i - W 0 ζ i)
  occupation : ∀ᵐ ζ ∂P,
    volume {r : ℝ | r ∈ Set.Icc 0 S ∧ Y (Real.toNNReal r) ζ ∈ eucCollisionSet d N} = 0

/-- No collisions on `[0,S]`, a.s. -/
def SSNoCollision {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (P : Measure Ω) (S : ℝ)
    (Y : ℝ≥0 → Ω → EucConfig d N) : Prop :=
  ∀ᵐ ζ ∂P, ∀ t : ℝ≥0, (t : ℝ) ≤ S → Y t ζ ∉ eucCollisionSet d N

/-- The ordering clause of `IsWholeCepaLepingleFlow` on `[0,S]`. -/
def SSOrdered {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (P : Measure Ω) (S : ℝ)
    (Y : ℝ≥0 → Ω → EucConfig d N) : Prop :=
  ∃ π : Ω → Equiv.Perm (Fin N), (∀ σ, MeasurableSet {ζ | π ζ = σ}) ∧
    ∀ᵐ ζ ∂P, ∀ t : ℝ≥0, (t : ℝ) ≤ S → ∀ j : Fin d, ∀ k k' : Fin N, k ≤ k' →
      Y t ζ (π ζ k) j ≤ Y t ζ (π ζ k') j

/-- The self-similar entropy inequality `B:eq:selected-selfsimilar-entropy` on `[0,S]` for the laws of `Y`. -/
def SSEntropyIneq (d : ℕ) (s invβ : ℝ) (N : ℕ) (S : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : ℝ≥0 → Ω → EucConfig d N) : Prop :=
  ∀ τ ∈ Set.Icc (0 : ℝ) S,
    gibbsEntropyW (selfSimWeight d s invβ N τ) (law P (Y (Real.toNNReal τ))) +
      ((ENNReal.ofReal invβ * ∫⁻ r in Set.Icc (0 : ℝ) τ,
        fisherInfoW (selfSimWeight d s invβ N r) (law P (Y (Real.toNNReal r))) : ℝ≥0∞) : EReal) ≤
    gibbsEntropyW (selfSimWeight d s invβ N 0) (law P (Y 0))

/-! ### The interface packets -/

/-- **P1** (new probability, L).  Strong-solution adaptedness: an everywhere-continuous modification of the selected
flow is a filtered solution for some Brownian filtration, with the branch information. -/
theorem ss_P1_filtered_version (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (N : ℕ)
    (hN : 2 ≤ N) (invβ : ℝ) (hβ : 0 < invβ) (T : ℝ) (hT : 0 < T)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N)
    (hX : SelectedFlowRd P (⟨s, -1, fun _ => 0, invβ⟩ : WholeDyn d) T X₀ W X) :
    ∃ (X' : ℝ≥0 → Ω → EucConfig d N) (ℱ : Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ),
      (∀ t : ℝ≥0, (t : ℝ) ≤ T → X' t =ᵐ[P] X t) ∧ (∀ᵐ ζ ∂P, X' 0 ζ = X₀ ζ) ∧
      SSAddSol P invβ (fun _ Ξ i => particleDriftW (⟨s, -1, fun _ => 0, invβ⟩ : WholeDyn d) Ξ i)
        T ℱ W' W X' ∧
      (SSNoCollision P T X' ∨ (d = 1 ∧ s = 0 ∧ SSOrdered P T X')) := by
  sorry

/-- **P2** (time change, L).  The self-similar process of a filtered solution of the original equation is a filtered
solution of the self-similar equation on `[0, log(1+T)]` (for `ℱ̄_τ = ℱ_{e^τ-1}` and the time-changed Brownian
motion), and collision-freeness and ordering transfer. -/
theorem ss_P2_time_change (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (N : ℕ)
    (hN : 2 ≤ N) (invβ : ℝ) (hβ : 0 < invβ) (T : ℝ) (hT : 0 < T)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {X : ℝ≥0 → Ω → EucConfig d N}
    (hX : SSAddSol P invβ (fun _ Ξ i => particleDriftW (⟨s, -1, fun _ => 0, invβ⟩ : WholeDyn d) Ξ i)
      T ℱ W' W X) :
    ∃ (ℱb : Filtration ℝ mΩ) (Wb' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (Wb : ℝ≥0 → Ω → (Fin N → Euc d)),
      SSAddSol P invβ (ssDrift d s N) (Real.log (1 + T)) ℱb Wb' Wb (ssPath X) ∧
      (SSNoCollision P T X → SSNoCollision P (Real.log (1 + T)) (ssPath X)) ∧
      (SSOrdered P T X → SSOrdered P (Real.log (1 + T)) (ssPath X)) := by
  sorry

/-- **P3** (port of B.3, M).  The laws of a filtered additive-noise solution solve the weak forward equation on the
collision-free configuration space, for a drift jointly measurable and continuous on `[0,S] × Ω_N`. -/
theorem ss_P3_fke {N : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {ν : ℝ} (hν : 0 ≤ ν) {S : ℝ} (hS : 0 < S) {b : ℝ → EucConfig d N → EucConfig d N}
    (hbm : Measurable fun p : ℝ × EucConfig d N => b p.1 p.2)
    (hbc : ContinuousOn (fun p : ℝ × EucConfig d N => b p.1 p.2)
      (Set.Icc 0 S ×ˢ (eucCollisionSet d N)ᶜ))
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {Y : ℝ≥0 → Ω → EucConfig d N} (hY : SSAddSol P ν b S ℱ W' W Y) :
    SolvesFKEW ν b S (fun r => law P (Y (Real.toNNReal r))) := by
  sorry

/-- **P4** (new analysis, XL).  The self-similar entropy inequality for a collision-free self-similar solution. -/
theorem ss_P4_entropy_free (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (N : ℕ)
    (hN : 2 ≤ N) (invβ : ℝ) (hβ : 0 < invβ) (S : ℝ) (hS : 0 < S)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {Y : ℝ≥0 → Ω → EucConfig d N}
    (hY : SSAddSol P invβ (ssDrift d s N) S ℱ W' W Y) (hnc : SSNoCollision P S Y)
    (hH0 : gibbsEntropyW (selfSimWeight d s invβ N 0) (law P (Y 0)) < ⊤) :
    SSEntropyIneq d s invβ N S P Y := by
  sorry

/-- **P5** (port of B.14 to the line, XL).  The self-similar entropy inequality for an ordered (Cépa-Lépingle)
self-similar solution, `d = 1`, `s = 0`. -/
theorem ss_P5_entropy_cepa (N : ℕ) (hN : 2 ≤ N) (invβ : ℝ) (hβ : 0 < invβ) (S : ℝ) (hS : 0 < S)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ} {W : ℝ≥0 → Ω → (Fin N → Euc 1)}
    {Y : ℝ≥0 → Ω → EucConfig 1 N}
    (hY : SSAddSol P invβ (ssDrift 1 0 N) S ℱ W' W Y) (hord : SSOrdered P S Y)
    (hH0 : gibbsEntropyW (selfSimWeight 1 0 invβ N 0) (law P (Y 0)) < ⊤) :
    SSEntropyIneq 1 0 invβ N S P Y := by
  sorry

/-- **P6** (elementary, S; proved).  Finite Gibbs entropy forces absolute continuity. -/
theorem ss_P6_absCont_of_entropy {N : ℕ} {G : EucConfig d N → ℝ} {μ : Measure (EucConfig d N)}
    (h : gibbsEntropyW G μ < ⊤) : μ ≪ (volume : Measure (EucConfig d N)) := by
  have h1 : relEntropy μ (gibbsRefW G) ≠ ⊤ := by
    intro htop
    rw [gibbsEntropyW, htop] at h
    simp at h
  have h2 : μ ≪ gibbsRefW G := by
    by_contra hac
    exact h1 (InformationTheory.klDiv_of_not_ac hac)
  refine h2.trans ?_
  unfold gibbsRefW
  exact Measure.smul_absolutelyContinuous.trans (withDensity_absolutelyContinuous _ _)

/-- **P7** (elementary, S).  Regularity of the two drifts. -/
theorem ss_P7_drift_regular (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (N : ℕ) (invβ : ℝ) :
    (Measurable (fun p : ℝ × EucConfig d N => ssDrift d s N p.1 p.2) ∧
      ∀ S : ℝ, ContinuousOn (fun p : ℝ × EucConfig d N => ssDrift d s N p.1 p.2)
        (Set.Icc 0 S ×ˢ (eucCollisionSet d N)ᶜ)) ∧
    (Measurable (fun p : ℝ × EucConfig d N => fun i : Fin N =>
        particleDriftW (⟨s, -1, fun _ => 0, invβ⟩ : WholeDyn d) p.2 i) ∧
      ∀ S : ℝ, ContinuousOn (fun p : ℝ × EucConfig d N => fun i : Fin N =>
        particleDriftW (⟨s, -1, fun _ => 0, invβ⟩ : WholeDyn d) p.2 i)
        (Set.Icc 0 S ×ˢ (eucCollisionSet d N)ᶜ)) := by
  sorry

/-! ### Assembly helpers (proved) -/

/-- `SolvesFKEW` only sees the family on `[0,S]`. -/
theorem ss_solvesFKEW_congr {N : ℕ} {ν S : ℝ} (hS : 0 ≤ S) {b : ℝ → EucConfig d N → EucConfig d N}
    {μ μ' : ℝ → Measure (EucConfig d N)} (h : ∀ r ∈ Set.Icc (0 : ℝ) S, μ r = μ' r)
    (H : SolvesFKEW ν b S μ') : SolvesFKEW ν b S μ := by
  intro Φ hΦ
  rw [h 0 ⟨le_rfl, hS⟩]
  have hI : (∫ r in (0 : ℝ)..S, ∫ x,
      (deriv (fun r' => Φ r' x) r +
        ν * ∑ k : Fin N × Fin d, iteratedFDeriv ℝ 2 (Φ r) x ![configBasis d N k, configBasis d N k] +
        fderiv ℝ (Φ r) x (b r x)) ∂(μ r)) =
      ∫ r in (0 : ℝ)..S, ∫ x,
      (deriv (fun r' => Φ r' x) r +
        ν * ∑ k : Fin N × Fin d, iteratedFDeriv ℝ 2 (Φ r) x ![configBasis d N k, configBasis d N k] +
        fderiv ℝ (Φ r) x (b r x)) ∂(μ' r) := by
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [Set.uIcc_of_le hS] at hr
    simp only [h r hr]
  rw [hI]
  exact H Φ hΦ

/-! ### The assembly -/

/-- Corollary S.A.28, assembled from the packets P1-P7 (statement verbatim from
`HRS.Whole.AppendixALemmas.selected_law_selfsimilar`). -/
theorem selected_law_selfsimilar_proof (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (N : ℕ)
    (hN : 2 ≤ N) (invβ : ℝ) (hβ : 0 < invβ) (T : ℝ) (hT : 0 < T)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N)
    (hX : SelectedFlowRd P (⟨s, -1, fun _ => 0, invβ⟩ : WholeDyn d) T X₀ W X)
    (hdens0 : law P (X₀) ≪ (volume : Measure (EucConfig d N)))
    (hH0 : gibbsEntropyW (selfSimWeight d s invβ N 0) (law P X₀) < ⊤) :
    (∀ τ ∈ Set.Icc (0 : ℝ) (Real.log (1 + T)),
      law P (selfSimProcess X τ) ≪ (volume : Measure (EucConfig d N))) ∧
    SolvesFKEW invβ (fun τ Ξ i => -((aSelfSim s τ / N) • ∑ j ∈ Finset.univ.erase i,
        rieszKernelGrad d s (Ξ i - Ξ j) + (1 / 2 : ℝ) • Ξ i)) (Real.log (1 + T))
      (fun τ => law P (selfSimProcess X τ)) ∧
    (∀ τ ∈ Set.Icc (0 : ℝ) (Real.log (1 + T)),
      gibbsEntropyW (selfSimWeight d s invβ N τ) (law P (selfSimProcess X τ)) +
        ((ENNReal.ofReal invβ * ∫⁻ r in Set.Icc (0 : ℝ) τ,
          fisherInfoW (selfSimWeight d s invβ N r) (law P (selfSimProcess X r)) : ℝ≥0∞) : EReal) ≤
      gibbsEntropyW (selfSimWeight d s invβ N 0) (law P X₀)) ∧
    SolvesFKEW invβ (fun _ Ξ i => particleDriftW (⟨s, -1, fun _ => 0, invβ⟩ : WholeDyn d) Ξ i) T
      (fun t => law P (X (Real.toNNReal t))) := by
  obtain ⟨X', ℱ, W', hXX', hX'0, hY, hbr⟩ :=
    ss_P1_filtered_version hd s hs0 hsd N hN invβ hβ T hT P X₀ W X hX
  obtain ⟨ℱb, Wb', Wb, hYb, hnc, hord⟩ := ss_P2_time_change hd s hs0 hsd N hN invβ hβ T hT P hY
  have hlog : 0 < Real.log (1 + T) := Real.log_pos (by linarith)
  -- laws: the modification and the re-indexing do not change the laws
  have hss : ∀ τ : ℝ, 0 ≤ τ → τ ≤ Real.log (1 + T) →
      law P (selfSimProcess X τ) = law P (ssPath X' (Real.toNNReal τ)) := by
    intro τ hτ hτT
    have hle : ((Real.toNNReal (Real.exp τ - 1) : ℝ≥0) : ℝ) ≤ T := by
      rw [Real.coe_toNNReal _ (by linarith [Real.add_one_le_exp τ])]
      have := (Real.le_log_iff_exp_le (by linarith : (0 : ℝ) < 1 + T)).1 hτT
      linarith
    refine Measure.map_congr ?_
    filter_upwards [hXX' (Real.toNNReal (Real.exp τ - 1)) hle] with ζ hζ
    funext i
    simp only [ssPath, selfSimProcess, Real.coe_toNNReal _ hτ, hζ]
  have h0 : law P X₀ = law P (ssPath X' 0) := by
    refine Measure.map_congr ?_
    filter_upwards [hX'0] with ζ hζ
    funext i
    simp [ssPath, selfSimProcess, hζ]
  have hXlaw : ∀ t ∈ Set.Icc (0 : ℝ) T,
      law P (X (Real.toNNReal t)) = law P (X' (Real.toNNReal t)) := fun t ht =>
    Measure.map_congr (hXX' _ (by rw [Real.coe_toNNReal _ ht.1]; exact ht.2)).symm
  have hH0' : gibbsEntropyW (selfSimWeight d s invβ N 0) (law P (ssPath X' 0)) < ⊤ := h0 ▸ hH0
  -- the entropy inequality for the self-similar version, by branch
  have hent : SSEntropyIneq d s invβ N (Real.log (1 + T)) P (ssPath X') := by
    rcases hbr with hnc0 | ⟨rfl, rfl, hord0⟩
    · exact ss_P4_entropy_free hd s hs0 hsd N hN invβ hβ _ hlog P hYb (hnc hnc0) hH0'
    · exact ss_P5_entropy_cepa N hN invβ hβ _ hlog P hYb (hord hord0) hH0'
  have hent' : ∀ τ ∈ Set.Icc (0 : ℝ) (Real.log (1 + T)),
      gibbsEntropyW (selfSimWeight d s invβ N τ) (law P (selfSimProcess X τ)) +
        ((ENNReal.ofReal invβ * ∫⁻ r in Set.Icc (0 : ℝ) τ,
          fisherInfoW (selfSimWeight d s invβ N r) (law P (selfSimProcess X r)) : ℝ≥0∞) : EReal) ≤
      gibbsEntropyW (selfSimWeight d s invβ N 0) (law P X₀) := by
    intro τ hτ
    have hI : (∫⁻ r in Set.Icc (0 : ℝ) τ,
        fisherInfoW (selfSimWeight d s invβ N r) (law P (selfSimProcess X r))) =
        ∫⁻ r in Set.Icc (0 : ℝ) τ,
          fisherInfoW (selfSimWeight d s invβ N r) (law P (ssPath X' (Real.toNNReal r))) :=
      setLIntegral_congr_fun measurableSet_Icc (fun r hr => by rw [hss r hr.1 (hr.2.trans hτ.2)])
    rw [hI, hss τ hτ.1 hτ.2, h0]
    exact hent τ hτ
  obtain ⟨⟨hm1, hc1⟩, ⟨hm2, hc2⟩⟩ := ss_P7_drift_regular hd s hs0 hsd N invβ
  refine ⟨fun τ hτ => ?_, ?_, hent', ?_⟩
  · -- clause 1: densities from finiteness of the entropy
    apply ss_P6_absCont_of_entropy (G := selfSimWeight d s invβ N τ)
    have h1 := hent' τ hτ
    have h2 : gibbsEntropyW (selfSimWeight d s invβ N τ) (law P (selfSimProcess X τ)) ≤
        gibbsEntropyW (selfSimWeight d s invβ N τ) (law P (selfSimProcess X τ)) +
        ((ENNReal.ofReal invβ * ∫⁻ r in Set.Icc (0 : ℝ) τ,
          fisherInfoW (selfSimWeight d s invβ N r) (law P (selfSimProcess X r)) : ℝ≥0∞) : EReal) :=
      le_add_of_nonneg_right (EReal.coe_ennreal_nonneg _)
    exact lt_of_le_of_lt (h2.trans h1) hH0
  · -- clause 2: the self-similar forward equation (P3 in self-similar variables)
    have hfke := ss_P3_fke P hβ.le hlog hm1 (hc1 _) hYb
    exact ss_solvesFKEW_congr hlog.le (fun r hr => hss r hr.1 hr.2) hfke
  · -- clause 4: the unconfined forward equation (P3 in the original variables)
    have hfke := ss_P3_fke P hβ.le hT hm2 (hc2 _) hY
    exact ss_solvesFKEW_congr hT.le (fun r hr => hXlaw r hr) hfke

example := (@selected_law_selfsimilar_proof : type_of% @selected_law_selfsimilar)

end HRS.MP.SelfSim
