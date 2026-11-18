import HRS.Whole.HeadlineStatement
import HRS.MS.StarTie
import HRS.MS.OrbIdTie
import HRS.MS.FldRemTie

/-!
# S56 plan: S5.6 `general_paths` (HRS/Whole/Headline.lean:226)

Written 2026-10-23 (worker S56).  TeX: supplement L3971-3997 (statement), proof L3989-4025, preceded by L3884-3905
(`W:r2:general-orbits`), L3425-3458 (trace comparison `W:r2:trace-comparison`), L3912-3957 (`E_{N,p}`, `w_N`, `epsilon_{N,p}`).

## 0. Verdict on the frozen statement

TRUE and non-vacuous as far as I can tell; no statement defect forces a stop.  Junk-value audit (all checked against the
current Lean text):

* `energyMomentE`, `initialErrorE` are `lintegral`-valued, may be `top`.  `S.σ N, S.A N > 0` (`sigmaScale`: `κ N` or
  `min κ √(N/invβ)`, both positive), so `ofReal σ * top = top`: the bound is trivial when `E_{N,p} = top` or `ε_{N,p} = top`.
  Hence the junk `(energyMomentE ..).toReal = 0` inside `generalLocalizationRate` is harmless (it only matters when the
  energy moment is finite).
* `M₂ <= 0` is impossible under the moment hypotheses (`pair (withDensityReal ρ) |x|² = 0` contradicts `IsProbDensity`),
  so `1 + M₂ > 0` and `w_N >= 0`, `q_N w_N >= 0`, `Real.sqrt` is not a junk.  `q_N = 0` iff `invβ = 0` (`qScale`), then
  both `q w` terms vanish exactly and `Y` has deterministic Gaussian part (`multivariateGaussian 0 0`).
* `smoothDist 2` is an `iSup` over `CbUnitBall`: bounded by `2` for probability laws, genuine (AEMeasurable conjuncts make the
  laws probability measures, the instance `OscPath` is a Borel space).  `wassersteinE` is `ℝ≥0∞`-valued (no junk).
* `flucPathW` / `processWindow` / `windowPathOf` return `0` off the continuity event.  Continuity of `t ↦ σ(μ_N^t - ρ_N^t) ∈ B_m`
  holds a.s.: `X` continuous a.s. (`IsWholeStrongSolution.cont`), and `t ↦ ρ_N^t(ψ)` is continuous for every `ψ ∈ C_b²`
  (`s55f_weak_cont_bdd`/`s55_weak_cont` of S5.5: even when the Bochner integral of the weak identity is a junk `0`, the
  identity forces continuity), plus `ℓ²` tail control from `‖φ_α‖_∞ <= C λ_α^{-m/2+..}` (summable, `m > J+3d+4`).
  So the AEMeasurable conjuncts are true (modify on a measurable null set; `Y` continuous a.s. by `IsLinearFluctuationSolutionW.cont`).
* `η₀ : Ω → (Euc d → ℝ) → ℝ` is an arbitrary random FUNCTION (no measurability, no linearity).  Only its values `η₀(U^{0,t}φ_α)`
  enter (through `initialErrorE` and the Gaussian part of `Y`).  The statement is still true (see 2.F): `Y` continuous and
  `Y^t(φ) - A η₀(U^{0,t}φ) ~ Gaussian ⟂ η₀` for each finite family force that, for rational `t`, the path
  `c(t)_α := A η₀(U^{0,t}φ_α)` is a.s. restrictions of a continuous path; `ε` (a `sup` over all `t`) dominates the rational sup.
  The `lintegral` of a possibly non-measurable integrand is a lower integral, monotone: only upper bounds of the form
  `∫⁻ (measurable) <= ∫⁻ (big)` are used.  For the proof the random FUNCTION `η₀` is replaced by the random PATH `c ∈ C([0,T];ℓ²)`
  (a Polish space), see packet P7.
* Pathwise uniqueness of the particle SDE is NOT a hypothesis of `general_paths`, but the frozen `duality_identity_rd` asks for
  `SelectedFlowRd` whose first branch contains `WholePathwiseUnique`.  The proof of `duality_identity_rd`
  (`HRS/MH/DualityRdFinal.lean`) only uses `flow_contact` (the strong solution as a contact strong solution), so the identity is
  applied through the packets A4/B3/C2 directly with `IsWholeStrongSolution + IsWholeFilteredSolution` (no uniqueness needed).
* `X₀` is only a.e. equal to the measurable `X 0` and `IndepFun (X₀, η₀) W` is stated for the possibly non-measurable `X₀`;
  independence transfers to `X 0` (sets differing by a subset of a null set have the same outer measure).  Small lemma, P7.
* `OscAdjointInput (S.coeff N) b.m b.T` is still in the frozen text (temporary hypothesis, F-CAU).  It supplies exactly what is
  needed for the identification clause (`duhamel`, junk-free `feature`).  No action: it is kept as a hypothesis.
* The statement does not use S5.4 `weighted_higher_order` nor S5.7: no dependency on worker S54.

## 1. Merged inputs used (exact names)

* Features/maximal/commutator: `HRS.MS.Star.general_orbits_features_proof`, `general_orbits_maximal_proof` (StarTie),
  `HRS.MS.Go.general_orbits_commutator_proof` (GoTie): `C0min` of the commutator row is the `C₀min` of `general_paths`.
* Duhamel/K-measurability tools: `s55f_*`, `s55m_*` (GoFeatAux1..5, GoMeasAux1..3), `s55f_coeffHyp`, `s55f_propagatorW_eq`,
  `s55f_weak_cont_bdd`, `s55_ul_of_sup` (GoFeatAux1), `s55fMeas_holds`, `propagatorW_unique_star`.
* Identification: `HRS.MS.S52.orbit_maximal_identification_bdd` (OrbIdTie; the repaired statement with `hB`); `s52_*` helpers.
* Duality: `HRS.MH.DualityRd*` packets (A4, B3, C2; `flow_contact`) / `HRS.Whole.AppendixA.duality_identity_rd` (statement).
* Cutoff test inequality: `HRS.Whole.AppendixALemmas.test_cutoff_pathwise` (deterministic; `cNormE`, `smearScale`, `oNΛ`),
  `whole_coercivity_pair` (proved: `HRS.MH.CoercTest.p_assembly`), `oNΛ_le_oN`.
* Main-paper abstract Hilbert pieces: `HRS.Uniform.smooth_path_comparison_proof` (Q45Smooth), `Q45.maximal_estimate_meas`,
  `relative_covariance_coupling_proof` (RelativeCoupling), `Q14.q14_bures2_W2`, `hilbert_polar_coupling`, `hilbert_martingale_w2`
  (HilbertMartingale), the GF skeleton (`HRS/Main/GFSpec3..GFFinal*.lean`: `gf_adapted_coupling_trace`, `gff_*`, the proof of
  `gf_wasserstein_comparison`, `gf_init_enlargement`, `gf_law_identification`) as templates (they are stated for
  `NegSobolev`/`GeneralSetup`, so they are re-proved or re-instantiated for `K = KSpace d m T`).

## 2. Proof architecture

Fixed: `T = b.T`, `m = b.m`, `K := KSpace d m T`, `ℓ² := OscDual d m`, `𝒯 : C([0,T];K) → C([0,T];ℓ²)`,
`(𝒯M)(t) = (M T).evalA t - (M T).B + (M t).B` (`reconstructPath`), a bounded linear map; `Γ_a(r,x) = gradFeature (S.coeff N) m T a r x`.

A. Constants.  `C₀min := max(commutator C₀min, coercivity C₀', Λ-dependent bound making oNΛ(C₀',Λ) <= oN(C₀))`; from
   `general_orbits_features/maximal/commutator`, `test_cutoff_pathwise` constants; `Σ_α λ_α^{(J-m)} < ∞` (`summable_oscEigenvalue_rpow_iff`).
B. Pathwise covariance error.  For injective `X`, `R >= 1`, `‖featureForm(μ_N) - featureForm(ρ_r dx)‖_{𝔖₁} <= C q [R^{d/2}(N^{-1/d} + √(F+o)) + (m₂(μ_N)+m₂(ρ_r))/R²]`
   (variational definition of `traceNormForm`: for finite orthonormal pairs `(e_i),(f_i)` and signs `ε_i`, `Σ|C(e_i,f_i)| = 2q Σ_a (μ_N-ρ_r)(h_a)`,
   `h_a = ⟨AΓ_a,Γ_a⟩`, `A = Σ ε_i f_i⊗e_i`, `‖A‖ <= 1`; derivatives of `h_a` by `ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear`;
   `𝒩(h) = cNormE χ h` bounded by `s55_ul_of_sup`-type bound (a `ulocNormE` version of that lemma is needed, same proof with `z ∈ ℝ^d`)).
   Then expectation and `inf_R` give `E∫_0^T ‖Σ_r - C̄_r‖₁ dr <= C T q w_N`, Jensen for `√`.
C. Time regularity.  `ρ_N^t` weakly continuous; `t ↦ σ(μ_N^t - ρ_N^t) ∈ ℓ²` continuous; AEMeasurable path maps; joint measurability of
   `(r,ζ) ↦ F_N(X_r ζ, ρ_r) + o_N` (needs `t ↦ g*ρ_t(x)` continuity by a `ε`-truncation argument, `ρ_t <= Λ`).
D. K-valued particle martingale.  `Φ r ζ (i,a) = √(2q/N) Γ_a(r, X_r ζ i)`, `IsHSIntegrand` (progressive: `ofNNRealTime X` progressive;
   `(r,x) ↦ Γ_a(r,x) ∈ K` jointly measurable: separate continuity in `r` by the equi-Lipschitz bound of S5.5 and Carathéodory,
   `s55m_ex`), the Itô integral `M` (`IsHilbertItoIntegral`) and `IsHilbertMartingaleWithCovariation P ℱ T M Sg` with
   `Sg r ζ = featureForm m T q (Γ·(r)) (empirical (X_r ζ))` (Itô isometry layer of `HRS/Prob/HilbertMartingale.lean`; torus analogue
   `gf_particle_martingale`).  Deterministic side: `Cb r = featureForm .. (ρ_r dx)` is an `IsDetCovDensity` (trace bound `Ctr`, measurability).
E. Mild identity.  A.s., for all `t ∈ [0,T]` and `α`: `Ξ(t)_α = I(t)_α + (𝒯M)(t)_α + R(t)_α`, with `I(t)_α = σ(μ_N^0-ρ_N^0)(U^{0,t}φ_α)`,
   `R(t)_α = (σ/2)∫_0^t flucInteractionRd .. dr`; from `DualityIdentityRd` at rational `t` (hypotheses `IsRegularMFRd s 3 Λ T ρ`
   from `s55f_coeffHyp`, `VHypRd` from `s55f_vhyp_quadV`), `orbit_maximal_identification_bdd` and continuity in `t` of both sides.
F. Gaussian side and initial path.  (i) `c := Ψ(η₀)` continuous path (Kolmogorov modification of the Gaussian part `Y - Aη₀(U)`),
   (ii) `law(Y path) = law(c + 𝒯G)`, `G` the continuous `K`-Gaussian martingale with covariation `Cb` (covariance of `(𝒯G)(t)_α` is `noiseCovW`
   because `Λ_{t,α}(Γ_a(r,x)) = 1_{r<=t} ∂_aU^{r,t}φ_α(x)` by `OscAdjointInput.duhamel`), (iii) initial coupling enlargement making `c` `ℱ_0`-measurable
   (Polish target; `gf_init_enlargement` template), `ε`-term `E‖I - c‖`.
G. Remainder: `‖R(t)‖_{ℓ²} <= (σ/2) C (Σ b_α²)^{1/2} ∫_0^T (F+o)(X_r) dr` by the commutator row; `E sup_t ‖R‖ <= C T σ E_{N,1}`, `L²` version by Cauchy-Schwarz in `r`.
H. Smooth bound: `smooth_path_comparison_proof` with `H = E = K`, identity evolution (`EvolData.TwoLevel`), `X₀ = k_n`, `k_n = (c_n(0), c_n', 0)`, `c_n` piecewise-linear
   interpolation of `c` (`H¹`, measurable in `c`), `n → ∞` (constant independent of `X₀`); push forward by `𝒯`
   (`cbUnitBall_comp_clm`), add `R` and `I - c` by the 1-Lipschitz property of `Φ ∈ C_b²`.
I. `W_p`: `relative_covariance_coupling_proof` (adapted Gaussian coupling, cost `‖Σ-Cb‖₁`) + difference martingale in `K` with
   `E‖𝒯(M-G)‖²_{C_tℓ²} <= Cmax E∫ Tr` (that is `general_orbits_maximal`, clause (ii) of `OrbitMaximalConclusion`) + `q14_bures2_W2` +
   `(E∫ cost)^{1/2} <= √(C q w_N)`, Minkowski with `R` and `I - c`.
J. Assembly: ties, cases `E=top`, `ε=top`, AEMeasurable conjuncts, `inf_R`.

## 3. Packets (each <= 2k lines; files HRS/MS/GenPathAux<k>.lean, tie GenPathTie.lean)

| id | file(s) | content | est. lines | depends |
|----|---------|---------|-----------:|---------|
| P1 | GenPathAux2 | step B pathwise (`s56_trace_pathwise`) | 700-1000 | features, test_cutoff_pathwise |
| P2 | GenPathAux3 | step B expectation + `w_N` (`s56_trace_moment`), Jensen, `inf_R` | 400-600 | P1, C (energy measurability) |
| P3 | GenPathAux4 | step G (`s56_remainder_pathwise`, `s56_remainder_moment_p1/p2`) | 500-700 | commutator row |
| P4 | GenPathAux5 | step C (continuity/AEMeasurable/energy measurability) | 700-900 | S5.5 weak continuity |
| P5 | GenPathAux6-7 | step D (K-martingale, covariation, `IsDetCovDensity`) | 1200-1600 | S5.5 measurability, HilbertMartingale |
| P6 | GenPathAux8-9 | step E (mild identity, rational times -> all times) | 1000-1400 | duality packets, S5.2 |
| P7 | GenPathAux10-11 | step F(i),(iii), independence transfer | 900-1300 | GF template |
| P8 | GenPathAux12-14 | step F(ii) law identification + Gaussian `K`-martingale | 1800-2500 | P5 |
| P9 | GenPathAux15-16 | steps H, I abstract comparisons in `K` | 1500-2200 | Uniform, GF |
| P10 | GenPathTie | step J + `type_of%` tie | 600-900 | all |

Total estimate 9.5k-13k lines (the NEXT_WAVE_PLAN figure `~4k` is too small by a factor 2.5-3; the main-paper analogue
`general_fluctuation` took about 15k lines in HRS/Main/GF*).  With the stop rule 4,500 lines this run can deliver P1-P4 and part of P9,
which are the pieces with no dependence on the stochastic-integral construction; the rest is listed above with names.

## 4. Order of work in this run

1. GenPathAux1 (docstring = this plan).  2. P1, P2.  3. P3.  4. P4 or abstract part of P9, whichever compiles first.
Each compiled file without unfinished proofs is committed.  No change to any frozen file; if a packet statement turns out false it is reported.

## 5. Status at the end of run 1 (committed; every declaration complete, dependencies only propext, Classical.choice, Quot.sound; about 2.2k lines incl. this plan)

| packet | declarations | file |
|--------|--------------|------|
| P1 | `s56_trace_generic`, `s56_trace_pathwise` (pathwise `‖C_r - C̄_r‖₁ ≤ C q [R^{d/2}(N^{-1/d}+√(F+o)) + (m₂+m₂')/R²]`, `C₀min` from `p_assembly`/`oNΛ ≤ oN`) | GenPathAux2, GenPathAux3 |
| P2 | `s56_moment_core`, `s56_trace_moment` (`E∫_0^T‖Σ_r-C̄_r‖₁ ≤ C q T w_N`, `generalLocalizationRate`) | GenPathAux4 |
| P3 | `s56_rem_l2`, `s56_rem_moment_p1/p2`, `s56_fluc_eq_comm` (`flucInteractionRd = ½ commN`), `s56_rem_bound`, `s56_rem_moment` (`‖R_N‖_{L^p(C_tℓ²)} ≤ C σ E_{N,p}`, `p=1,2`) | GenPathAux5, 12, 13, 14 |
| P4 | `s56_energy_meas`, `s56_energy_aemeas`, `s56_mm_aemeas` (joint measurability, discharges the hypotheses of `s56_trace_moment`) | GenPathAux11 |
| P9 | `s56_reconCLM` (`𝒯`, norm `≤ 3+√T`), `s56_idEvol` + `MaxHyp` + `s56_isStochConv_id`, `s56_smooth_abstract`, `s56_wasserstein_abstract` (`p=1,2`: Prop 3.21 / `gf_wasserstein_comparison_proof` on `𝒦` with identity evolution, then `𝒯` and the remainder) | GenPathAux6-10 |
| misc | `s56_secondMoment_pos` (`M₂>0`), `s56_itoIntegral_congr` (Itô integrals only see `r ≥ 0`) | GenPathAux15, 16 |

Findings of the run (none stops the row):
* The `K`-valued abstract comparisons are applied with `X₀ = X₀' = k₀`, the SAME `ℱ₀`-measurable initial `𝒦`-state encoding the PARTICLE
  initial path `I(t) = A(k₀)(t)`, and the arbitrary prescribed initial path `c` (from `η₀`, need not be `H¹`) is handled by the 1-Lipschitz
  triangle `Law(A(k₀)+𝒯G) -> Law(c+𝒯G)` on the coupling space (no `H¹` approximation of `c`).  `k₀` is the Bochner integral
  `σ∫ orbitFeature(D = id, r = 0)(x) d(μ_N^0 - ρ_N^0)` in `𝒦`; the value-Duhamel identity needed for `A(k₀)(t)_α = I(t)_α` follows from the
  gradient Duhamel of `OscAdjointInput` because `μ_N^0 - ρ_N^0` has total mass `0` (an `x`-independent offset is invisible).
* `empiricalNoiseIntegrand` contains `propagatorW C r t φ = Classical.choose` which is arbitrary for `r < 0`, so it is not provably progressive on `ℝ`;
  construct the Itô integral for the truncation `1_{r≥0}Φ` and transfer by `s56_itoIntegral_congr` (this is what `orbit_maximal_identification` consumes).
* `duality_identity_rd` is applied through its packets (A4/B3/C2): pathwise uniqueness (a field of `SelectedFlowRd`) is not used by its proof.
* The shared `.lake/build` was rebuilt by the orchestrator during the run (Orbits/Headline changed for S5.7); compile failures "object file ... does not exist" are transient.

Remaining packets (updated estimates): P5 `K`-martingale (joint measurability of `(r,x) ↦ Γ_{r,a}(x) ∈ K` for `r ≥ 0` by Carathéodory from
`s55m_continuousOn_star` + continuity of the classical solution in `r`, weak measurability via a Hilbert basis; HS integrand; `isHM_of_hilbertIto`,
`gfb3_exists_hilbert_version`) 1.0-1.4k; P6 mild identity 1.0-1.4k (note: truncated integrand, orbit_maximal_identification, rational times to all times);
P7 initial path `k₀`, `c`, independence transfer, enlargement 0.9-1.3k; P8 Gaussian `K`-martingale `G` on the coupling space (`gff_adapted_coupling_trace` generic),
law identification `Law Y = Law(c + 𝒯G)` 1.5-2.2k; P10 assembly/tie (cases `E=⊤`, `ε=⊤`, AEMeasurable conjuncts, `inf_R`) 0.7-1k.  Total remaining 5-7.5k lines.

-/

noncomputable section

namespace HRS.MS.GenPath

end HRS.MS.GenPath
