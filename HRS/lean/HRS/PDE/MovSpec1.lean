import HRS.PDE.MovSpecAux
import HRS.Appendix.B15BAux1
import HRS.Appendix.B15DAux1
import HRS.Energy.PressureProof

/-!
# MOVSPEC (part 1): entropy dissipation along the moving reference `ℚ_{N,β}(μ^t)` on the torus

TeX: `HRS_periodic_main_20261008T010000Z.tex` (M).  The exact source `N:eq:source` (L6429-6441), the exponential
bound `N:eq:source-exp` (L6443-6450), the entropy differential `N:eq:entropy-differential` (L6452-6457),
`N:prop:pressure` and its proof (L6118-6137, L6344-6406), the commutator envelope (L6408-6417), the
sketch "Entropy identities without an inverse-Gibbs moment" (L8558-8585); the justification of the entropy
identities for the unregularised process is only *referred* to `sec:finite-regularity` (L6466-6467, L5768),
which is deterministic.  Design decision: `docs/PROOF_QUEUE.md` "2026-10-16 D3 / MOV design decision",
`docs/ISSUES.md` "MOV: TeX insufficiency for the moving-reference entropy identities" and "D3".

Files: `MovSpecAux.lean` (Mathlib-only analysis lemmas, all proved), `MovSpec1.lean` (this file: setting, `ε`-level entropy
packets), `MovSpec2.lean` (`L^p`: `mov_lp_ineq`, `mov_lp_bound`), `MovSpec2b.lean` (assembly of `mov_ent_ineq`: bounded
initial density, conditioning), `MovSpec3.lean` (modulated free energy `mov_mfe_ineq`; bridges A-D), `MovSpec.lean`.

## What is stated (consumer-facing, torus names)

* `mov_ent_ineq`  (`MovSpec2b`): integrated entropy inequality along the moving reference with source `R_N^t`,
  Fisher term dropped (ISSUES MOV item 4); includes the non-junk integrability of `E_Q[C_N]`.
* `mov_lp_ineq`, `mov_lp_bound` (`MovSpec2`): variable-exponent `L^p(Q_N^t)` bound along the exponent path of `P:eq:p-ode`.
* `mov_mfe_ineq`  (`MovSpec3`): modulated free energy dissipation `𝖤_N(f^t,μ^t) ≤ 𝖤_N(f^0,μ^0) - ½∫∫Comm_N f`.

## Consumer map (which consumer hypothesis each MOV statement discharges)

| MOV statement | consumer | what it replaces |
|---|---|---|
| `mov_ent_ineq` + `movT_entropy_bound` (+ `movT_source_exp`) | Thm 5.4 `dynamic_entropy`, `dynamic_comparison` (`HRS/Sections/Sec5.lean:150,174`) | the sentence "Justification of the entropy identities for the unregularized process is given in `sec:finite-regularity`" (M L6466-6467): `H_t ≤ C_T B_N` for `H(f_N^t | Q_N^t)` |
| `mov_lp_ineq` + `mov_lp_bound` (+ `movT_source_exp_scaled_uniform`, bridges B, C) | Lemma 5.8 `moving_log_moment` (`Sec5.lean:357`), Lemma 7.8 item 1 `alltime_Lp` (`HRS/Sections/Sec7Fields.lean:70`) | "variable-exponent identity ... first at bounded density truncations" (M L6674-6705, L8415-8420) |
| `mov_mfe_ineq` (+ bridge `movT_hyp_of_mfeHyp`) | Prop 3.41 `mfe_uniform` (`HRS/Energy/Coercivity.lean:3395`) | "pass the resulting integrated inequality to the selected law by the same entropy, Fisher-information, and diagonal-truncation lower-semicontinuity argument" (M L3220-3224) |
| bridges A (`movT_traj_of_global`, `movT_traj_uniform`), D (`movT_hyp_of_parts`, `movT_Q_eq_beta`) | `IsSmoothPositiveTrajectory`/`IsParticleSystem` of Sec5 | hypotheses of the consumers |

## Chain plan (packets; sizes S < 100, M < 300, L < 800, XL ≥ 800 lines; `SPEC` = sorried)

Notation: `Q^M_t = movT_Q (b15c_gReg d s M) …` (`ℚ` with the truncated kernel `g_M`, packet C of B.15), `f^n_t` the law
of the regularised process `X^{M_n}`, `S^M = movT_srcReg` the regularised source (the D3 source plus normalisation).
Existing inputs: D3 (proved layer `d3_entropy_moving_proof`, `d1_fp_entropy_proof`, `HRS/PDE/TorusFPEntropy{Classical,Measure}.lean`;
statements `d3_*` in `TorusFPEntropySpec.lean`), D2 `b15d_*` (`B15DAux1-5`), packet C `b15c_*` (`B15CAux1-3`), packet B `b15b_*`
(`B15BAux1`, DV/lsc), `perturbed_pressure` (`PressureProof.lean:821`).

| # | packet | TeX | size | role |
|---|---|---|---|---|
| 1 | `movT_regSeq_exists` (MovSpec1) | L12157-12166 | M | consumer hypotheses ⇒ regularisation scheme (`MovRegSeq`), same as B.15 packet E step 1 |
| 2 | `movT_traj_bounds` | L6425 | M | `inf ρ > 0`, uniform Lipschitz bound of `u^r` from `MovTraj` |
| 3 | `movT_pressure_two_sided_C2` | L6118-6137 | M | `pressure_two_sided` for `C²` backgrounds (new statement, existing one untouched) |
| 4 | `movT_Q_tendsto_weak` | L12183-12194 | M | `Q^{M_n}_t ⇀ Q_t` |
| 5 | `movT_init_tendsto` | – (not in TeX) | M | `H(f_0|Q^{M_n}_0) → H(f_0|Q_0)` (needs `0 ≤ T`) |
| 6 | `movT_convFun_tendstoUniformly`, `movT_gReg_L1_tendsto` | L6429-6441 | S+S | ISSUES item 3: `g_M*f → g*f`, `‖g-g_M‖_{L¹} → 0` |
| 7 | **`movT_srcReg_decomp` (MOV-A)** | L6429-6441 | L | `ε`-level exact source identity with one-body remainders `≤ C N ‖g-g_M‖_{L¹}`, `Lip(u^M) ≤ Lip(u) + o(1)`; routes 8, 10, `movT_source_exp_scaled_uniform` |
| 8 | `movT_srcReg_tendsto` | L6429-6441 | L | `S^{M_n} → R_N` off collisions (from 7 and the convergence `C^M_N → C_N`) |
| 9 | `movT_srcReg_measurable` | – | S | `S^M` Borel |
| 10 | `movT_reg_ineq` | L6452-6457, L12167-12180 | XL (1.5-2.5k) | `ε`-level inequality: D3 `d3_entropy_moving_proof` + D2 `b15d_law_eq_fp` + Config/Torus transport + `V ∈ C²` mollification |
| 11 | `movT_source_exp_uniform` | L6118-6137, L6344-6406 | XL | **gap (2)**: `ε`-uniform exponential bound; route (i) below; needs `pressure_two_sided` restated parametrically in `(g_L,q,c₀)` reusing the cores (L) plus 3, 7 |
| 12 | `movT_source_exp` | L6443-6450, L6413-6416 | M | `N`-uniform exponential bound of the exact source (`C²` version of `perturbed_pressure`) |
| 13 | `movT_source_limit_bdd` (MovSpec2b) | – | L | **gap (5)**, bounded-density case: Hölder UI + exceptional set (Review 1 D2) |
| 14 | `movT_cond_hyp`, `movT_cond_entropy_limit`, `movT_cond_narrow`, `movT_source_limit_cond` | – | M+M+S+M | general initial law by conditioning on `{dν₀/dQ₀ ≤ k}`, `k → ∞` |
| 15 | `movT_source_exp_scaled_uniform` (MovSpec2) | L6321-6322, L6670 | L | `L(t)`-scaled version of 11 (for `L^p`) |
| 16 | `movT_lp_reg_bound` (MovSpec2) | L6674-6695, L8415-8420 | XL+ | `ε`-level variable-exponent bound (needs the `L^p` analogue of D3, an optional D3 item) |
| 17 | `movT_lp_init_limsup` (MovSpec2) | – | M | initial `L^{p₀}` norms converge (needs `0 ≤ T`) |
| 18 | `movT_lp_lsc` (MovSpec2) | L6703-6705 | L | joint narrow lsc of `‖dν/dQ‖_{L^p(Q)}`, with eventual absolute continuity (Review 1 D1) |
| 19 | `movT_relEntropy_split` (MovSpec3) | L446-457 | M | `H(f|Q) = H(f|μ^{⊗N}) + βN∫F f + log K`, finiteness equivalence (`C²` density) |
| 20 | `movT_logK_integral` (MovSpec3) | L6439 | L | `(log K_N)' = βN E_Q C_N` (hand-checked, see MovSpec3) |
| 21 | `movT_isC12Test_of_weak` (MovSpec3) | – | M | `IsC12Test` from a weak solution with `C^{m_*+2}` bounds |
| 22 | bridges A `movT_traj_of_global`, A' `movT_traj_uniform`, B `movT_relaxation_L`, C `movT_prepared_initial_Lp`, D `movT_hyp_of_mfeHyp` (MovSpec3) | L738-745, L6660, L8409-8413 | S-M, M, M, M, S-M | consumer bridges |

Proved glue (no `sorry` in the proof body, conditional on the packets): `movT_QReg_isProb`, `movT_Q_isProb`, `movT_entropy_lsc`
(from `b15b_klDiv_liminf_le`), `movT_reg_init_law`, `movT_entropy_gronwall`, `mov_ent_ineq_bdd`, `mov_ent_ineq`,
`movT_entropy_bound`, `mov_lp_ineq`, `mov_lp_bound`, `mov_mfe_ineq`, `movT_hyp_of_parts`, `movT_Q_eq_beta`; Mathlib-only
lemmas in `MovSpecAux.lean` (`movspec_gronwall`, `movspec_gronwall_exp`, `movspec_gronwall_var` (variable coefficient,
Review 1 D6), `movspec_ent_assembly`, `movspec_gibbs`, `movspec_int_le`, `movspec_one_le_eLpNorm_rnDeriv`),
`movT_pPath_bounds`, `movT_pPath_ge`, `movT_commAt_eq_half`.

Entropy chain (`mov_ent_ineq`): `{dν₀/dQ₀ ≤ k}`-conditioning (14) ⟶ for each `k`, `mov_ent_ineq_bdd`: 1 ⟶ per level `n`: 10 ⟶
uniform `L^q` bound (16 with `L ≡ 1`, 17, 11) ⟶ 13 / 5 / `movT_entropy_lsc` (4) ⟶ `movspec_ent_assembly` ⟶ `k → ∞` with
`movT_entropy_gronwall` (uniform entropy bound), 14 (limit of the source terms, lsc) ⟶ `movspec_ent_assembly`.
Item (5) of ISSUES for `L^p` (UI for `(p-1)∫R h^p dQ`) is avoided: the `ε`-level bound is on `L^p` norms, which pass to the
limit by lsc (packet 18).  The packet `movT_energy_lsc` (ISSUES item 6) of the first draft was deleted: the route through the
entropy lsc makes it unnecessary.

Packet 11, route (i), verified: `g_M = g_L + q^M_0 - c_0` with `q^M_0 := g_M - g_L + c_0`.  Since `min(g,M) ≤ g_M ≤ g`
(`b15c_min_le_trunc`, `b15c_gReg_le`, `b15c_cap`) one has `0 ≤ q^M_0 ≤ q_0` as soon as `M ≥ sup g_L - c_0`, so the
envelope `q ≤ A w` and the row bound `a < a_0` of `q_0` (`N:eq:finite-split`, M L6355-6362) are inherited uniformly
in `M`; `|h^M_v| ≤ C‖v‖_{C¹}(g_M + c)` because `0 ≤ trunc' ≤ 1` and `trunc' = 0` on `g ≥ M+1`.
`N:lem:weak-pressure` is used unchanged (only the abstract `q`-kernel properties enter: M L6146-6155, L6372-6375).
The one-body remainders are bounded by `C N ‖g-g_M‖_{L¹}` (packet 7).  `perturbed_pressure`/`pressure_two_sided`
(`HRS/Energy/PressureProof.lean:821,506`) are stated for `g = periodicRiesz`, but their proof is parametric in `(g_L,q,c)`:
`pressure_upper_core` (:91; hypotheses `hsplit : g x = ∑ a_k cos_k + q x - c` for `x ≠ 0`, `RowOK` of `g_L`, `q`, `h`) and
`pressure_lower_core` (:157; any `RowOK` kernel with bounded row integrals) apply verbatim to `g_M`; the weak-reference
partition bound used inside `pressure_two_sided` is applied to `q^M_0 - θh + |θ|D` (envelope and row bound uniform in `M`).

## Review 1 repairs (what changed with respect to commit 0cbff84)

* D1 `movT_lp_lsc` gets `hacn : ∀ᶠ n, ν_n ≪ Q_n` (the statement was false without it); `mov_lp_ineq` keeps the
  absolute-continuity part of `movT_lp_reg_bound` and passes it on.
* D2 `movT_source_limit` (false via entropy + exponential moment alone) is replaced by the constructive route: bounded initial
  density (`movT_source_limit_bdd`, `mov_ent_ineq_bdd`, with the `L^q` bound from `movT_lp_reg_bound`) and conditioning
  (`movT_cond_*`, `movT_source_limit_cond`); `mov_ent_ineq` is glued through it; `movT_reg_entropy_bound` was removed.
* D3 `0 ≤ T` added to `movT_init_tendsto`, `movT_lp_init_limsup`.
* D4 `MovTraj` has `IsCk 2` densities with a `C²` bound; `movT_pressure_two_sided_C2` (new packet), `movT_source_exp`,
  `movT_relEntropy_split` weakened; `movT_isC12Test_of_weak`, `movT_hyp_of_mfeHyp` added.
* D5 MOV-A `movT_srcReg_decomp` (+ `movT_gReg_L1_tendsto`, `movT_convFun_tendstoUniformly`) added.
* D6 `movspec_gronwall_var` proved.  D7 `movT_energy_lsc` deleted.
* NOTE `mov_ent_ineq` now also concludes `Q_N^r`-integrability of `C_N`.  Bridges A-D added (MovSpec3).

## Doubts for the reviewer
* `movT_cond_hyp` (conditioning keeps the Brownian filtration/independence) and `movT_source_limit_bdd` (Hölder UI on `G^n`,
  exceptional set via the `L^q` bound) are the least routine new packets.
* `movT_lp_reg_bound` (XL+) needs an `L^p` analogue of D3 for classical positive solutions (not in the D3 layer).
* `movT_prepared_initial_Lp` excludes `β₀ = 0` (iid preparation) because `pressure_two_sided` needs positive temperature
  (small negative coupling for `s = 0`); bridge C is incomplete there.
* Bridges A, A', B depend on `Regime.reg`/`Regime.relax` (still sorried upstream) and on a relaxation input absent from
  `IsSmoothPositiveTrajectory`.
* `V ∈ C²` only: `D1/D3` need `Torus.IsSmooth U`, hence the mollification inside `movT_reg_ineq`.
* The `ε`-level source `S^M` is defined from the D3 formula `Lψ + κ|∇ψ|² - ∂_tψ + E_q ∂_tψ`; its relation to `R_N^t` is MOV-A
  and `movT_srcReg_tendsto`.

-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {d N : ℕ}

/-! ### Definitions: the moving reference, the commutator and the exact source -/

/-- The moving reference `Q_N^r = ℚ_{N,β}(μ^r)` (`H:eq:modulated-gibbs`, M L446-452) for an interaction kernel `g`
(`g = periodicRiesz d D.s` for the physical reference; `g = b15c_gReg d D.s M` for the regularised one),
`μ^r = withDensityReal (ρ r)`, `β = D.invβ⁻¹`. -/
def movT_Q (g : Torus d → ℝ) (D : DynData d) (N : ℕ) (ρ : ℝ → Torus d → ℝ) (r : ℝ) :
    Measure (Config d N) :=
  modulatedGibbs g N D.invβ⁻¹ (withDensityReal (ρ r))

/-- The commutator statistic `C_N(u;μ) = F_N^{h_u}(X_N,μ)` of `N:eq:commutator` (M L6409-6411),
`h_u(x,y) = (u(x) - u(y))·∇g(x-y)` (`commKernel`), for the transport field `u = β⁻¹∇log ρ + ∇g*ρ + ∇V`
of `N:eq:velocity` (M L6425, `mfeTransport`), at one time slice `ρ`. -/
def movT_commAt (D : DynData d) (N : ℕ) (ρ : Torus d → ℝ) (X : Config d N) : ℝ :=
  modulatedEnergy (commKernel (periodicRieszGrad d D.s) (mfeTransport D ρ)) X (withDensityReal ρ)

/-- The exact source `R_N = -βN(C_N(u;μ) - E_{Q_N}[C_N(u;μ)])` of `N:eq:source` (M L6429-6433) at one time slice,
`β = D.invβ⁻¹`, `Q_N = ℚ_{N,β}(μ)` (physical kernel).  The Bochner integral `E_{Q_N}[C_N]` is not junk:
`C_N` is `Q_N`-integrable by `N:eq:pair-exp` (`movT_source_exp`). -/
def movT_sourceAt (D : DynData d) (N : ℕ) (ρ : Torus d → ℝ) (X : Config d N) : ℝ :=
  -(D.invβ⁻¹ * N) * (movT_commAt D N ρ X -
    ∫ Y, movT_commAt D N ρ Y ∂(modulatedGibbs (periodicRiesz d D.s) N D.invβ⁻¹ (withDensityReal ρ)))

/-- `C_N(u^r;μ^r)` along a trajectory. -/
def movT_comm (D : DynData d) (N : ℕ) (ρ : ℝ → Torus d → ℝ) (r : ℝ) (X : Config d N) : ℝ :=
  movT_commAt D N (ρ r) X

/-- `R_N^r` along a trajectory (`N:eq:source`). -/
def movT_source (D : DynData d) (N : ℕ) (ρ : ℝ → Torus d → ℝ) (r : ℝ) (X : Config d N) : ℝ :=
  movT_sourceAt D N (ρ r) X

/-- Normalisation check: `movT_commAt = ½ Comm_N` (`B:eq:commutator-quantity`, M L2815-2818): both are the same
pairing, `F_N^h = ½ ∬ h d(μ_N-μ)^{⊗2}` for symmetric `h`. -/
theorem movT_commAt_eq_half (D : DynData d) (N : ℕ) (ρ : Torus d → ℝ) (X : Config d N) :
    movT_commAt D N ρ X = (1 / 2) * commQuantity d D.s (mfeTransport D ρ) X (withDensityReal ρ) := by
  unfold movT_commAt commQuantity commQuantityWith offDiagPairing modulatedEnergy
  ring

/-! ### The standing hypotheses -/

/-- The deterministic background of the moving reference: the smooth positive trajectory of Section 5 (M L738-745),
or the `(r,Λ)`-regular positive mean-field solution of Prop 3.41 (M L3205), with exactly the regularity the
proofs use.  Fields: `M = -I`, `β < ∞`, `V ∈ C²` (B.15 convention), `ρ` a weak mean-field solution on `[0,T]`
(`H:eq:meanfield`), strictly positive `C²` densities with a uniform `C²` bound (Review 1, D4: all pressure estimates use
the density only through its sup bound and positive lower bound, see `movT_pressure_two_sided_C2`; `MFEHyp` has
`C^{m_*+2}`), and the classical `C^{1,2}` regularity `IsC12Test T ρ ρt` (the TeX trajectory is smooth in
space-time; needed for the tilt `ψ^t` of D3).  Technical hypotheses: `C²`/positivity/`C^{1,2}` (see doubts in the
header). -/
structure MovTraj (D : DynData d) (T : ℝ) (ρ : ℝ → Torus d → ℝ) : Prop where
  gradient : D.M = -1
  pos_temp : 0 < D.invβ
  V_reg : Torus.IsCk 2 D.V
  mf : IsMeanFieldSolution D T ρ
  ck : ∀ r ∈ Set.Icc 0 T, Torus.IsCk 2 (ρ r)
  bounds : ∃ Λ₂ : ℝ, ∀ r ∈ Set.Icc 0 T, Torus.cbNorm 2 (ρ r) ≤ Λ₂
  pos : ∀ r ∈ Set.Icc 0 T, ∀ x, 0 < ρ r x
  classical : ∃ ρt : ℝ → Torus d → ℝ, IsC12Test T ρ ρt

/-- The particle system on the background: `X` a collision-free strong solution on `[0,T]` of
`H:eq:intro-particles` driven by the vector Brownian motion `W` with initial datum `X₀` independent of `W`
(the fields of `IsParticleSystem`, as in `MFEHyp`), adapted to a Brownian filtration (`IsFilteredSolution`, as in
`dynamic_comparison`, `moving_log_moment`, `MFEHyp`). -/
structure MovHyp {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (D : DynData d) (N : ℕ) (T : ℝ)
    (ρ : ℝ → Torus d → ℝ) (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d))
    (X : ℝ≥0 → Ω → Config d N) : Prop where
  traj : MovTraj D T ρ
  brownian : IsVectorBrownian P W
  indep : ProbabilityTheory.IndepFun X₀ (fun ω => fun t : ℝ≥0 => W t ω) P
  sol : IsStrongSolution P D T X₀ W X
  filtered : ∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X

/-! ### The regularised dynamics and the regularised source -/

/-- The one-body tilt `φ^r = β(V + g_M*ρ^r) + log ρ^r` (`g_M = b15c_gReg d D.s M`, `β = D.invβ⁻¹`) with
`ℚ^M(μ^r) ∝ e^{-βU_M} e^{∑_i φ^r(x_i)}` (`U_M = b15c_potentialReg`), the tilt of D3 (`d3_tiltPot κ U (ψ r)`,
`ψ = ∑_i φ`).  Check: `-βN F^M_N(X,μ) + ∑_i log ρ(x_i) = -β(2N)⁻¹∑_{i≠j} g_M + β∑_i g_M*μ(x_i) + ∑ log ρ(x_i)`. -/
def movT_phi (D : DynData d) (M : ℝ) (ρ : ℝ → Torus d → ℝ) (r : ℝ) (x : Torus d) : ℝ :=
  D.invβ⁻¹ * (D.V x + convFun (b15c_gReg d D.s M) (ρ r) x) + Real.log (ρ r x)

/-- The time derivative of the tilt: `β g_M*∂_tρ + ∂_tρ/ρ` (`ρt = ∂_tρ`). -/
def movT_phit (D : DynData d) (M : ℝ) (ρ ρt : ℝ → Torus d → ℝ) (r : ℝ) (x : Torus d) : ℝ :=
  D.invβ⁻¹ * convFun (b15c_gReg d D.s M) (ρt r) x + ρt r x / ρ r x

/-- The tilt on configurations `ψ^r(X) = ∑_i φ^r(x_i)`. -/
def movT_psi (D : DynData d) (M : ℝ) (ρ : ℝ → Torus d → ℝ) (r : ℝ) (X : Config d N) : ℝ :=
  ∑ i, movT_phi D M ρ r (X i)

/-- `∂_tψ^r(X) = ∑_i ∂_tφ^r(x_i)`. -/
def movT_psit (D : DynData d) (M : ℝ) (ρ ρt : ℝ → Torus d → ℝ) (r : ℝ) (X : Config d N) : ℝ :=
  ∑ i, movT_phit D M ρ ρt r (X i)

/-- The regularised source: the D3 source `Lψ + κ‖∇ψ‖² - ∂_tψ` of `d3_source` plus the normalisation
`E_{Q^M}[∂_tψ]` of `d3_entropy_moving` (`κ = D.invβ`, generator `L = d1_configGen κ (b15d_configDriftReg D M)` of the
regularised SDE `dX = -∇U_M dt + √(2κ)dW`, `|∇ψ|² = ∑_i|∇φ(x_i)|²`).  At `M = ∞` it is `R_N^r`
(`movT_srcReg_tendsto`); in general it differs from `R_N^r` by the one-body remainders of `g_M*ρ - g*ρ`. -/
def movT_srcReg (D : DynData d) (N : ℕ) (M : ℝ) (ρ ρt : ℝ → Torus d → ℝ) (r : ℝ) (X : Config d N) : ℝ :=
  d1_configGen D.invβ (b15d_configDriftReg D M) (movT_psi D M ρ r) X
    + D.invβ * ∑ i, ‖Torus.grad (movT_phi D M ρ r) (X i)‖ ^ 2
    - movT_psit D M ρ ρt r X
    + ∫ Y, movT_psit D M ρ ρt r Y ∂(movT_Q (b15c_gReg d D.s M) D N ρ r)

/-- Bundle of the data of the regularisation scheme of B.15 (packet C) along a sequence of levels `M n → ∞`:
Brownian filtration `(ℱ, W')`, initial lift `Y₀` of `X₀` adapted at all real times, regularised global strong solutions
`Y n` of the SDE with drift `b15c_liftedDriftReg D (M n)` driven by the same noise, and the a.s. eventual equality
`X^{M_n} = X` on `[0,T]` (`b15c_regularised_eq_strong`).  The hypotheses of `b15c_marginal_tendsto`. -/
structure MovRegSeq {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) (ℱ : Filtration ℝ mΩ)
    (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (D : DynData d) (T : ℝ) (X₀ : Ω → Config d N)
    (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N) (M : ℕ → ℝ)
    (Y₀ : Ω → Fin N → Euc d) (Y : ℕ → ℝ → Ω → (Fin N → Euc d)) : Prop where
  levels : Tendsto M atTop atTop
  levels_nonneg : ∀ n, 0 ≤ M n
  brownian : IsBrownianFiltration P ℱ W'
  coords : ∀ᵐ ω ∂P, ∀ t i j, W' t ω (i, j) = W t ω i j
  init_adapted : ∀ t : ℝ, Measurable[ℱ t] Y₀
  init_lift : ∀ᵐ ω ∂P, (fun i => Torus.mk (Y₀ ω i)) = X₀ ω
  sol : ∀ n, IsAdditiveSDESolution P ℱ W' (fun _ => b15c_liftedDriftReg D (M n)) (liftedNoise D)
    Y₀ (fun _ => ⊤) (Y n)
  eventually_eq : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ t : ℝ≥0, (t : ℝ) ≤ T →
    b15c_regProcess (Y n) t ω = X t ω


/-! ### Bridging packets (setting) -/

/-- **SPEC (sorried, M).**  From the consumer hypotheses to the regularisation scheme of B.15 along the levels `M n = n`:
a Brownian filtration `ℱ` with `ℱ t := ℱ₀ (max t 0)` (so that `Y₀ = rep ∘ X 0` is adapted at *all* real times, the
requirement of `b15c_exists_regularised_solution`; `IsFilteredSolution.adapted` constrains only `t ≥ 0`), the
global solutions `Y n` (`b15c_exists_regularised_solution`, from `b15c_liftedDriftReg_isLipschitz`, packet C) and the
eventual equality `X^{M_n} = X` (`b15c_regularised_eq_strong`).  Identical to the first step of B.15 packet E
(`b15_sde_entropy_law_free`).  TeX M L12157-12166. -/
theorem movT_regSeq_exists {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {D : DynData d} {T : ℝ} {ρ : ℝ → Torus d → ℝ} {X₀ : Ω → Config d N}
    {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (h : MovHyp P D N T ρ X₀ W X) :
    ∃ (ℱ : Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (M : ℕ → ℝ) (Y₀ : Ω → Fin N → Euc d)
      (Y : ℕ → ℝ → Ω → (Fin N → Euc d)), MovRegSeq P ℱ W' D T X₀ W X M Y₀ Y := by
  sorry

/-- **SPEC (sorried, S-M).**  Uniform bounds of the background on `[0,T]`: `inf ρ ≥ c₀ > 0` (joint continuity of
`ρ` from `IsC12Test` and compactness of `[0,T] × 𝕋^d`, positivity), and a uniform Lipschitz bound of the transport
field `u^r = β⁻¹∇log ρ^r + ∇g*ρ^r + ∇V` (`C¹` bounds of `ρ`, `∇g*ρ` via `HRS/Kernel/GradReg.lean`; M L6425). -/
theorem movT_traj_bounds {D : DynData d} {T : ℝ} {ρ : ℝ → Torus d → ℝ} (h : MovTraj D T ρ) :
    ∃ c₀ Lu : ℝ, 0 < c₀ ∧ 0 < Lu ∧ (∀ r ∈ Set.Icc 0 T, ∀ x, c₀ ≤ ρ r x) ∧
      ∀ r ∈ Set.Icc 0 T, IsLipschitzVF Lu (mfeTransport D (ρ r)) := by
  sorry

/-! ### Packets on the reference measures -/

/-- The regularised reference `ℚ^M(μ^r)` is a probability measure (`g_M` is smooth, hence bounded). -/
theorem movT_QReg_isProb (D : DynData d) {T : ℝ} {ρ : ℝ → Torus d → ℝ} (h : MovTraj D T ρ) (M : ℝ)
    {r : ℝ} (hr : r ∈ Set.Icc 0 T) :
    IsProbabilityMeasure (movT_Q (b15c_gReg d D.s M) D N ρ r) := by
  haveI : IsProbabilityMeasure (withDensityReal (ρ r)) := isProb_withDensityReal (h.mf.density r hr)
  have hg : Continuous (b15c_gReg d D.s M) :=
    b15c_isSmooth_continuous (b15c_gReg_isSmooth (b15_one_le_d D) D.hs0 D.hsd M)
  exact modulatedGibbs_prob_of_continuous hg _ _

/-- **SPEC (sorried, M): `pressure_two_sided` for `C²` backgrounds** (Review 1, D4).  The statement of
`pressure_two_sided` (`HRS/Energy/PressureProof.lean:506`) with the hypotheses `IsSmooth ρ`, `∀k, ‖ρ‖_{C^k} ≤ Λ_k`
replaced by `IsCk 2 ρ`, `‖ρ‖_{C²} ≤ Λ₂`.  The existing proof uses the density only through its sup bound
(`WeakRef.le_cbNorm_zero`), positivity and normalisation (M L6118-6137: "smooth positive background" is only used
through bounded density and lower bound), so the proof carries over verbatim.  Existing statements are not edited. -/
theorem movT_pressure_two_sided_C2 (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (cstar : ℝ) (hw : ∀ z : Torus d, z ≠ 0 → 1 ≤ periodicRiesz d s z + cstar)
    (βm βp : ℝ) (hβm : 0 < βm) (c₀ : ℝ) (hc₀ : 0 < c₀) (Λ₂ : ℝ) (B : ℝ) :
    ∃ θ₀ C : ℝ, 0 < θ₀ ∧ 0 ≤ C ∧
      ∀ ρ : Torus d → ℝ, IsProbDensity ρ → Torus.IsCk 2 ρ → (∀ x, c₀ ≤ ρ x) →
        Torus.cbNorm 2 ρ ≤ Λ₂ →
      ∀ h : Torus d → Torus d → ℝ, Measurable (Function.uncurry h) → (∀ x y, h x y = h y x) →
        (∀ x y, |h x y| ≤ B * (periodicRiesz d s (x - y) + cstar)) →
      ∀ N : ℕ, 2 ≤ N → ∀ β ∈ Set.Icc βm βp, ∀ θ : ℝ, |θ| ≤ θ₀ →
          ENNReal.ofReal (Real.exp (-(C * N * deltaN d s N))) ≤
              ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (-β * N *
                modulatedEnergy (fun x y => periodicRiesz d s (x - y) - θ * h x y) X
                  (withDensityReal ρ))) ∂(Measure.pi fun _ => withDensityReal ρ) ∧
          ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (-β * N *
                modulatedEnergy (fun x y => periodicRiesz d s (x - y) - θ * h x y) X
                  (withDensityReal ρ))) ∂(Measure.pi fun _ => withDensityReal ρ) ≤
            ENNReal.ofReal (Real.exp (C * N * deltaN d s N)) := by
  sorry

/-- The physical reference `ℚ_{N,β}(μ^r)` is a probability measure for a positive `C²` background
(`0 < K < ∞`: `gibbs_facts` with `rowOK_g_h`, and `movT_pressure_two_sided_C2` at `θ = 0`, `h = 0`).  PROVED from the
`C²` pressure packet.  Implicit in the TeX (H:eq:modulated-gibbs, M L446-452). -/
theorem movT_Q_isProb (hN : 2 ≤ N) {D : DynData d} {T : ℝ} {ρ : ℝ → Torus d → ℝ} (h : MovTraj D T ρ)
    {r : ℝ} (hr : r ∈ Set.Icc 0 T) :
    IsProbabilityMeasure (movT_Q (periodicRiesz d D.s) D N ρ r) := by
  have hd : 1 ≤ d := b15_one_le_d D
  have hβ : 0 < D.invβ⁻¹ := inv_pos.2 h.pos_temp
  haveI hμ : IsProbabilityMeasure (withDensityReal (ρ r)) := isProb_withDensityReal (h.mf.density r hr)
  obtain ⟨Bg, hBg⟩ := b15_periodicRiesz_lower D
  have hw : ∀ z : Torus d, z ≠ 0 → 1 ≤ periodicRiesz d D.s z + (Bg + 1) := fun z _ => by
    have := hBg z; linarith
  have hcont : Continuous (ρ r) := b15_continuous_of_isCk (h.ck r hr)
  obtain ⟨x₀, -, hx₀⟩ := isCompact_univ.exists_isMinOn (Set.univ_nonempty (α := Torus d))
    hcont.continuousOn
  have hc₀ : 0 < ρ r x₀ := h.pos r hr x₀
  obtain ⟨Λ₂, hΛ₂⟩ := h.bounds
  obtain ⟨θ₀, C, hθ₀, hC, hP⟩ := movT_pressure_two_sided_C2 hd D.s D.hs0 D.hsd (Bg + 1) hw D.invβ⁻¹
    D.invβ⁻¹ hβ (ρ r x₀) hc₀ Λ₂ 0
  have hP0 := hP (ρ r) (h.mf.density r hr) (h.ck r hr) (fun x => hx₀ (Set.mem_univ x))
    (hΛ₂ r hr) (fun _ _ => 0) measurable_const (fun _ _ => rfl) (fun x y => by simp) N hN
    D.invβ⁻¹ ⟨le_rfl, le_rfl⟩ 0 (by simp [hθ₀.le])
  simp only [zero_mul, sub_zero] at hP0
  obtain ⟨hlow, hup⟩ := hP0
  have hK0 : ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (-D.invβ⁻¹ * N *
      modulatedEnergy (fun x y => periodicRiesz d D.s (x - y)) X (withDensityReal (ρ r))))
      ∂(Measure.pi fun _ : Fin N => withDensityReal (ρ r)) ≠ 0 := by
    intro h0
    rw [h0] at hlow
    simp at hlow
    exact absurd hlow (not_le.2 (Real.exp_pos _))
  have hKt : ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (-D.invβ⁻¹ * N *
      modulatedEnergy (fun x y => periodicRiesz d D.s (x - y)) X (withDensityReal (ρ r))))
      ∂(Measure.pi fun _ : Fin N => withDensityReal (ρ r)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hup
  obtain ⟨Mρ, hMρ0, hMρ⟩ := exists_abs_bound hcont
  have hρΛ : ∀ x, ρ r x ≤ Mρ := fun x => (le_abs_self _).trans (hMρ x)
  obtain ⟨hgR, -⟩ := rowOK_g_h hd D.s D.hs0 D.hsd (Bg + 1) hw 0 hMρ0 hρΛ
    (h := fun _ _ => 0) measurable_const (fun x y => by simp)
  exact (gibbs_facts hgR hK0 hKt).2

/-- **SPEC (sorried, S-M).**  `ℚ^{M_n}(μ^r) ⇀ ℚ(μ^r)` narrowly on the compact space `Config d N`: the normalised
weights `e^{-βN F^{M}}/K^M` are dominated by a constant (`g_M ≥ -B`, `b15c_gReg_ge`) and converge off the collision set
(`b15c_gReg_eventuallyEq`), the normaliser converges and is positive (`movT_Q_isProb`).  This is the analogue of
`b15b_gibbsRef_tendsto_weak` / `b15c_normDensity_tendsto_L1` (B.15 Step 3, M L12183-12194) for the moving reference. -/
theorem movT_Q_tendsto_weak (hN : 2 ≤ N) {D : DynData d} {T : ℝ} {ρ : ℝ → Torus d → ℝ}
    (h : MovTraj D T ρ) {M : ℕ → ℝ} (hM : Tendsto M atTop atTop) (hM0 : ∀ n, 0 ≤ M n) {r : ℝ}
    (hr : r ∈ Set.Icc 0 T) {φ : Config d N → ℝ} (hφ : Continuous φ) :
    Tendsto (fun n => ∫ X, φ X ∂(movT_Q (b15c_gReg d D.s (M n)) D N ρ r)) atTop
      (𝓝 (∫ X, φ X ∂(movT_Q (periodicRiesz d D.s) D N ρ r))) := by
  sorry

/-- **Lower semicontinuity of the relative entropy along the regularisation** (the entropy part of B.15 Step 4,
M L12195-12204, for the moving reference): `H(f_t | Q_t) ≤ liminf_n H(f^n_t | Q^{M_n}_t)`.  PROVED from
`b15b_klDiv_liminf_le` (joint narrow lsc of `klDiv`, from Donsker-Varadhan), `b15c_marginal_tendsto` (narrow convergence of
the marginals) and `movT_Q_tendsto_weak`. -/
theorem movT_entropy_lsc {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} {D : DynData d} {T : ℝ}
    {ρ : ℝ → Torus d → ℝ} {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {X : ℝ≥0 → Ω → Config d N} {M : ℕ → ℝ} {Y₀ : Ω → Fin N → Euc d}
    {Y : ℕ → ℝ → Ω → (Fin N → Euc d)}
    (hN : 2 ≤ N) (htr : MovTraj D T ρ) (hS : IsStrongSolution P D T X₀ W X)
    (seq : MovRegSeq P ℱ W' D T X₀ W X M Y₀ Y) {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    relEntropy (P.map (X t.toNNReal)) (movT_Q (periodicRiesz d D.s) D N ρ t) ≤
      liminf (fun n => relEntropy (selectedLaw P (b15c_regProcess (Y n)) t)
        (movT_Q (b15c_gReg d D.s (M n)) D N ρ t)) atTop := by
  haveI hQ : IsProbabilityMeasure (movT_Q (periodicRiesz d D.s) D N ρ t) := movT_Q_isProb hN htr ht
  haveI hQn : ∀ n, IsProbabilityMeasure (movT_Q (b15c_gReg d D.s (M n)) D N ρ t) :=
    fun n => movT_QReg_isProb D htr (M n) ht
  haveI hf : IsProbabilityMeasure (P.map (X t.toNNReal)) :=
    inferInstance
  haveI hfn : ∀ n, IsProbabilityMeasure (selectedLaw P (b15c_regProcess (Y n)) t) := fun n =>
    b15b_selectedLaw_isProb (fun s => b15c_regProcess_measurable (seq.sol n) s) t
  exact b15b_klDiv_liminf_le
    (fun φ hφ => b15c_marginal_tendsto hS seq.sol seq.eventually_eq ht.1 ht.2 hφ)
    (fun φ hφ => movT_Q_tendsto_weak hN htr seq.levels seq.levels_nonneg ht hφ)

/-- **SPEC (sorried, M).**  Convergence of the initial regularised entropies: for a probability law `ν` with
`H(ν | Q_0) < ∞`, `H(ν | Q^{M_n}_0) < ∞` for all `n` and `H(ν | Q^{M_n}_0) → H(ν | Q_0)`.  Proof: write
`H(ν|Q^M) = H(ν|μ^{⊗N}) + βN∫F^M dν + log K^M` (`movT_relEntropy_split`, MovSpec3); `F^M ≤ F + C` and `F^M → F`
pointwise off the collision set, with `∫F dν < ∞`; monotone convergence of the pair part (`g_M ↑ g`), bounded one-body
parts, `K^M → K`.  Not stated in the TeX (B.15 Step 3 only treats the fixed Gibbs reference, M L12183-12187). -/
theorem movT_init_tendsto (hN : 2 ≤ N) {D : DynData d} {T : ℝ} {ρ : ℝ → Torus d → ℝ}
    (hT : 0 ≤ T) (h : MovTraj D T ρ) {M : ℕ → ℝ} (hM : Tendsto M atTop atTop) (hM0 : ∀ n, 0 ≤ M n)
    {ν : Measure (Config d N)} [IsProbabilityMeasure ν]
    (hfin : relEntropy ν (movT_Q (periodicRiesz d D.s) D N ρ 0) ≠ ⊤) :
    (∀ n, relEntropy ν (movT_Q (b15c_gReg d D.s (M n)) D N ρ 0) ≠ ⊤) ∧
      Tendsto (fun n => (relEntropy ν (movT_Q (b15c_gReg d D.s (M n)) D N ρ 0)).toReal) atTop
        (𝓝 (relEntropy ν (movT_Q (periodicRiesz d D.s) D N ρ 0)).toReal) := by
  sorry

/-! ### Packets on the source -/

/-- **One-body remainders** (ISSUES MOV item 3): `g_{M_n}*f → g*f` uniformly on the torus for every continuous `f`
(`‖g_M*f - g*f‖_∞ ≤ ‖f‖_∞‖g - g_M‖_{L¹}` and `‖g - g_M‖_{L¹} → 0` by dominated convergence: `g_M ≤ g` off `0`,
`g_M ≥ -B` (`b15c_gReg_ge`), `g ∈ L¹` (`CoercAux.integrable_periodicRiesz_one`), `g_M → g` off `0`
(`b15c_gReg_eventuallyEq`)).  Applied to `f = ρ, ∂ρ, ∂²ρ, ∂_tρ` this controls the tilt `φ^M = β(V + g_M*ρ) + log ρ`,
its first and second derivatives (`∂^α(g_M*ρ) = g_M*∂^αρ`) and `∂_tφ^M`, i.e. the difference between the regularised and
the exact one-body terms of the source (M L6429-6441 with `g` replaced by `g_ε`).  Stated as `TendstoUniformly`. -/
theorem movT_convFun_tendstoUniformly (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {M : ℕ → ℝ}
    (hM : Tendsto M atTop atTop) (hM0 : ∀ n, 0 ≤ M n) {f : Torus d → ℝ} (hf : Continuous f) :
    TendstoUniformly (fun n x => convFun (b15c_gReg d s (M n)) f x) (convFun (periodicRiesz d s) f)
      atTop := by
  sorry

/-- **SPEC (sorried, S): `‖g - g_M‖_{L¹} → 0`** (`g_M ≤ g` off `0`, `g_M ≥ -B`, `g ∈ L¹`, `g_M → g` off `0`: dominated
convergence; `b15c_gReg_le`, `b15c_gReg_ge`, `b15c_gReg_eventuallyEq`, `CoercAux.integrable_periodicRiesz_one`). -/
theorem movT_gReg_L1_tendsto (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {M : ℕ → ℝ}
    (hM : Tendsto M atTop atTop) (hM0 : ∀ n, 0 ≤ M n) :
    Tendsto (fun n => ∫ z : Torus d, |periodicRiesz d s z - b15c_gReg d s (M n) z|) atTop (𝓝 0) := by
  sorry

/-- The regularised transport field `u^M = β⁻¹∇log ρ + ∇(g_M*ρ) + ∇V` (`N:eq:velocity` with `g` replaced by `g_M`). -/
def movT_uReg (D : DynData d) (M : ℝ) (ρ : Torus d → ℝ) (x : Torus d) : Euc d :=
  D.invβ • Torus.grad (fun y => Real.log (ρ y)) x + Torus.grad (convFun (b15c_gReg d D.s M) ρ) x +
    Torus.grad D.V x

/-- The regularised commutator statistic `C^M_N = F_N^{h^M_{u^M}}`, `h^M_v(x,y) = (v(x)-v(y))·∇g_M(x-y)`. -/
def movT_commReg (D : DynData d) (N : ℕ) (M : ℝ) (ρ : Torus d → ℝ) (X : Config d N) : ℝ :=
  modulatedEnergy (commKernel (Torus.grad (b15c_gReg d D.s M)) (movT_uReg D M ρ)) X (withDensityReal ρ)

/-- **SPEC (sorried, L): MOV-A, the `ε`-level exact source identity** (Review 1, D5; ISSUES MOV item 3).  There is a
constant `C_ι` (depending on the trajectory data) such that for all levels `M ≥ 0`, `r ∈ [0,T]`, configurations `X`:
`S^M_r(X) = -βN(C^M_N(X) - E_{Q^M_r}[C^M_N]) + ι^M_r(X)` with `|ι^M_r(X)| ≤ C_ι N ‖g - g_M‖_{L¹}`
(the one-body remainders produced by `∂_tρ = κΔρ + div(ρ∇(V + g*ρ))` involving `g` while the dynamics uses `g_M`:
`∇(g_M*ρ) - ∇(g*ρ) = (g_M - g)*∇ρ`, `‖(g_M-g)*f‖_∞ ≤ ‖g_M-g‖_{L¹}‖f‖_∞`, plus the `E_{Q^M}` terms), and
`Lip(u^M_r) ≤ Lip(u_r) + C_ι‖g - g_M‖_{L¹}`.  Proof: the computation `Lψ + κ|∇ψ|² - ∂_tψ + E_q∂_tψ` of D3 for the tilt
`movT_phi`, the pair terms symmetrised exactly as in M L6436-6441 (`h^M_v` symmetric because `∇g_M` is odd), the mean-field
equation (a consequence of `IsMeanFieldSolution` + `IsC12Test`, `movT_isC12Test_of_weak`).  Routes packets
`movT_srcReg_tendsto` (with `movT_gReg_L1_tendsto` and the convergence `C^M_N → C_N` off collisions),
`movT_source_exp_uniform` and `movT_source_exp_scaled_uniform` (the pair part has the same envelope as `g_M`; the
remainder is `C N ‖g-g_M‖_{L¹} → 0`).

Repaired 2026-10-17, ISSUES MOVA: added `0 < T` (false at `T = 0`: `IsC12Test.time_deriv` is vacuous on `Ioo 0 0`, so `ρt 0` is
arbitrary). -/
theorem movT_srcReg_decomp (hN : 2 ≤ N) {D : DynData d} {T : ℝ} {ρ ρt : ℝ → Torus d → ℝ}
    (h : MovTraj D T ρ) (hρt : IsC12Test T ρ ρt) (hT : 0 < T) :
    ∃ Cι : ℝ, 0 ≤ Cι ∧ ∀ M : ℝ, 0 ≤ M → ∀ r ∈ Set.Icc 0 T,
      (∀ X : Config d N, |movT_srcReg D N M ρ ρt r X -
          (-(D.invβ⁻¹ * N) * (movT_commReg D N M (ρ r) X -
            ∫ Y, movT_commReg D N M (ρ r) Y ∂(movT_Q (b15c_gReg d D.s M) D N ρ r)))| ≤
        Cι * N * ∫ z : Torus d, |periodicRiesz d D.s z - b15c_gReg d D.s M z|) ∧
      ∀ L : ℝ, IsLipschitzVF L (mfeTransport D (ρ r)) →
        IsLipschitzVF (L + Cι * ∫ z : Torus d, |periodicRiesz d D.s z - b15c_gReg d D.s M z|)
          (movT_uReg D M (ρ r)) := by
  sorry

/-- **SPEC (sorried, M-L).**  Pointwise convergence of the regularised source to the exact source, off the
collision set: `S^{M_n}_r(X) → R_N^r(X)`.  This contains (i) the one-body remainders produced by `g_M*ρ - g*ρ`
(ISSUES MOV item 3: `∇g_M*ρ → ∇g*ρ` and `Δ(g_M*ρ) = g_M*Δρ → g*Δρ` uniformly, `ρ ∈ C²`), (ii) the
convergence of the drift `b15d_configDriftReg D M → ` physical drift at `X` (`b15c_liftedDriftReg_eq_of_sep`),
(iii) `E_{Q^M}[∂_tψ^M] → E_Q[∂_tψ]` (`movT_Q_tendsto_weak`, domination), and (iv) the exact identity `N:eq:source`
`Lψ + κ|∇ψ|² - ∂_tψ + E_Q∂_tψ = -βN(C_N(u;μ) - E_Q C_N(u;μ))` at the singular level (M L6429-6441: differentiate
`H:eq:modulated-gibbs`, insert `∂_tμ = Div(μu)` which follows from `IsMeanFieldSolution` + `IsC12Test`, integrate the
background terms by parts).  The identity is not written in the TeX beyond the sketch.

Repaired 2026-10-17, ISSUES MOVC: added `0 < T` (false at `T = 0`, same reason as `movT_srcReg_decomp`). -/
theorem movT_srcReg_tendsto (hN : 2 ≤ N) {D : DynData d} {T : ℝ} {ρ ρt : ℝ → Torus d → ℝ}
    (h : MovTraj D T ρ) (hρt : IsC12Test T ρ ρt) (hT : 0 < T) {M : ℕ → ℝ} (hM : Tendsto M atTop atTop) {r : ℝ}
    (hr : r ∈ Set.Icc 0 T) {X : Config d N} (hX : X ∉ collisionSet d N) :
    Tendsto (fun n => movT_srcReg D N (M n) ρ ρt r X) atTop (𝓝 (movT_source D N ρ r X)) := by
  sorry

/-- **SPEC (sorried, S).**  The regularised source is a continuous (hence Borel) function of the configuration
(composition of smooth functions: `g_M`, `φ^r ∈ C²`; the expectation term is a constant). -/
theorem movT_srcReg_measurable {D : DynData d} {T : ℝ} {ρ ρt : ℝ → Torus d → ℝ} (h : MovTraj D T ρ)
    (hρt : IsC12Test T ρ ρt) (M : ℝ) {r : ℝ} (hr : r ∈ Set.Icc 0 T) :
    Measurable (movT_srcReg D N M ρ ρt r) := by
  sorry

/-- **SPEC (sorried, L), `ε`-level moving-reference entropy inequality.**  For the regularised SDE
`dX = -∇U_M(X)dt + √(2/β) dW` with initial `H(f^M_0 | Q^M_0) < ∞`:
`H(f^M_t|Q^M_t) ≤ H(f^M_0|Q^M_0) + ∫_0^t∫S^M df^M_r dr`, the Fisher term dropped, all quantities finite.
Route: D3 `d3_entropy_moving` (`HRS/PDE/TorusFPEntropySpec.lean`) on `𝕋^{Nd}` with `U = b15d_U D M`,
`ψ^t = movT_psi`, `ℚ^M(μ^t) = d1_gibbsMeasure κ (U - κψ^t)` (`movT_phi` check) transported by
`d1_configEquiv`; `Law(X^M_t)` is the FP solution by D2 (`b15d_law_eq_fp`, from `d1_fp_exists`); the source
integrand is bounded; the TeX target is `N:eq:entropy-differential` (M L6452-6457), the form with the nonpositive Fisher
term retained is M L8569-8573.  `V ∈ C²` only: mollify `V_δ → V` in `C²` before the limit (B.15 packet E; the sources
converge uniformly on the compact torus). -/
theorem movT_reg_ineq {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (hN : 2 ≤ N) {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    (hW' : IsBrownianFiltration P ℱ W') {D : DynData d} {T : ℝ} {ρ ρt : ℝ → Torus d → ℝ}
    (htr : MovTraj D T ρ) (hρt : IsC12Test T ρ ρt) (M : ℝ) (hM : 0 ≤ M) {Y₀ : Ω → Fin N → Euc d}
    (hY₀ : ∀ t : ℝ, Measurable[ℱ t] Y₀) {Y : ℝ → Ω → (Fin N → Euc d)}
    (hY : IsAdditiveSDESolution P ℱ W' (fun _ => b15c_liftedDriftReg D M) (liftedNoise D) Y₀
      (fun _ => ⊤) Y)
    (hfin : relEntropy (selectedLaw P (b15c_regProcess Y) 0)
      (movT_Q (b15c_gReg d D.s M) D N ρ 0) ≠ ⊤) :
    ∀ t ∈ Set.Icc 0 T,
      relEntropy (selectedLaw P (b15c_regProcess Y) t) (movT_Q (b15c_gReg d D.s M) D N ρ t) ≠ ⊤ ∧
      (∀ r ∈ Set.Icc 0 t, Integrable (movT_srcReg D N M ρ ρt r) (selectedLaw P (b15c_regProcess Y) r)) ∧
      IntegrableOn (fun r => ∫ Z, movT_srcReg D N M ρ ρt r Z ∂(selectedLaw P (b15c_regProcess Y) r))
        (Set.Icc 0 t) ∧
      (relEntropy (selectedLaw P (b15c_regProcess Y) t) (movT_Q (b15c_gReg d D.s M) D N ρ t)).toReal ≤
        (relEntropy (selectedLaw P (b15c_regProcess Y) 0) (movT_Q (b15c_gReg d D.s M) D N ρ 0)).toReal +
        ∫ r in Set.Icc 0 t, ∫ Z, movT_srcReg D N M ρ ρt r Z ∂(selectedLaw P (b15c_regProcess Y) r) := by
  sorry

/-- **SPEC (sorried, L): GENUINE GAP (ISSUES MOV item 2).**  `ε`-uniform exponential bound for the regularised
source, at fixed `N`: there are `l > 0`, `C`, `M₀` with `E_{Q^M_r}[e^{l|S^M_r|}] ≤ e^C` for all `M ≥ M₀`, `r ∈ [0,T]`.
The TeX (`N:prop:pressure`, M L6118-6137, proof L6344-6406) covers the kernel `g - θh`, `|θ| ≤ θ₀`, for the *singular*
`g`; the regularised kernel `g_M = g - (g - g_M)` would be the case `θ = 1` (large), and monotonicity goes the wrong
direction.  Verified route (i), see header item 9: `g_M = g_L + q^M_0 - c_0` with `0 ≤ q^M_0 ≤ q_0` for
`M ≥ M₀`, so that `N:lem:weak-pressure` (L6271-6278), whose hypotheses are only the envelope `q ≤ A w` and the row bound
`a < a_0` (L6146-6154, "uses no positive-definiteness"), applies unchanged and uniformly in `M`; the
envelope `|h^M_{u+e}| ≤ C‖u+e‖_{C¹}(g_M + c)` is uniform; the one-body remainders are bounded by `C N ‖ι_M‖_∞`. -/
theorem movT_source_exp_uniform (hN : 2 ≤ N) {D : DynData d} {T : ℝ} {ρ ρt : ℝ → Torus d → ℝ}
    (htr : MovTraj D T ρ) (hρt : IsC12Test T ρ ρt) :
    ∃ l C M₀ : ℝ, 0 < l ∧ ∀ M : ℝ, M₀ ≤ M → ∀ r ∈ Set.Icc 0 T,
      ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (l * |movT_srcReg D N M ρ ρt r X|))
        ∂(movT_Q (b15c_gReg d D.s M) D N ρ r) ≤ ENNReal.ofReal (Real.exp C) := by
  sorry

/-- Law of the regularised process at time `0` is the law of `X₀` (`Y n 0 = Y₀` and `mk ∘ Y₀ = X₀` a.s.). -/
theorem movT_reg_init_law {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} {D : DynData d} {T : ℝ}
    {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    {M : ℕ → ℝ} {Y₀ : Ω → Fin N → Euc d} {Y : ℕ → ℝ → Ω → (Fin N → Euc d)}
    (seq : MovRegSeq P ℱ W' D T X₀ W X M Y₀ Y) (n : ℕ) :
    selectedLaw P (b15c_regProcess (Y n)) 0 = P.map X₀ := by
  unfold selectedLaw
  refine Measure.map_congr ?_
  filter_upwards [seq.init_lift] with ω hω
  rw [← hω]
  funext i
  simp [b15c_regProcess, projectPath, (seq.sol n).init ω]

/-! ### The `N`-uniform exponential bound for the exact source (from `perturbed_pressure`) -/

/-- **SPEC (sorried, M): `N:eq:source-exp` (M L6443-6450) with the `L(t)`-scaling of `P:eq:source-exp` (L6670).**
Uniformly over the data of `N:prop:pressure` (`s, β ∈ [βm,βp]`, `inf ρ ≥ c₀`, `‖ρ‖_{C²} ≤ Λ₂`; Review 1 D4: `C²` instead of
`C^∞` with all `Λ_k`, from `movT_pressure_two_sided_C2`) there are `l > 0`, `C`
such that for every `Lu > 0` with `u = β⁻¹∇log ρ + ∇g*ρ + ∇V` `Lu`-Lipschitz (the `L(t) = ‖∇u^t‖_∞` of the TeX), every
`N ≥ 2`: `C_N(u;μ)` is `Q_N`-integrable (so `E_{Q_N}[C_N]` in `movT_sourceAt` is non-junk) and
`log E_{Q_N}[e^{(l/Lu)|R_N|}] ≤ C N δ_N`.
Proof (from `perturbed_pressure`, `HRS/Energy/PressureProof.lean:821`, with `movT_pressure_two_sided_C2` in place of
`pressure_two_sided`, i.e. the `C²` version of its proof): `h = h_u/Lu` satisfies `|h| ≤ B w` with `B = B(d,s)`
(`commKernel_bound`, `HRS/Energy/Commutator/AbsConv.lean:42`, and `tdist^{-s} + 1 ≤ C(g + c_*)`), `h` symmetric and
measurable; `R = -β Lu N (F^h - E_Q F^h)`; `E_Q e^{θ₁N|F^h|} ≤ e^{CNδ_N}` and, by Jensen,
`N|E_Q F^h| ≤ (log E_Q e^{θ₁N|F^h|})/θ₁`; `l := θ₁/(2βp)`.  M L6413-6416 (commutator envelope), L6443-6450. -/
theorem movT_source_exp (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (βm βp : ℝ) (hβm : 0 < βm)
    (c₀ : ℝ) (hc₀ : 0 < c₀) (Λ₂ : ℝ) :
    ∃ l C : ℝ, 0 < l ∧ ∀ D : DynData d, D.s = s → D.invβ⁻¹ ∈ Set.Icc βm βp →
      ∀ ρ : Torus d → ℝ, IsProbDensity ρ → Torus.IsCk 2 ρ → (∀ x, c₀ ≤ ρ x) →
        Torus.cbNorm 2 ρ ≤ Λ₂ →
      ∀ Lu : ℝ, 0 < Lu → IsLipschitzVF Lu (mfeTransport D ρ) →
      ∀ N : ℕ, 2 ≤ N →
        Integrable (movT_commAt D N ρ)
          (modulatedGibbs (periodicRiesz d s) N D.invβ⁻¹ (withDensityReal ρ)) ∧
        ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp ((l / Lu) * |movT_sourceAt D N ρ X|))
          ∂(modulatedGibbs (periodicRiesz d s) N D.invβ⁻¹ (withDensityReal ρ)) ≤
        ENNReal.ofReal (Real.exp (C * N * deltaN d s N)) := by
  sorry


end HRS

end
