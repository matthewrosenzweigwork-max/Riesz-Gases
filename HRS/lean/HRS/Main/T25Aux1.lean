import HRS.Main.Headline
import HRS.PDE.MovFinalConsumers
import HRS.Sections.AdjKGlue

/-!
# T25-IN, part 1: statement check of Theorem 2.5, chain plan for the T25 assembly, and the BRIDGES (packet T25IN)

TeX (`source/handoff/sources/HRS_periodic_main_20261008T010000Z.tex`, "M"): Theorem 2.5 `H:thm:prepared` L766-801; proof
L6728-6767; inputs L6540-6657 (`P:eq:envelope`, `P:eq:entropy-input`, `P:eq:pair-input`, `P:eq:linear-input`,
`P:eq:noneq-mild` .. `P:eq:noneq-trace`); Lemma 5.8 `P:lem:moving-moments` L6658-6726; Proposition 3.28 `P:prop:comparison`.
Frozen statements: `HRS.Main.prepared_fluctuations`, `prepared_fluctuations_W2`, `prepared_scales`
(HRS/Main/Headline.lean:834/868/895).  This file: the statement check, the plan, and the PROVED bridges `t25_*` (below).

## 1. Statement check of the three frozen statements (result: NO statement defect found)

* Junk values.  `.toReal` is applied only to finite quantities: `S.initW .. ≠ ⊤` is a hypothesis of the first clause; `S.B` uses
  `(relEntropy ..).toReal` and the hypothesis is `relEntropy .. < ⊤`; `S.J` uses `(eLpNorm ..).toReal` and `MemLp` makes it finite
  (and `‖h‖_{L^{p₀}(Q)} ≥ 1`, `Q` a probability measure, so `log ≥ 0`, `J_N ≥ 1 + Nδ_N`).  `B_N/√N`, `(B_N/N)^{1/4}`: `N ≥ 2`, `B_N ≥ 2`.
  `δ_N` is the exact `H:eq:delta`.  `Nδ_N ≥ 1` (`one_le_mul_deltaN`).  `∃ C : ℝ` in `prepared_scales` has no sign constraint
  (harmless: the bound is between positive quantities).
* `T = 0`: excluded by `hT : 0 < T`; `a = 0` allowed (window = `[0,T]`).
* Measurability.  `S.etaLaw = law P (windowFluc ..)` and `law P' (windowPath ..)` are push-forwards: if the junk-defined window maps
  were not (AE)measurable the law would be the zero measure.  They are a.s. continuous (`SelectedFlow` + `IsStrongSolution.cont`;
  `IsLinearFluctuationSolution.cont`), and `Y t`, `X t` are measurable (`adapted`, `meas`); AEMeasurability of the `dite` is the
  packet M0 of AdjKSpec (`adjk_flucPath_aemeasurable`, `adjk_toPath_aemeasurable`, sorried there): a PROOF obligation, not a defect.
* `SelectedFlow` branch.  The second disjunct (Cépa-Lépingle, d = 1) is excluded by `S.hd : 2 ≤ d`, so `SelectedFlow ⇒
  IsParticleSystem` (`t25_isParticleSystem`).  `PreparedData` ⇒ `IsSmoothPositiveTrajectory` (`t25_traj`).
* Quantifier order.  `∃ C c` before `∀ a N P ..`; `C` depends on `(S, m, T)` and in the `W₂` clause on `p₀` only: as in the TeX
  ("independent of N and of the window start a"); the `W₂` constants are chosen after `p₀` (docstring AMBIGUITY).
* Third conjunct of `prepared_fluctuations` (spec flag 1: "initial term replaced by `C_T d₂^{E_m}(η_N^0, η°)`", TeX L781-782, no proof
  printed).  ASSESSMENT: TRUE and provable from Proposition 3.28 plus one new lemma; NOT a statement defect.  Proof: (a) apply
  `comparison_smooth_proof` with `X₀' := η_N^0` itself (the identity coupling, `ℱ_0`-measurable because it is a function of `X₀`):
  the initial term vanishes and the remaining terms are the ones of the first clause, so
  `d₂(η_N^{a+·}, Ȳ^{a+·}) ≤ C_T (B_N/√N + √(B_N/N))` for the linear process `Ȳ` started at `η_N^0`;
  (b) LIN-LAW (new, M): for two `IsPreparedLinear` solutions the window laws are `(V^{a+·,0})_* ν ⊛ γ_a` with the same centred
  Gaussian `γ_a` (the Gaussian part is independent of `Y₀` with `ν`-independent law, `IsLinearFluctuationSolution.gaussian_part`; law
  uniqueness = Prop A.33 / `gf_law_identification_proof` at level `m`), hence for `Φ ∈ C_b²(𝒳_{m,T})`,
  `Φ̃(x) = ∫Φ(V^{a+·,0}x + z)dγ_a(z)` is `C_b²(E_m)` with `‖Φ̃‖_{C_b²} ≤ max(1,K,K²)‖Φ‖_{C_b²}`, `K = sup_a‖V^{a+·,0}‖ ≤ C_m`
  (Lemma 3.27 decay), so `d₂(law Ȳ^{a+·}, law Y^{a+·}) ≤ C d₂^{E_m}(ν_N, ν)`; (c) triangle inequality.  (`smoothDist ≤ 2`, no
  moment hypotheses needed, which is why the third conjunct is unconditional in the statement.)

## 2. Findings that change the packet plan (read first)

F1 (HORIZON-UNIFORM ENTROPY; DONE here, `T25Aux2`/`T25Aux3`).  `P:eq:entropy-input` is `sup_{t≥0}`.  The proved `dynamic_entropy_proof'` /
`movT_entropy_bound_proof` have a constant `C(T') = e^{A T'} max(1, B_c T')` (Gronwall with the SUP Lipschitz bound; MovFinal1:116)
that grows with the horizon, so they cannot give a constant uniform in the window start `a` (the horizon is `a + T`).  The TeX uses
`∫_0^∞ L < ∞` (relaxation).  PROVED: `t25_gronwall_unif` (weighted Gronwall by Λ-blocks, constant `2^{⌈2AΛ₁⌉+1}`), `t25_entropy_Q`
(per-time `movT_source_exp_proof` with `Lu := L(r)`, `movspec_int_le`, `mov_ent_ineq_proof`, `MovLog.movlog_L`), `t25_product_bound`
(single-time copy of `dynent_product_bound`), `t25_entropy_uniform` (both entropies `≤ C B_N`, `C` independent of the horizon).
F2 (PAIR/LINEAR INPUT; DONE here, `T25Aux4`).  `t25_pair_entropy` (`movlog_expmoment` + `movspec_int_le`, kernel repaired on the
diagonal as in `movfin_movlog_pair_core`), `t25_pair_input` (`P:eq:pair-input` for the particle law), `t25_linear_input`
(`P:eq:linear-input`; `dyncmp_linear_entropy` = Hoeffding + Donsker-Varadhan).  NOTE `T25Aux4` imports `HRS.Sections.DynCmpAux3`, which no
other file imported (it was an unbuilt orphan; it compiles).
F3 (5.8 needs ALL horizons; DONE here, `T25Aux7`).  `moving_log_moment_proof'`, `moving_pair_moments_proof'` assume `∀ T,
IsParticleSystem P _ T ..`; `SelectedFlow` is only on `[0,a+T]`.  PROVED: `t25_moving_log_moment`, `t25_moving_pair_moments`
(text copies with the horizon bookkeeping changed, same constants, independent of `T`).
F4 (`GeneralSetup`/Theorem 2.1 packets are NOT reusable as is).  `HRS.GF.gf_*_proof` are for `GeneralSetup` (integer level `γ > 2d+10`,
`β_N` varying, energy-moment bounds); Theorem 2.5 is at real `m > d+2`.  The T25 chain must re-run those packets at level `m` along an
`IsSmoothPositiveTrajectory` (the ADJ-K packets B0, B3, B2 of `HRS/Sections/AdjKSpec.lean` are exactly the particle martingale / mild
decomposition / remainder at level `m`; B2 is for `a = 0, [0,T]` only, so an `a`-uniform version with `P:eq:noneq-integrated`'s
weight `e^{-c(a-r)_+}` and the horizon-uniform entropy (F1) is needed).  `adjk_evolution_along_trajectory` (PROVED glue) gives the
evolution `V` on `E_m`, decay `C e^{-c(t-u)}` and the maximal estimate (the hypothesis `MaxWindows` of `comparison_wasserstein`, for
`Ω : Type`) uniform in the window start `a`, for every real `m`.
F5 (flag 1, measure-theoretic half DONE, `T25Aux8`).  `t25_smoothDist_conv_le` (convolution with a fixed probability law does not
increase `d₂`: Fubini + `cbUnitBall_translate`) and `t25_smoothDist_affine_le`
(`d₂(Φ_*(ν⊗γ), Φ_*(ν'⊗γ)) ≤ max(1,‖L‖²) d₂(ν,ν')`, `Φ(x,z) = Lx + z`).  The remaining half is the law identification
`Law(Y^{a+·}) = Φ_*(ν⊗γ_a)` with `γ_a` the law of the stochastic convolution of the Gaussian martingale: it is the same
`gf_law_identification` at level `m` that clause 1 needs (item (6)), so clause 3 costs only the triangle inequality on top.

## 3. Chain plan for T25 (`prepared_fluctuations` and `_W2`), what is covered, what remains, sizes

Notation: `htr = t25_traj S`; `Vev` the dual evolution on `E_m` (`adjk_evolution_along_trajectory`, PROVED); `ν_N` the law of `η_N^0`.

(0) Bridges, DONE (`T25Aux1`, `T25Aux6`): `t25_traj`, `t25_dyn_eq`, `t25_isParticleSystem`, `t25_linear_of_prepared`, `t25_ref_eq`, `t25_B_eq`,
    `t25_movHyp` (`SelectedFlow` + filtered ⇒ `MovHyp` at the horizon), `t25_windowPath_eq` (`Main.windowPath = Uniform.windowPath a T`),
    `t25_windowFluc_eq` (`Main.windowFluc` = `Uniform.windowPath a T (GF.flucProc ..)`, `a ≥ 0`).
(1) Entropy input, horizon-uniform: `t25_entropy_uniform`.                                                          [DONE]
(2) `P:eq:pair-input`, `P:eq:linear-input`: `t25_pair_input`, `t25_linear_input`.                                   [DONE]
(3) `P:eq:noneq-mode/field/integrated` (summation over `k` with `D = Cλ_k²` from `movsx_hdom` and `L = d‖e_k‖_{C²}` (`dyncmp_lip_grad`),
    `‖e_k‖_{C²} ≤ Cλ_k²`; E_m-valued field `R_N^r`, Bochner integrability by Tonelli, `E sup_{a≤t≤a+T}‖∫V R‖ ≤ C_T B_N/√N` with the
    weight `e^{-c(a-r)_+}`; `t25_pair_input` gives `E|R^t(e_k)| ≤ Cλ_k² B_N/√N` for ALL `t ≤ a+T` with `C` independent of `a`):
    = ADJ-K B2 made `a`-uniform (+ C2 interval-integrability, + the `R_r ∈ E_m` construction).                       [L, T25-A]
(4) `P:eq:noneq-trace`: `E‖C_N^r − C̄^r‖_{𝔖₁(E_m)} ≤ C √(B_N/N)` from `t25_linear_input` applied to the entries `b = ∇e_k·∇e_l`
    (`‖b‖_∞ ≤ C|k||l|`) and the trace-norm series (`m > d+1`; a matrix unit has trace norm 1; agreement of the series with `covForm m q μ_N −
    covForm m q μ` on the Fourier core); needs a summability lemma `‖Q‖_{𝔖₁} ≤ ∑_{kl}|Q_{kl}|` for `traceNormForm`.   [M, T25-B]
(5) The mild identity at level `m` (ADJ-K B0 `adjk_particle_martingale` + B3 `adjk_mild_decomposition`, `duality_identity_final`):
    `η_N^t = V^{t,0}η_N^0 + Z_t + Rem_t` a.s. for all `t`, with continuous measurable versions (`gf_measurable_modification_proof`).
                                                                                                                     [L+L, T25-C, AdjKSpec]
(6) Initial coupling + Gaussian coupling at level `m`: `gf_init_enlargement_proof` re-run for real `m` and an arbitrary initial coupling of
    `(η_N^0, η°)` with `E‖η_N^0−η'‖ ≈ W_1` (ε-optimal coupling, then `ε→0`), independent of the Brownian noise (`condDistrib`
    enlargement; the TeX remark "the initial coupling is chosen before the particle Brownian motions"); `gf_adapted_coupling_trace`
    (Lemma 3.29, cost `‖Sg − Cb‖_{𝔖₁}`) and for `W_p` the polar coupling of Lemma 3.24/`hilbert_polar_coupling`; `gf_law_identification`
    at level `m` identifying `Law X̄ = Law Y` (IsPreparedLinear solution).                                          [L + L-XL, T25-D]
(7) Apply `comparison_smooth_proof` (`W_1`: `comparison_wasserstein_proof`, `p = 1`) with `K = C_m`, `c = c_m` (decay), `MaxWindows`
    from `adjk_evolution_along_trajectory`; weight `∫_0^{a+T} e^{-2c(a-r)_+}dr ≤ (2c)^{-1}+T`; remainder from (3), trace from (4); windows
    via `t25_windowPath_eq`, `t25_windowFluc_eq`.  Output: clause 1 (`H:eq:prepared-smooth`, `-W1`).                 [M glue, T25-E]
(8) Clause 3 (flag 1): `comparison_smooth_proof` with `X₀' := η_N^0` (initial term 0), then `t25_smoothDist_affine_le` +
    law identification (item (6)) + `smoothDist_triangle`.                                                          [M, T25-F]
(9) `prepared_fluctuations_W2`: `comparison_wasserstein_proof` with `p = 2` and `L²` remainder `‖R‖_{L²(C([a,a+T];E_m))} ≤ C J_N/√N`
    (`P:eq:L2-integrated`: `t25_moving_pair_moments` with `r = 2`, `D = Cλ_k²`, `m > d/2+2`; Minkowski with the weight = ADJ-K C3
    `adjk_det_convolution_L2`, sorried there) + the trace term `(B_N/N)^{1/4}` as in (4).  `t25_moving_log_moment` supplies
    `P:eq:log-moment` for the `J_N` hypothesis.                                                                     [M glue + M (C3), T25-G]
`prepared_scales`: DONE (`T25Aux5`, relocated `prepared_scales_proof` in `T25Final`, tied by `type_of%`).
Total for T25 beyond this packet: about 4-6k lines (dominated by (3), (5), (6)); (3), (5) are shared with ADJ-K, so doing ADJ-K first is
cheaper; (6) shares its law identification with ADJ-K's `dynamic_convergence` (`adjk_convergence_of_tight_fidi`).

## 3b. STATUS (T25P, final)

`prepared_fluctuations` and `prepared_fluctuations_W2` are PROVED (relocated): `prepared_fluctuations_proof`,
`prepared_fluctuations_W2_proof` in `HRS/Main/T25PFinal.lean` (tied to the frozen statements by `type_of%`; axioms: propext,
Classical.choice, Quot.sound).  Chain: `T25PAux1-21` (core estimate, law identification), `T25PAux22` (coupling enlargement),
`T25PAux23` (`hid` for window laws), `T25PAux24-25` (`t25p_prep`), `T25PAux26-27` (clause 1), `T25PAux28` (`W₂`),
`T25PAux29-33` (clause 3: uniqueness in law, re-basing, `t25_smoothDist_affine_le`, triangle inequality).

## 4. Sorry-free declarations of this packet (all `#print axioms` = propext, Classical.choice, Quot.sound)

T25Aux1: `t25_traj`, `t25_dyn_eq`, `t25_isParticleSystem`, `t25_linear_of_prepared`, `t25_ref_eq`, `t25_B_eq`.
T25Aux2: `t25_gronwall_unif` (+ `t25_block`, `t25_chain`).  T25Aux3: `t25_product_bound`, `t25_entropy_Q`, `t25_entropy_uniform`.
T25Aux4: `t25_pair_entropy`, `t25_pair_input`, `t25_linear_input`.  T25Aux5: `t25_prepared_scales` (+ `t25_press`, `t25_hpress`,
`t25_scales_entropy`, `t25_J_of_lintegral`, `t25_ratio_bound`, `t25_scales_ratio`, `t25_scales_log`).  T25Aux6: `t25_movHyp`,
`t25_windowPath_eq`, `t25_windowFluc_eq`.  T25Aux7: `t25_moving_log_moment`, `t25_moving_pair_moments`.  T25Aux8:
`t25_smoothDist_conv_le`, `t25_smoothDist_affine_le`.  T25Final: `prepared_scales_proof`.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

namespace T25

variable {d : ℕ}

open HRS.Main

/-- Bridge: the data `S` of Section 2.4 is an `IsSmoothPositiveTrajectory` (the global `H^K` solution for every `K`). -/
theorem t25_traj (S : PreparedData d) :
    IsSmoothPositiveTrajectory d S.s S.β S.V S.ρ0 S.ρ where
  hs0 := S.hs0
  hsd := S.hsd
  hβ := S.hβ
  V_smooth := S.hV
  init := S.hρ0
  global := fun K hK => by
    obtain ⟨ρc, h1, h2⟩ := S.hρ K hK
    exact ⟨ρc, h1, fun t _ => by rw [← h2]⟩

/-- The two dynamics data agree (they differ only by proof terms). -/
theorem t25_dyn_eq (S : PreparedData d) : (t25_traj S).dyn = S.dyn := rfl

/-- Bridge: a `SelectedFlow` of `S.dyn` is a `IsParticleSystem` (`d ≥ 2` excludes the Cépa-Lépingle branch). -/
theorem t25_isParticleSystem (S : PreparedData d) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {T : ℝ} {N : ℕ} {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {X : ℝ≥0 → Ω → Config d N} (h : SelectedFlow P S.dyn T X₀ W X) :
    IsParticleSystem P S.dyn T X₀ W X := by
  refine ⟨h.brownian, h.indep, ?_⟩
  rcases h.flow with ⟨hs, -⟩ | ⟨hd1, -⟩
  · exact hs
  · exact absurd hd1 (by have := S.hd; omega)

/-- Bridge: an `IsPreparedLinear` process is an `IsLinearFluctuationSolution` for the data of the trajectory. -/
theorem t25_linear_of_prepared (S : PreparedData d) {m T' : ℝ} {ν : Measure (NegSobolev d m)}
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} {Y₀ : Ω' → NegSobolev d m}
    {Y : ℝ → Ω' → NegSobolev d m} (h : IsPreparedLinear S m T' ν P' Y₀ Y) :
    IsLinearFluctuationSolution P' (t25_traj S).dyn S.ρ m (S.β)⁻¹ T' Y₀ Y := h.sol

/-- The reference measure `Q_N^t` of `PreparedData` is the modulated Gibbs measure of the trajectory. -/
theorem t25_ref_eq (S : PreparedData d) (N : ℕ) (t : ℝ) :
    S.refMeasure N t = modulatedGibbs (periodicRiesz d S.s) N S.β (withDensityReal (S.ρ t)) := rfl

/-- `B_N` of `PreparedData` is the `entropyScale` of Proposition 5.4. -/
theorem t25_B_eq (S : PreparedData d) (N : ℕ) (f0 : Measure (Config d N)) :
    S.B N f0 = entropyScale d S.s N f0 (modulatedGibbs (periodicRiesz d S.s) N S.β
      (withDensityReal (S.ρ 0))) := rfl

end T25

end HRS

end
