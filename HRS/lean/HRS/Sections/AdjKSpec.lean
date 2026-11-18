import HRS.Sections.Sec5
import HRS.Uniform.Q54Aux24
import HRS.Sections.Q40bAux2

/-!
# ADJK-SPEC: shared infrastructure ADJ-K for `dynamic_convergence` (Prop 5.4) and `moving_integrated_forcing` (Lemma 5.8)

Sorried SPECIFICATION statements (definitions carry no `sorry`).  The proved glue lives in `HRS/Sections/AdjKGlue.lean`
(imports this file).  TeX = `source/handoff/sources/HRS_periodic_main_20261008T010000Z.tex` (M).
Consumers: `dynamic_convergence` (Sec5.lean:311, TeX M L6096-6106, proof L6518-6519 "the trajectory conclusion is proved in
sec:finite-regularity" -- the TeX gives NO argument for tightness; the route below is the reconstruction) and
`moving_integrated_forcing` (Sec5.lean:418, TeX M L6651-6656 / L6719-6725, with L6587-6613 `P:eq:noneq-integrated`).

## Findings that change the packet (read first)

1. **The k-quantitative bounds on `∇U^{r,t}e_k` (task item (a)) are NOT on the critical path.**  The TeX consumers use the
   *operator* estimates of Lemma 3.27 (`‖V^{t,u}‖_{E_r→E_r} ≤ C_r e^{-c_r(t-u)}`, the maximal estimate for `∫V dM`), which the repo
   already has: `Uniform.evolution_estimates_proof` (HRS/Uniform/Q54Aux24.lean, all real `r`).  `adjk_evolution_along_trajectory`
   (PROVED, AdjKGlue) transports it to an `IsSmoothPositiveTrajectory`.  Per-mode bounds enter only through
   `‖∇e_k‖_∞ ≤ C|k|`, `‖e_k‖_{C²} ≤ Cλ_k²` (explicit functions) inside `moving_pair_moments` with `D = Cλ_k²`
   (TeX L6592-6596).  They are nevertheless specified (`adjk_adjoint_modes`, A1) as requested; A1 is the route-R2 input
   (martingale/forcing coordinates `∑_k λ_k^{-2m}|∫R(U^{·,t}e_k)|²` bounded mode by mode) and gives only `m > d/2 + a`
   with `a` the Sobolev index `j` of `adjoint_decay_comparison` (even `j > d/2+4`), i.e. thresholds `m > d + 5` or worse --
   which does NOT reach the TeX thresholds (`m > d+4` for 5.4, `m > d/2+2` for 5.8).  So route R1 (E_m-valued objects +
   operator bounds) is the one specified for the consumers; A1 is optional.
2. What the *time modulus* needs is the operator increment bound `‖V^{t,u}z - z‖_{E_{j+2}} ≤ C(t-u)‖z‖_{E_j}` (A2), the dual
   of `‖U^{u,t}φ-φ‖_{H^j} ≤ C(t-u)‖φ‖_{H^{j+2}}`.  This is new (not in the repo): the repo's `adjoint_torus_classical` gives
   `H^{m'}` bounds only with growth `e^{Λ(t-u)}`, and `adjoint_decay_comparison` only decay for even `j > d/2+4`.
3. The remainder `Rem_N = ∫V R dr` needs NO modulus: `E sup_t ‖Rem_N^t‖_{E_m} ≤ C B_N/√N → 0` (B2), because `hB : B_N/√N → 0`.
   Tightness is therefore needed only for `Lin(η_N^0)` (from `hlaw`) and the martingale convolution `Z_N` (B1, BCONV, KOLM, COMPACT).
4. Integer levels: `A2` is stated for integer levels `j ≥ d+2` (the repo's adjoint estimates are integer-indexed).  For
   `m > d+4` the choice `j = ⌊m⌋ - 2 ≥ d+2` has `j + 2 ≤ m`, so `‖·‖_{E_m} ≤ ‖·‖_{E_{j+2}}`; a real `m ∈ (d+4, d+5)` leaves no
   integer in `(d+2, m-2]`, so B2 (which needs level `> d+2`) is applied at a real level `m₂ ∈ (max(j,d+2), m)` (see `adjk_tight_of_components`).
5. The path-space conclusion of `dynamic_convergence` needs `AEMeasurable` of `flucPath`/`toPath` into the Borel σ-algebra of
   `PathSpace` (`TendstoInDistribution.forall_aemeasurable`); both are junk-defined (`0` path off the continuity event): packet M0.
6. Mathlib has `IsKolmogorovProcess` (the *condition* only; no Kolmogorov-Chentsov theorem), `IsTightMeasureSet`, Prokhorov
   (`isCompact_closure_of_isTightMeasureSet`, `isTightMeasureSet_of_isCompact_closure`), Arzelà-Ascoli (`Topology/UniformSpace/Ascoli`),
   `TendstoInDistribution` (+ Slutsky for a single sample space only).  No GRR/Aldous.

## Statement ↔ TeX ↔ consumer map

| declaration | TeX | consumer | size |
|---|---|---|---|
| `adjk_adjoint_modes` (A1) | M L6592-6596 (`‖∇e_k‖_∞≤C|k|`), L2531-2546 | OPTIONAL (not dispatched) | M |
| `adjk_evolution_increment` (A2) | M L2531-2546 + generator of `H:eq:backward-generator` | time modulus of `Z_N` (5.4) | L |
| `adjk_evolution_along_trajectory` (A3) PROVED | M L2531-2546 | 5.4, 5.8 | -- |
| `adjk_particle_martingale` (B0) | M L6571-6576 (`P:eq:martingale`, `P:eq:bracket`) | 5.4 | M |
| `adjk_evolution_moment` (B1) | M L2026-2045 (3.17 with `p>2`) + L2531-2546 | 5.4 | M |
| `adjk_conv_kolmogorov` (BCONV) | M L6587-6629 reconstruction | 5.4 | M-L |
| `adjk_mild_decomposition` (B3) | M L6564-6569 `P:eq:noneq-mild` | 5.4, 5.8 | L |
| `adjk_remainder_L1` (B2) | M L6598-6613 `P:eq:noneq-field`, `P:eq:noneq-integrated` | 5.4 | L |
| `adjk_forcing_intervalIntegrable` (C2) | M L6651-6656 (well-definedness) | 5.8 (conjunct 1), 5.4 (B2) | M |
| `adjk_det_convolution_L2` (C3) | M L6719-6725 | 5.8 (conjunct 2) | M |
| `adjk_compactSet_isCompact` (COMPACT) | -- (Arzelà-Ascoli + `H^{-m₂}⊂⊂H^{-m}`) | 5.4 | M |
| `adjk_kolmogorov_equicont` (KOLM) | -- (Kolmogorov-Chentsov, Billingsley 12.3) | 5.4 | L |
| `adjk_flucPath_aemeasurable`, `adjk_toPath_aemeasurable` (M0) | -- | 5.4 (`forall_aemeasurable`) | M |
| `adjk_convergence_of_tight_fidi` (F) | -- (Prokhorov + fidi uniqueness) | 5.4 | M-L |
| PROVED in AdjKGlue (standard axioms unless noted): `adjk_evolution_along_trajectory` (A3), `adjk_lin_along_trajectory` (+ `adjkLin`, `adjkLin_continuous`), `adjk_tight_of_tendstoInDistribution`, `adjk_tight_add`, `adjk_supTail_of_moment` (BCONV sup bound ⟹ `hsup`), `adjkEnergy_mono/_lsc/_measurable`, `PathSpace` Polish instances; `adjk_tight_of_tail_bounds`, `adjk_tight_of_components` (hold modulo COMPACT only) | | 5.4 | -- |
| NOT written (orchestrator glue "TAILS", S-M): `Ξ_n = Z_n + Rem_n` tail bounds from BCONV(1,2) + KOLM (`p=4,q=2`) + B2 (+ `adjkEnergy_mono`, triangle inequality), and `hid` from B3 | | 5.4 | S-M |

## Reviewer rulings (independent review of d1720e6) and MISSING PIECES
Rulings: (a) operator bounds (3.27) suffice, A1 is OPTIONAL and dropped from the dispatch plan; (b) `m > d+4 = (d+2)+2` is consistent with the TeX
(level `> d+2` for B2 plus the order-2 shift of A2); (c) the remainder needs no modulus, only a finite-`n` step for `hequi` (each fixed law is tight).
Sizes raised: BCONV M-L (lift of the `E_m` martingale to `E_j`, identification of the convolutions at the two levels, splitting
`Z_t = V^{t,s}Z_s + ∫_s^t V dM`); B1 M (exponent `p > 2` is not in the repo; use `hilbert_bdg`).  B1 now carries `AEMeasurable (Z t)` (as
`Q45.maximal_estimate_meas`): `IsStochConv` uses lower integrals, so it does not force measurability.
Glue items NOT in this packet, for `dynamic_convergence`:
1. measurable continuous version of `Z` (`gf_measurable_modification_proof` + `isStochConv_congr_ae`) -- S-M;
2. tail combination for `Ξ_n := Φ_n - Lin(η⁰_n)` (Minkowski for `√adjkEnergy` in `ℝ≥0∞`, Markov via B2, finite-`n` modulus, AEMeasurability of `Ξ_n`) -- M;
3. product extension `P ⊗ γ` so the Gaussian `G` lives on the same `Ω`, independent of `X₀` (transfer `IsParticleSystem`/`IsFilteredSolution`,
   enlarged filtration), or reuse the enlargement of `DynCmpAux4` -- M;
4. `smoothDist`-closeness plus a convergent family gives convergence in law; continuity of convolution with a fixed Gaussian -- M;
5. `linCoord (ρ⁰) (f_a⁰) (X₀) = eval (η⁰, f_a⁰)` via Fourier summability of `U^{0,t}φ` -- S;
6. `(Φ_n ω).at' t = η_N^t` a.s.; `toPath Y = Y` a.s. -- S;
7. the case `T = 0` -- S.
For `moving_integrated_forcing`: construct `R_r ∈ E_m` from coordinates (progressive, `0` for `r < 0`) -- M; identify `evolvingForcingCoord` with
`⟨∫V R, e_k⟩` (mode expansion, `eval` commuting with the Bochner integral) -- M; apply `moving_pair_moments` (`cstar`, `D = Cλ_k²`, `r = 2`), then C3 -- S.

## Packet plan (ADJ-K), order
1. A2 (L), then BCONV (M-L; uses A2, B1, `q14_covForm_trace`, `evolution_estimates_proof`), B1 (M).  Independent in parallel: COMPACT (M), KOLM (L).
2. B0 (M; a re-run of `gf_particle_martingale_proof` outside `GeneralSetup`), B3 (L; `dyncmp_ae_identity` +
   `DynCmpAux2` identification of `flucInteraction` with `-modulatedEnergy (commKernel ..)` + stochastic Fubini as `gf_pair_identification_proof`).
3. C2 (M), B2 (L: needs `E|R(e_k)| ≤ Cλ_k² B_N/√N` from `DynCmpAux2` `dyncmp_R_bound`-type estimate at `D = Cλ_k²`, then C3-type Minkowski), C3 (M).
4. M0 (M), F (M-L).
5. Orchestrator glue (not in this packet): `dynamic_convergence` = `adjk_convergence_of_tight_fidi` with `adjk_tight_of_components`
   (hypotheses from BCONV + KOLM + B2 + B3 + `hlaw`) and the fidi convergence of DynConvAux1 steps (a)-(b).
Total estimate: ~1500-2500 lines (A2 and KOLM dominate).  `adjk_evolution_along_trajectory` shows the existence side of A2/B1/B3 is not
vacuous (the dual evolution exists along every `IsSmoothPositiveTrajectory`, `K ≥ K₀(r)` supplied by `htr.global`).

## Doubts for the reviewer
* D1 (A2): `U^{u,t}φ - φ = ∫_u^t 𝓛_r U^{r,t}φ dr` pointwise is `IsClassicalAdjointSolution.time_deriv`; passing to `‖·‖_{H^j}` needs `‖U^{r,t}φ‖_{H^{j+2}} ≤ C‖φ‖_{H^{j+2}}` uniformly in `0 ≤ r ≤ t` WITHOUT growth.  The repo has this only through `adjoint_decay_comparison` (even `j > d/2+4`, projected by `Q_β`) or with `e^{Λ(t-r)}` (`adjoint_torus_classical`).  For `t - u ≥ 1` the claim follows from 3.27; for `t-u ≤ 1` the growth constant is harmless.  So A2 is true; the integer-level hypothesis `j ≥ d+2` and `mStar` are the only reasons for the restriction.
* D2 (thresholds): A1 with `a = j`: see Findings 1.  TeX `m > d+4` leaves slack `d/2` over what BCONV needs (`m ≥ j+2` with `j > d/2+2`); I did not find where `d+4` comes from (maybe `j > d/2+4` in `P:prop:adjoint` plus `m > d/2 + j`), so the reconstruction may be proving a stronger statement than the TeX's route.
* D3 (B3): the a.s. identity holds for all `t ∈ [0,T]` simultaneously only through a continuous version of `Z` (the Itô integral `M_N[U^{·,t}e_k]` is defined for each `t` separately); stated with the `IsStochConv` limit and continuity.
* D4 (KOLM): stated with Mathlib's `IsKolmogorovProcess` on `Set.Icc 0 T`, conclusion in outer measure (no measurability of the modulus event assumed).
* D5 (B2): uses `entropyScale` (= `B_N`) and the hypothesis `relEntropy ≠ ⊤` as in `dynamic_convergence`; the TeX derives `P:eq:pair-input` from `P:eq:entropy-input` (M L6546-6557); only `[0,T]` is needed here, not `sup_{t≥0}`.
* D6 (F): the finite-dimensional hypotheses use smooth tests `φ` and `NegSobolev.eval`; the pairing with `realMode k` recovers coordinates, so the cylinder σ-algebra is the Borel σ-algebra of `PathSpace` (separable).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS.AdjK

open HRS.Uniform

variable {d : ℕ} {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}

/-! ### Definitions (no `sorry`) -/

/-- The squared `E_{m₁}`-norm of an element `F ∈ E_m` (`‖F‖²_{E_{m₁}} = ∑_k ⟨k⟩^{-2m₁}|F̂(k)|²`, `F̂ = ⟨k⟩^m coord F`),
as an `ℝ≥0∞` number, `∞` if `F ∉ E_{m₁}` (so no `tsum` junk).  For `m₁ ≤ m'` it is antitone in `m₁` (`adjkEnergy_mono`). -/
def adjkEnergy (m₁ m : ℝ) (F : NegSobolev d m) : ℝ≥0∞ :=
  ∑' k : NonzeroLattice d, ENNReal.ofReal (Lattice.jp k.1 ^ (2 * (m - m₁)) * NegSobolev.coord F k ^ 2)

/-- The Arzelà-Ascoli set of paths in `C([0,T];E_m)` with `sup_t ‖w^t‖_{E_{m₁}} ≤ R` and modulus
`‖w^s - w^t‖_{E_m} ≤ 1/(j+1)` whenever `|s-t| ≤ δ_j`. -/
def adjkCompactSet (d : ℕ) (m T m₁ R : ℝ) (δ : ℕ → ℝ) : Set (PathSpace d m T) :=
  {w | (∀ t, adjkEnergy m₁ m (w.at' t) ≤ ENNReal.ofReal (R ^ 2)) ∧
    ∀ (j : ℕ) (s t : Set.Icc (0 : ℝ) T), |(s : ℝ) - t| ≤ δ j → ‖w.at' s - w.at' t‖ ≤ 1 / ((j : ℝ) + 1)}

/-- The rational times of `[a,b]` (countable supremum, as in `moving_integrated_forcing`). -/
def ratIcc (a b : ℝ) : Set ℝ := {t : ℝ | t ∈ Set.Icc a b ∧ ∃ q : ℚ, (q : ℝ) = t}

/-! ### A. Adjoint / evolution bounds -/

/-- **A1** (TeX M L6592-6596, L2531-2546; consumer: route R2 of 5.4/5.8, optional).  Quantitative-in-`k` bound of the
gradient of the adjoint evolution of the real Fourier mode `e_k`: polynomial in `⟨k⟩`, exponentially decaying, uniform in
all `0 ≤ r ≤ t` (not only `≤ T`).  `cbNorm 1` of the vector field `∇U^{r,t}e_k` is `‖∇U e_k‖_∞ + ‖∇²U e_k‖_∞`.  The first
conjunct says `U^{·,t}e_k` is the genuine classical solution (so the propagator is not the junk value `0`).  The exponent `a` is
existential (derivable from `adjoint_decay_comparison` with `a = j`, Findings 1).  Ingredients: `q40b_adjoint` (qualitative),
`exists_adjoint_decay_abstract`, `adjoint_decay_comparison`, `cbNorm_le_sobolevNorm`, `‖Q_β e_k‖_{H^j} ≤ C⟨k⟩^j`.  SPEC, size M. -/
theorem adjk_adjoint_modes (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) :
    ∃ C c a : ℝ, 0 ≤ C ∧ 0 < c ∧ 0 ≤ a ∧ ∀ k : NonzeroLattice d,
      (∀ t : ℝ, 0 ≤ t → ∃ F : ℝ → Torus d → ℝ,
        IsClassicalAdjointSolution htr.dyn ρ t (Torus.realMode k) F ∧
          ∀ r ∈ Set.Icc 0 t, propagator htr.dyn ρ r t (Torus.realMode k) = F r) ∧
      ∀ r t : ℝ, 0 ≤ r → r ≤ t →
        Torus.cbNorm 1 (Torus.grad (propagator htr.dyn ρ r t (Torus.realMode k))) ≤
          C * Lattice.jp k.1 ^ a * Real.exp (-c * (t - r)) := by
  sorry

/-- **A2** (consumer: time modulus of the stochastic convolution in 5.4; TeX: the generator `H:eq:backward-generator` of order 2
acts `H^{j+2} → H^j`).  Operator increment bound for the dual evolution `V^{t,u}` on `E_j`: embedded in `E_{j+2}`,
`‖V^{t,u}z - z‖_{E_{j+2}} ≤ C (t-u) ‖z‖_{E_j}` for all `0 ≤ u ≤ t` (no `T`), every dual evolution `V` (`IsDualEvolution`).
Dual to `‖U^{u,t}φ - φ‖_{H^j} ≤ C(t-u)‖φ‖_{H^{j+2}}`.  Integer level `j ≥ d+2`.  SPEC, size L. -/
theorem adjk_evolution_increment (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ)
    (j : ℕ) (hj : (d : ℝ) + 2 ≤ j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Vev : ℝ → ℝ → NegSobolev d (j : ℝ) →L[ℝ] NegSobolev d (j : ℝ),
      IsDualEvolution htr.dyn ρ (j : ℝ) Vev →
      ∀ u t : ℝ, 0 ≤ u → u ≤ t → ∀ z : NegSobolev d (j : ℝ),
        ‖NegSobolev.embed ((j : ℝ) + 2) (Vev t u z - z)‖ ≤ C * (t - u) * ‖z‖ := by
  sorry

/-! ### B. Martingale part -/

/-- **B0** (TeX M L6571-6576 `P:eq:martingale`, `P:eq:bracket`; consumer: 5.4).  The `E_n`-valued particle martingale
`𝓜_N^t = √N M_N^t` (`n > d/2+2`): a Hilbert martingale with covariation `covForm n β⁻¹ (μ_N^r)` whose pairing with a smooth test
`φ` is `√N` times the scalar empirical martingale `HRS.empiricalMartingale` (noise level `D.invβ = β⁻¹`).  A re-run of
`GF.gf_particle_martingale_proof` outside `GeneralSetup` (`σ_N = √N`, `q_N = β⁻¹`).  SPEC, size M. -/
theorem adjk_particle_martingale (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ)
    (n : ℝ) (hn : (d : ℝ) / 2 + 2 < n) (T : ℝ) (hT : 0 < T) {N : ℕ} (hN : 2 ≤ N)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (hX : IsParticleSystem P htr.dyn T X₀ W X) (ℱ : Filtration ℝ mΩ)
    (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (hF : IsFilteredSolution P ℱ W' W X) :
    ∃ M : ℝ → Ω → NegSobolev d n,
      IsHilbertMartingaleWithCovariation P ℱ T M
        (fun r ω => covForm n β⁻¹ (empirical (X r.toNNReal ω))) ∧
      ∀ φ : Torus d → ℝ, Torus.IsSmooth φ → ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P,
        NegSobolev.eval (M t ω) φ =
          Real.sqrt N * empiricalMartingale P ℱ W' htr.dyn T (fun _ => φ) X t ω := by
  sorry

/-- **B1** (TeX M L2026-2045 Lemma 3.17 with `p > 2`, applied to the evolution of L2531-2546; consumer: 5.4 Kolmogorov
moments).  The exponent-`p` version of the maximal estimate of `evolution_estimates` (3)  `P:eq:maximal`, along the
trajectory, for windows `[a,a+h]` of every length `0 < h ≤ T` with a constant chosen before `a`, `h` and the martingale:
`E sup_{a≤t≤a+h} ‖Z_t‖^p_{E_r} ≤ C E (∫_a^{a+h} Tr C_u du)^{p/2}`.  (`p = 2` is `evolution_estimates`, with `T`-dependent
constant.)  The evolution is the (unique) dual evolution of `adjk_evolution_along_trajectory`.  SPEC, size M. -/
theorem adjk_evolution_moment (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) (r p : ℝ)
    (hp : 2 ≤ p) :
    ∃ Vev : ℝ → ℝ → NegSobolev d r →L[ℝ] NegSobolev d r,
      IsDualEvolution htr.dyn ρ r Vev ∧ (∀ T : ℝ, 0 ≤ T → IsPlainEvolution Vev T) ∧
      ∀ T : ℝ, 0 < T → ∃ C : ℝ, 0 ≤ C ∧
        ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (ℱ : Filtration ℝ mΩ) (a h : ℝ), 0 ≤ a → 0 < h → h ≤ T →
          ∀ (M : ℝ → Ω → NegSobolev d r)
            (Sg : ℝ → Ω → (NegSobolev d r →L[ℝ] NegSobolev d r →L[ℝ] ℝ)),
            IsHilbertMartingaleWithCovariation P ℱ (a + h) M Sg →
            ∃ Z : ℝ → Ω → NegSobolev d r,
              (∀ t ∈ Set.Icc a (a + h),
                IsStochConv P Vev (ContinuousLinearMap.id ℝ (NegSobolev d r)) M a t (Z t)) ∧
              (∀ᵐ ω ∂P, ContinuousOn (fun t => Z t ω) (Set.Icc a (a + h))) ∧
              (∀ t ∈ Set.Icc a (a + h), AEMeasurable (Z t) P) ∧
              ∫⁻ ω, (⨆ t ∈ Set.Icc a (a + h), ‖Z t ω‖ₑ) ^ p ∂P ≤
                ENNReal.ofReal C * ∫⁻ ω,
                  (∫⁻ u in Set.Icc a (a + h), ENNReal.ofReal (traceNormForm (Sg u ω))) ^ (p / 2) ∂P := by
  sorry

/-- **BCONV** (reconstruction of the time-modulus input; consumer: 5.4).  Let `M` be any `E_m`-valued Hilbert martingale
whose covariation is `covForm m β⁻¹ (μ^r_ω)` for probability measures `μ^r_ω` (the empirical measures of the particle system;
`traceNormForm` is then bounded pathwise by `q14_covForm_trace`, uniformly in `μ`), `Vev` the dual evolution on `E_m`, and
`Z` a continuous stochastic convolution `∫_0^t V^{t,u} dM_u`.  For integer `j ≥ d+2` with `j + 2 ≤ m`:
`E sup_t ‖Z_t‖²_{E_j} ≤ C` (the `E_j`-norm of the `E_m`-valued `Z_t`, `adjkEnergy j m`, supremum over rational times) and the
Kolmogorov moments `E‖Z_t - Z_s‖⁴_{E_m} ≤ C|t-s|²` on `[0,T]`.  Proof: `Z_t - Z_s = (V^{t,s}-I)Z_s + ∫_s^t V^{t,u}dM_u`,
A2 (at level `j`) + B1 (`p = 4`, windows `h = t - s`) + trace bound.  The constant is chosen before `Ω, P, M, μ, Vev`.  SPEC, size M. -/
theorem adjk_conv_kolmogorov (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ)
    (j : ℕ) (hj : (d : ℝ) + 2 ≤ j) (m : ℝ) (hjm : (j : ℝ) + 2 ≤ m) (T : ℝ) (hT : 0 < T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (ℱ : Filtration ℝ mΩ) (μ : ℝ → Ω → Measure (Torus d)) (_ : ∀ r ω, IsProbabilityMeasure (μ r ω))
      (M : ℝ → Ω → NegSobolev d m),
      IsHilbertMartingaleWithCovariation P ℱ T M (fun r ω => covForm m β⁻¹ (μ r ω)) →
      ∀ Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m,
        IsDualEvolution htr.dyn ρ m Vev → (∀ T' : ℝ, 0 ≤ T' → IsPlainEvolution Vev T') →
        ∀ Z : ℝ → Ω → NegSobolev d m,
          (∀ t ∈ Set.Icc (0 : ℝ) T,
            IsStochConv P Vev (ContinuousLinearMap.id ℝ (NegSobolev d m)) M 0 t (Z t)) →
          (∀ᵐ ω ∂P, ContinuousOn (fun t => Z t ω) (Set.Icc 0 T)) → (∀ t, Measurable (Z t)) →
          ∫⁻ ω, ⨆ t ∈ ratIcc 0 T, adjkEnergy (j : ℝ) m (Z t ω) ∂P ≤ ENNReal.ofReal C ∧
          ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T,
            ∫⁻ ω, ‖Z t ω - Z s ω‖ₑ ^ (4 : ℝ) ∂P ≤ ENNReal.ofReal (C * |t - s| ^ 2) := by
  sorry

/-! ### C. Remainder (forcing) part -/

/-- **B3** (TeX M L6564-6569 `P:eq:noneq-mild`; consumer: 5.4, 5.8).  The mild identity in coordinates at level `m`: if
`M` is the particle martingale (covariation `covForm m β⁻¹ (μ_N^r)`, pairing `√N`·`empiricalMartingale`, as given by B0),
`Vev` the dual evolution on `E_m` and `Z` a continuous stochastic convolution of `M`, then almost surely for all
`t ∈ [0,T]` and all modes `k`:
`η_N^t(e_k) = (V^{t,0}η_N^0)(e_k) + Z_t(e_k) + evolvingForcingCoord k t` (`η_N^t = etaE m (X_t) (ρ^t)`,
`F̂(k) = fourierCoeff`).  The a.s.-for-all-`t` form needs the continuous version of `Z` (Doubts D3).  SPEC, size L. -/
/- Repaired 2026-10-17 (ISSUES "ADJKC"): added `hZm` (measurability of `Z t`); without it the statement is false
(`IsStochConv` uses lower integrals: Z' = Z + 1_A·v, A a Bernstein-type set). Same repair as `gf_pair_identification`. -/
theorem adjk_mild_decomposition (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ)
    (m : ℝ) (hm : (d : ℝ) / 2 + 2 < m) (T : ℝ) (hT : 0 < T) {N : ℕ} (hN : 2 ≤ N)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (hX : IsParticleSystem P htr.dyn T X₀ W X) (ℱ : Filtration ℝ mΩ)
    (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (hF : IsFilteredSolution P ℱ W' W X)
    (M : ℝ → Ω → NegSobolev d m)
    (hM : IsHilbertMartingaleWithCovariation P ℱ T M
      (fun r ω => covForm m β⁻¹ (empirical (X r.toNNReal ω))))
    (hMid : ∀ φ : Torus d → ℝ, Torus.IsSmooth φ → ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P,
      NegSobolev.eval (M t ω) φ =
        Real.sqrt N * empiricalMartingale P ℱ W' htr.dyn T (fun _ => φ) X t ω)
    (Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m) (hV : IsDualEvolution htr.dyn ρ m Vev)
    (Z : ℝ → Ω → NegSobolev d m)
    (hZ : ∀ t ∈ Set.Icc (0 : ℝ) T,
      IsStochConv P Vev (ContinuousLinearMap.id ℝ (NegSobolev d m)) M 0 t (Z t))
    (hZm : ∀ t ∈ Set.Icc (0 : ℝ) T, AEMeasurable (Z t) P)
    (hZc : ∀ᵐ ω ∂P, ContinuousOn (fun t => Z t ω) (Set.Icc 0 T)) :
    ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ k : NonzeroLattice d,
      NegSobolev.fourierCoeff (etaE m (X t.toNNReal ω) (withDensityReal (ρ t))) k =
        NegSobolev.fourierCoeff (Vev t 0 (etaE m (X 0 ω) (withDensityReal (ρ 0)))) k +
          NegSobolev.fourierCoeff (Z t ω) k + evolvingForcingCoord htr.dyn ρ X k t ω := by
  sorry

/-- **B2** (TeX M L6598-6613 `P:eq:noneq-field`, `P:eq:noneq-integrated` for `a = 0`; consumer: 5.4).  The summed `L¹`
remainder bound: for `m > d+2` (the sum `∑_k λ_k^{2-m} < ∞` of the TeX) there is `C` (chosen before `N` and the system) with
`E sup_{t∈[0,T]∩ℚ} ‖∫_0^t V^{t,r} R_N^r dr‖_{E_m} ≤ C B_N/√N`, written coordinatewise through `evolvingForcingCoord`
(`‖·‖_{E_m} = (∑_k ⟨k⟩^{-2m}|·_k|²)^{1/2}`, an `ℝ≥0∞` `tsum`, so no junk), together with the a.s. interval integrability that
makes the coordinates honest.  `B_N = entropyScale` and the entropy finiteness are the hypotheses of `dynamic_convergence`
(`hfin`).  Ingredients: `E|R_N^t(e_k)| ≤ C λ_k² B_N/√N` (TeX `P:eq:noneq-mode`, from the pair-entropy bound `P:eq:pair-input`
at `D = C λ_k²`), the E_m-valued `R` and the operator bound `‖V^{t,r}‖ ≤ C e^{-c(t-r)}` (A3).  SPEC, size L. -/
theorem adjk_remainder_L1 (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ)
    (m : ℝ) (hm : (d : ℝ) + 2 < m) (T : ℝ) (hT : 0 < T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        IsParticleSystem P htr.dyn T X₀ W X →
        (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ),
          IsFilteredSolution P ℱ W' W X) →
        relEntropy (P.map X₀)
          (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))) ≠ ⊤ →
        (∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ k : NonzeroLattice d,
          IntervalIntegrable (fun r =>
            Real.sqrt N * modulatedEnergy
              (commKernel (periodicRieszGrad d htr.dyn.s)
                (Torus.grad (propagator htr.dyn ρ r t (Torus.realMode k))))
              (X r.toNNReal ω) (withDensityReal (ρ r))) volume 0 t) ∧
        ∫⁻ ω, ⨆ t ∈ ratIcc 0 T, (∑' k : NonzeroLattice d,
            ENNReal.ofReal (Lattice.jp k.1 ^ (-2 * m) * evolvingForcingCoord htr.dyn ρ X k t ω ^ 2)) ^
              (1 / 2 : ℝ) ∂P ≤
          ENNReal.ofReal (C * entropyScale d s N (P.map X₀)
            (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))) / Real.sqrt N) := by
  sorry

/-- **C2** (TeX M L6651-6656 "well-definedness of the integrals"; consumer: 5.8 conjunct 1, and B2).  Joint measurability /
a.s. interval integrability of `r ↦ F^h(X_r, ρ^r)` for the time-dependent kernel `h = commKernel (∇g) (∇U^{r,t}e_k)`:
for a particle system on `[0,T']` for every `T'`, almost surely for all `t ≥ 0`, `k`, the function is interval integrable on `[0,t]`
(exactly the first conjunct of `moving_integrated_forcing`).  No entropy or moment hypothesis.  Proof idea: a.s. paths are
continuous and collision-free (`IsStrongSolution`), so on `[0,t]` the pair distances stay `≥ c > 0`; `r ↦ U^{r,t}e_k` is jointly `C²`
continuous (`IsClassicalAdjointSolution.cont_c2`) and `ρ` jointly continuous (`q40b_jointCont`), hence the integrand is continuous in
`r`.  Second field: joint measurability on `[0,t] × Ω` only (for `r < 0` the propagator is junk and `X` may be altered on null sets), as an
`AEMeasurable` for `volume|_{[0,t]} ⊗ P` (Fubini).  Stated for one horizon `T' ≥ t` with the filtered-solution hypothesis (as
`moving_integrated_forcing`), so that it feeds B2 / `dynamic_convergence` on `[0,T]`; the half-line version is `∀ T'`.  SPEC, size M. -/
theorem adjk_forcing_intervalIntegrable (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ)
    {N : ℕ} (hN : 2 ≤ N) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (T' : ℝ) (hT' : 0 ≤ T') (hX : IsParticleSystem P htr.dyn T' X₀ W X)
    (hF : ∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
      (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X) :
    (∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T', ∀ k : NonzeroLattice d,
      IntervalIntegrable (fun r =>
        Real.sqrt N * modulatedEnergy
          (commKernel (periodicRieszGrad d htr.dyn.s)
            (Torus.grad (propagator htr.dyn ρ r t (Torus.realMode k))))
          (X r.toNNReal ω) (withDensityReal (ρ r))) volume 0 t) ∧
    ∀ t ∈ Set.Icc (0 : ℝ) T', ∀ k : NonzeroLattice d,
      AEMeasurable (Function.uncurry fun (r : ℝ) (ω : Ω) =>
        Real.sqrt N * modulatedEnergy
          (commKernel (periodicRieszGrad d htr.dyn.s)
            (Torus.grad (propagator htr.dyn ρ r t (Torus.realMode k))))
          (X r.toNNReal ω) (withDensityReal (ρ r))) ((volume.restrict (Set.Icc 0 t)).prod P) := by
  sorry

/-- **C3** (TeX M L6719-6725: "Minkowski's inequality with the same decaying time weight as in `P:eq:noneq-integrated`";
consumer: 5.8 conjunct 2).  Abstract deterministic-convolution `L²` bound: if `Vev` is an evolution on `E_m` with
`‖V^{t,r}‖ ≤ C_V e^{-c(t-r)}` and `R : ℝ → Ω → E_m` is jointly measurable with `∫⁻ ‖R_r‖² ≤ b²` for every `r ≥ 0` (here
`R_N^r ∈ E_m` with `‖R_N^r‖²_{E_m} = ∑_k ⟨k⟩^{-2m}|R_N^r(e_k)|²`, `b = C J_N/√N`, by `moving_pair_moments` with `D = C⟨k⟩²`,
`m > d/2+2`), then for every `a ≥ 0`: `E sup_{t∈[a,a+T]∩ℚ} ‖∫_0^t V^{t,r}R_r dr‖² ≤ (C_V(1/c + T) b)²`.  Constants are chosen
before `a`, `b`, `Ω`, `R`.  The sup is over rational times.  The Bochner integral is a.s. not junk: `∫_0^t ‖R_r‖ dr < ∞` a.s. by Tonelli from
the second-moment hypothesis.  SPEC, size M. -/
theorem adjk_det_convolution_L2 (m : ℝ) (T CV c : ℝ) (hT : 0 < T) (hCV : 0 ≤ CV) (hc : 0 < c) :
    ∀ (Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m),
      (∀ u t : ℝ, 0 ≤ u → u ≤ t → ‖Vev t u‖ ≤ CV * Real.exp (-c * (t - u))) →
      ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (R : ℝ → Ω → NegSobolev d m), Measurable (Function.uncurry R) → ∀ b : ℝ, 0 ≤ b →
        (∀ r : ℝ, 0 ≤ r → ∫⁻ ω, ‖R r ω‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal (b ^ 2)) →
        ∀ a : ℝ, 0 ≤ a →
          ∫⁻ ω, (⨆ t ∈ ratIcc a (a + T),
              ‖∫ r in (0 : ℝ)..t, Vev t r (R r ω)‖ₑ) ^ 2 ∂P ≤
            ENNReal.ofReal ((CV * (1 / c + T) * b) ^ 2) := by
  sorry

/-! ### D. Tightness criteria (analysis) -/

/-- **COMPACT** (Arzelà-Ascoli + the compact embedding `E_{m₁} ⊂⊂ E_m`, `m₁ < m`; consumer: 5.4).  The set
`adjkCompactSet` of paths bounded in `E_{m₁}` with a prescribed modulus in `E_m` is compact in `C([0,T];E_m)`.  SPEC, size M. -/
theorem adjk_compactSet_isCompact (d : ℕ) (m T m₁ R : ℝ) (hm₁ : m₁ < m) (δ : ℕ → ℝ)
    (hδ : ∀ j, 0 < δ j) : IsCompact (adjkCompactSet d m T m₁ R δ) := by
  sorry

/-- **KOLM** (Kolmogorov-Chentsov / Billingsley Thm 12.3 tightness criterion; consumer: 5.4).  A family of continuous processes
on `[0,T]` with values in a Banach space satisfying a uniform Kolmogorov condition (`Mathlib.IsKolmogorovProcess`, exponents
`p > 0`, `q > 1`, constant `M`) is asymptotically equicontinuous in probability, uniformly in the index: for all `ε, η > 0`
there is `δ > 0` with `P_i(∃ s t, |s-t| ≤ δ, ‖Y_s - Y_t‖ > η) ≤ ε` for all `i` (outer measure, no measurability assumed).
Mathlib has only the definition of the condition.  SPEC, size L. -/
theorem adjk_kolmogorov_equicont {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (T : ℝ) (hT : 0 < T) (p q : ℝ) (hq : 1 < q) (M : ℝ≥0)
    {ι : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)] (P : ∀ i, Measure (Ω i))
    [∀ i, IsProbabilityMeasure (P i)] (Y : ∀ i, Set.Icc (0 : ℝ) T → Ω i → E)
    (hY : ∀ i, IsKolmogorovProcess (Y i) (P i) p q M)
    (hcont : ∀ i, ∀ᵐ ω ∂P i, Continuous fun t => Y i t ω) :
    ∀ ε η : ℝ, 0 < ε → 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ i,
      P i {ω | ∃ s t : Set.Icc (0 : ℝ) T, |(s : ℝ) - t| ≤ δ ∧ η < ‖Y i s ω - Y i t ω‖} ≤
        ENNReal.ofReal ε := by
  sorry

/-! ### E. Measurability of the path functionals and the final limit step -/

/-- **M0a** (consumer: 5.4 `TendstoInDistribution.forall_aemeasurable`).  `flucPath` (junk `0` off the continuity event) is
`AEMeasurable` into the Borel σ-algebra of `C([0,T];E_m)` for a particle system on `[0,T]` (a.s. continuous collision-free paths,
`m > d/2`, so `ofMeasureDiff` is the honest weighted sequence).  SPEC, size M. -/
theorem adjk_flucPath_aemeasurable (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ)
    (m : ℝ) (hm : (d : ℝ) / 2 < m) (T : ℝ) (hT : 0 ≤ T) {N : ℕ} (hN : 2 ≤ N)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (hX : IsParticleSystem P htr.dyn T X₀ W X) :
    AEMeasurable (fun ω => flucPath m T (Real.sqrt N) X ρ ω) P := by
  sorry

/-- **M0b** (consumer: 5.4, limit side).  `toPath` of a process with continuous paths a.s. and measurable marginals
(`IsLinearFluctuationSolution.cont/.meas`) is `AEMeasurable` into `PathSpace` (`E_m` separable). -/
theorem adjk_toPath_aemeasurable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (m T : ℝ)
    (Y : ℝ → Ω → NegSobolev d m) (hmeas : ∀ t, Measurable (Y t))
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun t => Y t ω) (Set.Icc 0 T)) :
    AEMeasurable (toPath m T Y) P := by
  sorry

/-- **F** (consumer: 5.4; the final limit step).  Tightness of the laws of `Φ_n ∈ C([0,T];E_m)` and convergence of all finite
dimensional laws `(⟨φ_a, Φ_n^{t_a}⟩)_a` (smooth tests `φ_a`, times in `[0,T]`) to those of `Ψ` give convergence in law on
`C([0,T];E_m)`: Prokhorov (`isCompact_closure_of_isTightMeasureSet`) + uniqueness of the law from the cylinder sets (coordinates
`⟨e_k,·⟩` are the pairings with `realMode k`).  SPEC, size M-L. -/
theorem adjk_convergence_of_tight_fidi (m T : ℝ) (hT : 0 ≤ T)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)] (Φ : ∀ n, Ω n → PathSpace d m T)
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Ψ : Ω' → PathSpace d m T) (hΦ : ∀ n, AEMeasurable (Φ n) (P n)) (hΨ : AEMeasurable Ψ P')
    (htight : IsTightMeasureSet (Set.range fun n => (P n).map (Φ n)))
    (hfidi : ∀ (p : ℕ) (ts : Fin p → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) T)
      (φ : Fin p → Torus d → ℝ), (∀ a, Torus.IsSmooth (φ a)) →
      TendstoInDistribution
        (fun n ω => (WithLp.toLp 2 fun a => NegSobolev.eval ((Φ n ω).at' ⟨ts a, hts a⟩) (φ a) :
          EuclideanSpace ℝ (Fin p)))
        atTop
        (fun ω' => (WithLp.toLp 2 fun a => NegSobolev.eval ((Ψ ω').at' ⟨ts a, hts a⟩) (φ a) :
          EuclideanSpace ℝ (Fin p)))
        P P') :
    TendstoInDistribution Φ atTop Ψ P P' := by
  sorry

end HRS.AdjK
