import HRS.MP.SelfSimSpec

/-!
# MP-P5PLAN: decomposition of packet P5 `ss_P5_entropy_cepa` (statement-only interface + proved assembly)

Target: `HRS.MP.SelfSim.ss_P5_entropy_cepa` (`HRS/MP/SelfSimSpec.lean:294`): the self-similar entropy inequality
`SSEntropyIneq 1 0 invβ N S P Y` for an ordered (Cépa-Lépingle) self-similar solution `Y` of
`dξ_i = ((1/N) ∑_{j≠i} 1/(ξ_i-ξ_j) - ξ_i/2) dτ + √(2 invβ) dW_i` on `ℝ` (`d = 1`, `s = 0`, so `a_0 ≡ 1` and the Gibbs
weight `Ḡ = exp(-Ū/invβ) 1_{Ω_N}`, `Ū = (1/N) ∑_{i<j} -log|ξ_i-ξ_j| + ¼|ξ|²`, is time independent).
This file contains the vocabulary (chamber coordinates on the line, a convex `C²` truncation of the logarithm, generic
Gibbs entropy / Fisher information / weak Fokker-Planck on `EuclideanSpace ℝ ι`), ten interface lemmas `ss5_*`
(statement only, `sorry`), and the assembly `ss_P5_entropy_cepa_proof` (statement verbatim, **proved** from the
interface lemmas), tied to the spec by `example := (@ss_P5_entropy_cepa_proof : type_of% @ss_P5_entropy_cepa)`.

## Verdict

`ss_P5_entropy_cepa` is true as stated; no statement defect found.  Points checked: (i) for `s = 0`,
`aSelfSim 0 τ = 1`, so `selfSimWeight 1 0 invβ N τ` does not depend on `τ` and no `∂_τŪ` term appears; (ii) `0 < Z_Ḡ < ∞`
on `ℝ^N` (the weight is `∏_{i<j}|ξ_i-ξ_j|^{1/(N invβ)} e^{-|ξ|²/(4 invβ)}` off the collision set, bounded near collisions
and Gaussian at infinity), so `gibbsEntropyW` is the unnormalised free energy `∫ f log f + ∫ Ū/invβ f`; (iii) the
permutation of `SSOrdered` is only `mΩ`-measurable, not `ℱ₀`-measurable; this is harmless because the conditioning is done
on the `ℱ₀`-events `A_σ = Y₀⁻¹(cone σ)`, on which the permutation is forced to be `σ` (`ssp1c_perm_unique`).

## Route (and the one structural change against the circle proof)

Port of `HRS.MC.CepH5Fin.cep_H5_entropy_confined_proof` (`HRS/MC/CepH5FinProof.lean:235`), with one simplification that
removes the whole existence chain E4-E7 of the circle: **on the line we compare the regularised flows directly with
the given solution `Y`**.  Regularise in chamber coordinates `z_k = ξ_{σ k}` (fixed label `σ`) by the explicit convex `C²`
truncation `φ_ε` of `-log` (`φ_ε = -log` on `[ε,∞)`, its second-order Taylor polynomial at `ε` on `(-∞,ε]`; `φ_ε'' ≤ ε⁻²`),
`Φ_ε(z) = (1/N)∑_{k<l} φ_ε(z_l-z_k)`, `U_ε = Φ_ε + ¼|z|²`.  `Φ_ε` is convex on all of `ℝ^N`, so for the regularised strong
solution `Z^ε` (same noise path) and `y = toCh_σ Y` the noise cancels and
`d/dt ½|Z^ε-y|² = -⟨∇Φ_ε(Z^ε)-∇Φ_ε(y), Z^ε-y⟩ - ⟨∇Φ_ε(y)-∇Φ(y), Z^ε-y⟩ - ½|Z^ε-y|² ≤ |∇Φ_ε(y)-∇Φ(y)| |Z^ε-y|`,
hence `sup_{[0,S]}|Z^ε-y| ≤ ∫_0^S |∇Φ_ε(y_r)-∇Φ(y_r)| dr → 0` by dominated convergence (`∇Φ_ε = ∇Φ` where all gaps
are `≥ ε`, `|φ_ε'(g)| ≤ 2/g`, the inverse gaps of `y` are integrable, `y ∈ C` for a.e. `r`).  This is a quantitative
version of the P1 uniqueness argument and replaces CepE4 (L¹ bound), E5a-c (Yosida-Cauchy), E6 (limit, "no reflection",
SUSPECT and 5.2k lines on the circle), E7, CepH4Id and CepU2.  The CepaPlan warning against the vertical truncation of
B.15 does not apply: `φ_ε` is one-sided in chamber coordinates (labels may cross for `Z^ε`, but the comparison only uses
global monotonicity of `∇Φ_ε`, and the limit is `Y` itself).  (The same shortcut would also work on the circle for B.14,
where the flow is given; it was not needed there.)

## Interface lemmas (size: S < 300, M 300-1000, L 1000-3000, XL > 3000 Lean lines)

1. **`ss5_mixture` (L, ~1200).**  Reduction to one order class: conditioning on `A_σ = Y₀⁻¹(cone σ)`, mixture of the laws,
   additivity of `gibbsEntropyW`/`fisherInfoW` over the `N!` open cones (finite entropy of the components at time `τ` gives
   `≪ vol` by P6, hence no mass on the collision set), finiteness of the component initial entropies, recombination.
   Port of the bookkeeping of `CepH5FinProof.lean` (`h5_coe_sum` :41, `h5_sum_ne_bot` :51, `h5_components_lt_top` :76,
   `h5_recombine` :108, assembly :235; verbatim, generic `EReal` lemmas) and of `cep_H0_component_additivity`
   (`HRS/MC/CepaSpec.lean:577`, proof `CepH0*.lean`, 696 lines; cyclic components of the torus become the cones, test fields
   split because the cones are clopen in `Ω_N`).  New: measurability of `r ↦ fisherInfoW Ḡ (law Y_r)` (sup of continuous
   functions of `r` by path continuity; replaces `h5_fisher_measurable_ck`).  Split: (1a) H0 on `ℝ^N` (M ~600),
   (1b) Fisher measurability in time (S ~250), (1c) bookkeeping (S ~350).  Dependencies: P6 (proved).
2. **`ss5_cond_solution` (M, ~350).**  `SSAddSol` and the ordering by the fixed `σ` survive conditioning on the `ℱ₀`-event
   `A_σ` (augment `ℱ` by the `cond P A_σ`-null sets; `W'` stays Brownian because `A_σ ∈ ℱ₀ ⊆ ℱ_s` is independent of the
   increments; no independence of `Y₀` and `W` is needed, unlike `h5_cond_brownian`).  Template: `h5_cond_filtered_proof`
   (`HRS/MC/CepH5FFilt.lean:91`, verbatim up to `IsWholeFilteredSolution`); `ssp1c_perm_unique`
   (`HRS/MP/SelfSimP1CepaUniq.lean:105`) forces the permutation.  Dependencies: none.
3. **`ss5_chamber_reading` (M, ~900).**  In chamber coordinates `y = toCh_σ Y`: the permuted noise `k ↦ W'(σ k, 0)` is a
   Brownian filtration (template `cepH2_noise_brownian`, `HRS/MC/CepH2Sde1.lean`, simpler for a fixed `σ`); `y₀` is
   `ℱ₀`-measurable with finite second moment (Gibbs variational inequality against `e^{a|ξ|²}`, `a < 1/(4 invβ)`; replaces
   `cepH2_moment_init`, whose cell support disappears); a.s. `y_r ∈ C` for a.e. `r` (null occupation + order), the inverse
   gaps `1/(y_l-y_k)` are integrable on `[0,S]` (triangular argument: the drift of the lowest particle is a sum of terms of
   one sign, and so on upwards), and `y` solves the chamber equation with drift `-∇Φ(y) - y/2` (drift formula
   `ssp1c_drift_apply`, `HRS/MP/SelfSimP1CepaUniq.lean:48`, plus `-ξ/2`; `rieszKernelGrad 1 0 u = -1/u`).  This is
   CepE1 on the line: the Lipschitz remainder `Ψ` of the circle is just `¼|z|²` (no `π cot` correction `ρ`, no `V`, no lift
   or lattice anchor).  Split: (3a) noise (S ~150), (3b) moment (M ~350), (3c) drift, occupation, gaps (M ~400).
4. **`ss5_trunc_props` (M, ~500).**  `U_ε` is `C²` (gluing of `-log` and its Taylor polynomial at `ε`, matching to order
   2), `∇U_ε` is Lipschitz (`φ_ε'' ≤ ε⁻²`), `U_ε ≥ c|z|² - C` (`φ_ε(g) ≥ -|g|` for `ε ≤ 1`), and `∇Φ_ε` is monotone (convexity
   of `φ_ε`).  Replaces CepE2/CepE2Props (Moreau-Yosida, ~2k lines on the circle): no prox, no Yosida inequality.
   Further facts used inside 6, 9, 10 (`Φ_ε = Φ` where all gaps `≥ ε`, `φ_ε ≤ φ_{ε'}` for `ε' ≤ ε`, `φ_ε ≤ -log` on
   `(0,∞)`, `φ_ε → +∞` on `(-∞,0)`, `|φ_ε'(g)| ≤ 2/g` on `(0,∞)`) are elementary calculus and belong to the same file.
5. **`ss5_regularised_sol` (S, ~200).**  Global adapted strong solution for a Lipschitz drift with additive noise on
   `EuclideanSpace ℝ ι`.  Template `cep_E3_regularised_sde_proof` (`HRS/MC/CepE3.lean`), `exists_sde_solution_global_nonneg`
   (`HRS/Stochastic/SDE.lean:1050`, shared build).
6. **`ss5_pathwise_conv` (M, ~450).**  The deterministic comparison above.  Reuses the pattern of `ssp1c_energy_nonpos`
   (`HRS/MP/SelfSimP1CepaUniq.lean:224`) and `ssp1c_sq_integral` (:202).  **Per-ω uniqueness shared with P1:** the
   identification needs no separate uniqueness theorem; `HRS.MP.SelfSimP1.ssp1c_unique` (:268) itself does not apply
   verbatim (its drift is the unconfined `particleDriftW`, and it is qualitative), but its monotonicity core
   `ssp1c_monotone_sum` (:149) is the convexity of `Φ` used here.  Dependencies: 4.
7. **`ss5_sde_weakFP` (L, ~1100; shareable with P4).**  For `dZ = -∇U(Z)dt + √(2θ)dB`, `U ∈ C²` with Lipschitz gradient:
   weak Fokker-Planck identity for the test class `ss5_Test` (bounded, `‖∇g‖(1+‖z‖)` and `∇²g` bounded), second moments
   on `[0,T]`, narrow continuity.  Port of `cepH2_weakFP_of_sde` (`HRS/MC/CepH2Sde2.lean`, `CepH2Sde3.lean`), `cepH2_moment_flow`
   (`CepH2Sde4-6.lean`), `cepH2_narrow_of_paths`; Itô `ito_formula_additive` (`HRS/Stochastic/Ito.lean:3632`), pattern of
   `ss_P3_fke_proof` (`HRS/MP/SelfSimP3.lean:292`).  Split: (7a) weak FP (M ~700), (7b) moments + narrow continuity (M ~400).
8. **`ss5_dissipation_core` (XL, ~3500; shareable with P4).**  Entropy dissipation for weak FP solutions with Lipschitz
   `∇U` and quadratic confinement on `ℝ^n`: the CepH2 route "mollify the law, not the equation" (`HRS/MC/CepH2Plan.md`,
   proved on the cylinder as `cepH2_core'`, `HRS/MC/CepH2Core3.lean:23`) without periodisation, fundamental cell or
   compactification of the cylinder (plain Gaussian mollifier, cut-off in all directions, second moments in all
   directions) and without freezing (`∇U_ε` is globally Lipschitz).  Split as in `HRS/MC/CepH2Spec.lean`: (8a) mollified
   dissipation inequality `F(u_t) + θ(1-δ)∫D ≤ F(u_0) + t K² n ε/(2δ)` (L ~1500: `CepH2Aux4,6,7,9-31` minus periodisation);
   (8b) initial Jensen bound (M ~400, `CepH2Init1-4`); (8c) lsc of entropy and Fisher information under mollification (M ~800,
   `CepH2Ent1-4`, `CepH2Fish1-3`, `CepH2Comp2-3`; DV on `ℝ^n` by the `tanh` embedding into a cube as in `CepH2Comp1`);
   (8d) Fatou, `δ → 0`, `EReal` bookkeeping (M ~400, `CepH2Core1-3`; `cepH2_core'` returns a dominating `D`, then
   `lintegral_mono`).  Dependencies: none.
9. **`ss5_initial_bound` (S, ~300).**  `𝓗_{U_ε}(toCh_σ#μ₀) ≤ 𝓗_Ḡ(μ₀)` for `μ₀` carried by `cone σ`: both entropies are
   unnormalised free energies, `toCh_σ` is a measure-preserving linear isometry, `Ḡ ∘ unrank_σ = e^{-U/θ}` on `C` and
   `U_ε ≤ U` there, and `klDiv` is antitone in an unnormalised reference.  (Simpler than CepH3 (c): no `limsup` of
   partition functions.)  Uses `0 < Z_Ḡ < ∞` (shared with P4, see below).
10. **`ss5_limit` (L, ~1500).**  `ε → 0`: Donsker-Varadhan lower semicontinuity with the moving references
   `e^{-U_ε/θ} dz ↑ e^{-U/θ} 1_C dz` (monotone in `ε` since `φ_ε` increases as `ε ↓ 0`; dominated convergence) under the a.s.
   convergence `Z^ε_t → y_t`; lsc of the Fisher functionals for test fields compactly supported in the cone (where
   `∇U_ε = ∇U` for small `ε`), Fatou in `r` (level-`ε` Fisher information is measurable in `r` by path continuity);
   initial term by 9; transport chamber → configuration space (`gibbsEntropyW`, `fisherInfoW` of `unrank_σ#ν` for `ν` on
   `C̄`).  Port of `cep_H3_limit_semicontinuity` (`HRS/MC/CepaSpec.lean:626`, proof `CepH3*.lean`, 3.6k lines on the
   circle incl. cell bijection and DV on a compact space).  Split: (10a) transport of entropy and Fisher information
   (M ~400), (10b) DV lsc with moving reference on `ℝ^N` (M ~600; template `cepH2_entropy_lsc`,
   `HRS/MC/CepH2Ent3.lean:37`, and `CepH2Mov1`), (10c) Fisher lsc, Fatou, `EReal` bookkeeping (M ~500, `CepH4Core.lean`).

**Assembly** (this file, proved): 1 reduces to one class; for a class `σ`: 2 → 3 → for each `n` (`ε_n = 1/(n+1)`):
4, 5 (regularised solution), 7 + 8 (level-`n` inequality; initial finiteness by 9), 6 (pathwise convergence, a.s. for all
`n` at once) → 10.

**Total** ≈ 10k lines; 7 + 8 (≈ 4.6k) are generic on `EuclideanSpace ℝ ι` and shareable with P4; P5-specific ≈ 5.4k
(the orchestrator's estimate of 5k for P5 assumed a share of the CepH2 transplant).

## Order of attack

4 and 6 first (deterministic, they validate the new identification route), then 2, 3, 5, 9 (routine), 1 (port), 7, 10,
and 8 last together with P4 (largest packet, main risk: integrability on `ℝ^n` in the mollified free-energy computation).

## Overlap with P4

P4's plan file (`HRS/MP/SelfSimP4Spec.lean`, branch `wk/mp_p4plan`) did not exist when this plan was written (branch at the
base commit).  P4 needs the same level-`M` dissipation inequality on `ℝ^{dN}` with quadratic confinement: for `s = 0` its
regularised potential is time independent and lemmas 7 + 8 apply verbatim with `ι = Fin N × Fin d` (after transporting
`EucConfig d N` to `EuclideanSpace ℝ (Fin N × Fin d)`); for `s > 0` P4 needs a time-dependent version with the extra
term `β ∫ ∂_τ Ū_M u ≤ 0`, of which 7 + 8 are the special case `∂_τ U = 0`: the two planners should state one generic
packet.  Also shared: `0 < Z_Ḡ < ∞` for `s = 0` (P4's "new lemma", used here in 3, 9, 10) and the DV lsc with a moving
reference on `ℝ^n` (10b; P4 step (3)).  P4's monotone truncation `g_M` of the kernel (symmetric, collision-free case) and
P5's one-sided chamber truncation `φ_ε` are different and must stay different (symmetric truncation lets labels cross
and loses the ordered law).

## Where the TeX is incomplete / where the circle proof used compactness

* TeX L10969 "so B.14 applies": B.14 (`M:B:prop:cepa-entropy-confined`) is a statement on `𝕋`; the line statement with
  `V = ξ²/4` (unbounded, `V'' = ½`) is not in the manuscript, nor are the order-class conditioning, the regularisation and
  the identification of the regularised limit with the given flow.
* Compactness used essentially by the circle chain, and its replacement here: `‖V''‖_∞ < ∞` from compactness
  (`Appendix/CepaFlow.lean:274`) — here `V'' = ½` exactly, absorbed into `U_ε`; bounded initial chamber points (`hz₀b` of
  E4-E6: sorted representatives in `[0,1)^N`) — not needed, E4-E6 are bypassed; DV lsc on a compact space
  (`b15b_klDiv_liminf_le`, `Appendix/B15BAux1.lean:82`, `[CompactSpace]`) — replaced by 8c/10b on `ℝ^n`; cell/fundamental
  domain of the cylinder and `Z_G = K Z_C` (CepH3 (a)) — not needed, the entropies are compared in unnormalised form;
  moments: from the quadratic confinement (3b, 7b) instead of compactness of the circle.
* No statement here is suspected false.  The only delicate analytic input is 8 (as for CepH2); the hypotheses `hnar`
  (narrow continuity) and the dominating-function form of the conclusion of `cepH2_core'` show what the proof needs; 8 is
  stated with `hnar` and 7 provides it.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.SelfSim
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MP.SelfSimP5

/-! ### Vocabulary: chamber coordinates on the line -/

/-- Chamber coordinates: `ℝ^N` with the Euclidean structure. -/
abbrev Ch5 (N : ℕ) := EuclideanSpace ℝ (Fin N)

/-- The open Weyl chamber `{z_0 < z_1 < ... < z_{N-1}}`. -/
def ss5_chamber (N : ℕ) : Set (Ch5 N) := {z | ∀ k l : Fin N, k < l → z k < z l}

/-- The open cone of configurations ordered by `σ`: `ξ_{σ 0} < ... < ξ_{σ(N-1)}`. -/
def ss5_cone {N : ℕ} (σ : Equiv.Perm (Fin N)) : Set (EucConfig 1 N) :=
  {ξ | ∀ k l : Fin N, k < l → ξ (σ k) 0 < ξ (σ l) 0}

/-- Rank (chamber) coordinates of a configuration for the label `σ`: `z_k = ξ_{σ k}`. -/
def ss5_toCh {N : ℕ} (σ : Equiv.Perm (Fin N)) (ξ : EucConfig 1 N) : Ch5 N :=
  WithLp.toLp 2 fun k => ξ (σ k) 0

/-- The chamber noise `k ↦ W'_{(σ k, 0)}`. -/
def ss5_chNoise {Ω : Type*} {N : ℕ} (σ : Equiv.Perm (Fin N)) (W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ) :
    ℝ≥0 → Ω → Fin N → ℝ :=
  fun t ζ k => W' t ζ (σ k, 0)

/-- The singular chamber potential `Φ(z) = (1/N) ∑_{k<l} -log(z_l - z_k)` (meaningful on the chamber). -/
def ss5_Phi (N : ℕ) (z : Ch5 N) : ℝ :=
  (1 / (N : ℝ)) * ∑ k : Fin N, ∑ l : Fin N, if k < l then -Real.log (z l - z k) else 0

/-- The convex `C²` truncation of `-log`: `-log g` for `g ≥ ε`, its second-order Taylor polynomial at `ε` below. -/
def ss5_phiTr (ε g : ℝ) : ℝ :=
  if ε ≤ g then -Real.log g else -Real.log ε - (g - ε) / ε + (g - ε) ^ 2 / (2 * ε ^ 2)

/-- The truncated chamber potential `Φ_ε(z) = (1/N) ∑_{k<l} φ_ε(z_l - z_k)` (convex on all of `ℝ^N`). -/
def ss5_PhiTr (N : ℕ) (ε : ℝ) (z : Ch5 N) : ℝ :=
  (1 / (N : ℝ)) * ∑ k : Fin N, ∑ l : Fin N, if k < l then ss5_phiTr ε (z l - z k) else 0

/-- The regularised self-similar potential `U_ε = Φ_ε + ¼|z|²`. -/
def ss5_U (N : ℕ) (ε : ℝ) (z : Ch5 N) : ℝ := ss5_PhiTr N ε z + (1 / 4 : ℝ) * ‖z‖ ^ 2

/-- The truncation levels `ε_n = 1/(n+1)`. -/
def ss5_eps (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem ss5_eps_pos (n : ℕ) : 0 < ss5_eps n := by
  unfold ss5_eps; positivity

theorem ss5_eps_le_one (n : ℕ) : ss5_eps n ≤ 1 := by
  unfold ss5_eps
  rw [div_le_one (by positivity)]
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

/-! ### Vocabulary: Gibbs entropy, Fisher information and weak Fokker-Planck on `EuclideanSpace ℝ ι` -/

section Generic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `Z_U = ∫ e^{-U/θ}`. -/
def ss5_partition (θ : ℝ) (U : EuclideanSpace ℝ ι → ℝ) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal (Real.exp (-U z / θ))

/-- The normalised Gibbs reference `Z_U⁻¹ e^{-U/θ} dz`. -/
def ss5_ref (θ : ℝ) (U : EuclideanSpace ℝ ι → ℝ) : Measure (EuclideanSpace ℝ ι) :=
  (ss5_partition θ U)⁻¹ •
    (volume : Measure (EuclideanSpace ℝ ι)).withDensity fun z => ENNReal.ofReal (Real.exp (-U z / θ))

/-- `𝓗_U(μ) = H(μ | Z_U⁻¹ e^{-U/θ} dz) - log Z_U` (the convention of `gibbsEntropyW`). -/
def ss5_ent (θ : ℝ) (U : EuclideanSpace ℝ ι → ℝ) (μ : Measure (EuclideanSpace ℝ ι)) : EReal :=
  ((relEntropy μ (ss5_ref θ U) : ℝ≥0∞) : EReal) - ((Real.log (ss5_partition θ U).toReal : ℝ) : EReal)

/-- Test fields of the Fisher information: smooth with compact support. -/
structure ss5_IsTestField (ζ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) : Prop where
  smooth : ContDiff ℝ ∞ ζ
  compact : HasCompactSupport ζ

/-- Divergence of a vector field on `EuclideanSpace ℝ ι`. -/
def ss5_div (ζ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) (z : EuclideanSpace ℝ ι) : ℝ :=
  ∑ k : ι, fderiv ℝ (fun w => ζ w k) z (EuclideanSpace.single k 1)

/-- `𝓘_U(μ) = sup_ζ ∫ (-2 div ζ + 2θ⁻¹⟨∇U, ζ⟩ - |ζ|²) dμ` over smooth compactly supported `ζ`. -/
def ss5_fish (θ : ℝ) (U : EuclideanSpace ℝ ι → ℝ) (μ : Measure (EuclideanSpace ℝ ι)) : ℝ≥0∞ :=
  ⨆ (ζ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) (_ : ss5_IsTestField ζ),
    ENNReal.ofReal (∫ z, (-2 * ss5_div ζ z + 2 * θ⁻¹ * inner ℝ (gradient U z) (ζ z) - ‖ζ z‖ ^ 2) ∂μ)

/-- Test functions of the weak Fokker-Planck equation (`CepH2` class `H2Test` without periodicity). -/
structure ss5_Test (g : EuclideanSpace ℝ ι → ℝ) : Prop where
  smooth : ContDiff ℝ 2 g
  bdd : ∃ C : ℝ, ∀ z, |g z| ≤ C ∧ ‖fderiv ℝ g z‖ * (1 + ‖z‖) ≤ C ∧ ‖fderiv ℝ (fderiv ℝ g) z‖ ≤ C

/-- The Laplacian. -/
def ss5_lap (g : EuclideanSpace ℝ ι → ℝ) (z : EuclideanSpace ℝ ι) : ℝ :=
  ∑ k : ι, fderiv ℝ (fderiv ℝ g) z (EuclideanSpace.single k 1) (EuclideanSpace.single k 1)

/-- The generator `θ Δ g - ⟨∇U, ∇g⟩` of `dZ = -∇U dt + √(2θ) dB`. -/
def ss5_gen (θ : ℝ) (U g : EuclideanSpace ℝ ι → ℝ) (z : EuclideanSpace ℝ ι) : ℝ :=
  θ * ss5_lap g z - inner ℝ (gradient U z) (gradient g z)

/-- Weak Fokker-Planck equation on `t ≥ 0`. -/
def ss5_WeakFP (θ : ℝ) (U : EuclideanSpace ℝ ι → ℝ) (μ : ℝ → Measure (EuclideanSpace ℝ ι)) : Prop :=
  ∀ g, ss5_Test g → ∀ t : ℝ, 0 ≤ t →
    ∫ z, g z ∂(μ t) = ∫ z, g z ∂(μ 0) + ∫ s in Icc (0 : ℝ) t, ∫ z, ss5_gen θ U g z ∂(μ s)

/-- `Z` is a continuous adapted solution of `dZ = b(Z) dt + √(2θ) dB` from `z₀`. -/
def ss5_IsSol {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) (ℱ : Filtration ℝ mΩ)
    (B : ℝ≥0 → Ω → ι → ℝ) (θ : ℝ) (b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (z₀ : Ω → EuclideanSpace ℝ ι) (Z : ℝ → Ω → EuclideanSpace ℝ ι) : Prop :=
  (∀ ζ, Continuous fun t => Z t ζ) ∧ (∀ t, 0 ≤ t → Measurable[ℱ t] (Z t)) ∧
    ∀ᵐ ζ ∂P, ∀ t : ℝ, 0 ≤ t → Z t ζ = z₀ ζ + (∫ s in (0 : ℝ)..t, b (Z s ζ)) +
      Real.sqrt (2 * θ) • WithLp.toLp 2 (B (Real.toNNReal t) ζ)

end Generic

/-! ### The interface lemmas -/

/-- **1 (mixture over the order classes, L).**  The self-similar entropy inequality for `P` follows from the
inequality for the conditional laws on the classes `A_σ = Y₀⁻¹(cone σ)` of positive probability and finite initial
entropy.  Port of the bookkeeping of `cep_H5_entropy_confined_proof` and of `cep_H0_component_additivity`. -/
theorem ss5_mixture (N : ℕ) (hN : 2 ≤ N) (invβ : ℝ) (hβ : 0 < invβ) (S : ℝ) (hS : 0 < S)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {Y : ℝ≥0 → Ω → EucConfig 1 N} (hYm : ∀ t, Measurable (Y t)) (hYc : ∀ ζ, Continuous fun t => Y t ζ)
    (hord : SSOrdered P S Y) (hdist : ∀ᵐ ζ ∂P, Y 0 ζ ∉ eucCollisionSet 1 N)
    (hH0 : gibbsEntropyW (selfSimWeight 1 0 invβ N 0) (law P (Y 0)) < ⊤)
    (hcomp : ∀ σ : Equiv.Perm (Fin N), P (Y 0 ⁻¹' ss5_cone σ) ≠ 0 →
      gibbsEntropyW (selfSimWeight 1 0 invβ N 0)
        (law (ProbabilityTheory.cond P (Y 0 ⁻¹' ss5_cone σ)) (Y 0)) < ⊤ →
      SSEntropyIneq 1 0 invβ N S (ProbabilityTheory.cond P (Y 0 ⁻¹' ss5_cone σ)) Y) :
    SSEntropyIneq 1 0 invβ N S P Y := by
  sorry

/-- **2 (conditioning on an order class, M).**  Under `cond P A_σ`, `Y` is again an `SSAddSol` (for an augmented
filtration), ordered by the fixed label `σ`, started in `cone σ`. -/
theorem ss5_cond_solution (N : ℕ) (hN : 2 ≤ N) (invβ : ℝ) (hβ : 0 < invβ) (S : ℝ) (hS : 0 < S)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ} {W : ℝ≥0 → Ω → (Fin N → Euc 1)}
    {Y : ℝ≥0 → Ω → EucConfig 1 N}
    (hY : SSAddSol P invβ (ssDrift 1 0 N) S ℱ W' W Y) (hord : SSOrdered P S Y)
    (σ : Equiv.Perm (Fin N)) (hA : P (Y 0 ⁻¹' ss5_cone σ) ≠ 0) :
    ∃ ℱ' : Filtration ℝ mΩ,
      SSAddSol (ProbabilityTheory.cond P (Y 0 ⁻¹' ss5_cone σ)) invβ (ssDrift 1 0 N) S ℱ' W' W Y ∧
      (∀ᵐ ζ ∂(ProbabilityTheory.cond P (Y 0 ⁻¹' ss5_cone σ)), ∀ t : ℝ≥0, (t : ℝ) ≤ S →
        ∀ k k' : Fin N, k ≤ k' → Y t ζ (σ k) 0 ≤ Y t ζ (σ k') 0) ∧
      (∀ᵐ ζ ∂(ProbabilityTheory.cond P (Y 0 ⁻¹' ss5_cone σ)), Y 0 ζ ∈ ss5_cone σ) := by
  sorry

/-- **3 (the solution in chamber coordinates, M).**  For one order class: Brownian chamber noise, `ℱ₀`-measurable
initial chamber point with finite second moment, and, almost surely, `y = toCh_σ Y` is continuous, lies in the open
chamber for a.e. time, has integrable inverse gaps, and solves `y_t = y_0 + ∫_0^t (-∇Φ(y) - y/2) + √(2 invβ) β_t`. -/
theorem ss5_chamber_reading (N : ℕ) (hN : 2 ≤ N) (invβ : ℝ) (hβ : 0 < invβ) (S : ℝ) (hS : 0 < S)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ} {W : ℝ≥0 → Ω → (Fin N → Euc 1)}
    {Y : ℝ≥0 → Ω → EucConfig 1 N}
    (hY : SSAddSol Q invβ (ssDrift 1 0 N) S ℱ W' W Y) (σ : Equiv.Perm (Fin N))
    (hord : ∀ᵐ ζ ∂Q, ∀ t : ℝ≥0, (t : ℝ) ≤ S → ∀ k k' : Fin N, k ≤ k' → Y t ζ (σ k) 0 ≤ Y t ζ (σ k') 0)
    (h0 : ∀ᵐ ζ ∂Q, Y 0 ζ ∈ ss5_cone σ)
    (hH0 : gibbsEntropyW (selfSimWeight 1 0 invβ N 0) (law Q (Y 0)) < ⊤) :
    IsBrownianFiltration Q ℱ (ss5_chNoise σ W') ∧
      Measurable[ℱ 0] (fun ζ => ss5_toCh σ (Y 0 ζ)) ∧
      ∫⁻ ζ, ENNReal.ofReal (‖ss5_toCh σ (Y 0 ζ)‖ ^ 2) ∂Q < ⊤ ∧
      (∀ ζ, Continuous fun r : ℝ => ss5_toCh σ (Y (Real.toNNReal r) ζ)) ∧
      ∀ᵐ ζ ∂Q,
        (∀ᵐ r ∂volume, r ∈ Icc (0 : ℝ) S → ss5_toCh σ (Y (Real.toNNReal r) ζ) ∈ ss5_chamber N) ∧
        (∀ k l : Fin N, k < l → IntegrableOn
          (fun r : ℝ => (ss5_toCh σ (Y (Real.toNNReal r) ζ) l - ss5_toCh σ (Y (Real.toNNReal r) ζ) k)⁻¹)
          (Icc (0 : ℝ) S)) ∧
        ∀ t ∈ Icc (0 : ℝ) S, ss5_toCh σ (Y (Real.toNNReal t) ζ) = ss5_toCh σ (Y 0 ζ) +
          (∫ r in (0 : ℝ)..t, (-(gradient (ss5_Phi N) (ss5_toCh σ (Y (Real.toNNReal r) ζ))) -
            (1 / 2 : ℝ) • ss5_toCh σ (Y (Real.toNNReal r) ζ))) +
          Real.sqrt (2 * invβ) • WithLp.toLp 2 (ss5_chNoise σ W' (Real.toNNReal t) ζ) := by
  sorry

/-- **4 (the truncated potential, M).**  `U_ε` is `C²` with Lipschitz gradient and quadratically confining, and
`∇Φ_ε` is monotone on all of `ℝ^N` (convexity of `φ_ε`). -/
theorem ss5_trunc_props (N : ℕ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ContDiff ℝ 2 (ss5_U N ε) ∧ (∃ K : ℝ≥0, LipschitzWith K (gradient (ss5_U N ε))) ∧
      (∃ c C : ℝ, 0 < c ∧ ∀ z, c * ‖z‖ ^ 2 - C ≤ ss5_U N ε z) ∧
      ∀ z z' : Ch5 N, 0 ≤ inner ℝ (gradient (ss5_PhiTr N ε) z - gradient (ss5_PhiTr N ε) z') (z - z') := by
  sorry

/-- **5 (regularised strong solutions, S).**  Global continuous adapted solution of `dZ = b(Z) dt + √(2θ) dB`, `b`
Lipschitz, started exactly at the `ℱ₀`-measurable `z₀`. -/
theorem ss5_regularised_sol {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {B : ℝ≥0 → Ω → ι → ℝ} (hB : IsBrownianFiltration P ℱ B)
    {θ : ℝ} (hθ : 0 < θ) {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {K : ℝ≥0} (hb : LipschitzWith K b)
    {z₀ : Ω → EuclideanSpace ℝ ι} (hz₀ : Measurable[ℱ 0] z₀) :
    ∃ Z : ℝ → Ω → EuclideanSpace ℝ ι, ss5_IsSol P ℱ B θ b z₀ Z ∧ ∀ ζ, Z 0 ζ = z₀ ζ := by
  sorry

/-- **6 (pathwise convergence of the regularised flows to the given flow, M; deterministic).**  If `y` solves the
singular chamber equation (in the chamber for a.e. time, integrable inverse gaps) and `z n` solve the `ε_n`-regularised
equations with the same initial point and the same noise path `w`, then `z n t → y t` on `[0,S]`. -/
theorem ss5_pathwise_conv {N : ℕ} {S : ℝ} (hS : 0 ≤ S) {y w : ℝ → Ch5 N} {y0 : Ch5 N}
    (hyc : Continuous y)
    (hyC : ∀ᵐ r ∂volume, r ∈ Icc (0 : ℝ) S → y r ∈ ss5_chamber N)
    (hgap : ∀ k l : Fin N, k < l → IntegrableOn (fun r : ℝ => (y r l - y r k)⁻¹) (Icc (0 : ℝ) S))
    (hy : ∀ t ∈ Icc (0 : ℝ) S,
      y t = y0 + (∫ r in (0 : ℝ)..t, (-(gradient (ss5_Phi N) (y r)) - (1 / 2 : ℝ) • y r)) + w t)
    {z : ℕ → ℝ → Ch5 N} (hzc : ∀ n, Continuous (z n))
    (hz : ∀ n, ∀ t ∈ Icc (0 : ℝ) S,
      z n t = y0 + (∫ r in (0 : ℝ)..t, -(gradient (ss5_U N (ss5_eps n)) (z n r))) + w t) :
    ∀ t ∈ Icc (0 : ℝ) S, Tendsto (fun n => z n t) atTop (𝓝 (y t)) := by
  sorry

/-- **7 (weak Fokker-Planck, moments and narrow continuity for a Lipschitz-gradient SDE, L; shareable with P4).** -/
theorem ss5_sde_weakFP {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {B : ℝ≥0 → Ω → ι → ℝ} (hB : IsBrownianFiltration P ℱ B)
    {U : EuclideanSpace ℝ ι → ℝ} (hU : ContDiff ℝ 2 U) {K : ℝ≥0} (hK : LipschitzWith K (gradient U))
    {θ : ℝ} (hθ : 0 < θ) {z₀ : Ω → EuclideanSpace ℝ ι} (hz₀ : Measurable[ℱ 0] z₀)
    (hm0 : ∫⁻ ζ, ENNReal.ofReal (‖z₀ ζ‖ ^ 2) ∂P < ⊤)
    {Z : ℝ → Ω → EuclideanSpace ℝ ι} (hZ : ss5_IsSol P ℱ B θ (fun z => -(gradient U z)) z₀ Z) :
    ss5_WeakFP θ U (fun t => P.map (Z t)) ∧
      (∀ T : ℝ, ∃ M : ℝ≥0∞, M < ⊤ ∧
        ∀ t ∈ Icc (0 : ℝ) T, ∫⁻ z, ENNReal.ofReal (‖z‖ ^ 2) ∂(P.map (Z t)) ≤ M) ∧
      ∀ g : EuclideanSpace ℝ ι → ℝ, Continuous g → (∃ C : ℝ, ∀ z, |g z| ≤ C) → ∀ T : ℝ,
        ContinuousOn (fun t => ∫ z, g z ∂(P.map (Z t))) (Icc (0 : ℝ) T) := by
  sorry

/-- **8 (entropy dissipation for weak Fokker-Planck solutions, Lipschitz `∇U`, quadratic confinement, XL; shareable
with P4).**  The CepH2 core (`cepH2_core'`) on `ℝ^n`. -/
theorem ss5_dissipation_core {ι : Type*} [Fintype ι] [DecidableEq ι] {U : EuclideanSpace ℝ ι → ℝ} (hU : ContDiff ℝ 2 U)
    {K : ℝ≥0} (hK : LipschitzWith K (gradient U)) (hconf : ∃ c C : ℝ, 0 < c ∧ ∀ z, c * ‖z‖ ^ 2 - C ≤ U z)
    {θ : ℝ} (hθ : 0 < θ) {μ : ℝ → Measure (EuclideanSpace ℝ ι)}
    (hprob : ∀ t, 0 ≤ t → IsProbabilityMeasure (μ t)) {T : ℝ} (hT : 0 ≤ T)
    (hmom : ∃ M : ℝ≥0∞, M < ⊤ ∧ ∀ t ∈ Icc (0 : ℝ) T, ∫⁻ z, ENNReal.ofReal (‖z‖ ^ 2) ∂(μ t) ≤ M)
    (hnar : ∀ g : EuclideanSpace ℝ ι → ℝ, Continuous g → (∃ C : ℝ, ∀ z, |g z| ≤ C) →
      ContinuousOn (fun t => ∫ z, g z ∂(μ t)) (Icc (0 : ℝ) T))
    (hfp : ss5_WeakFP θ U μ) (hfin : ss5_ent θ U (μ 0) < ⊤) :
    ∀ t ∈ Icc (0 : ℝ) T,
      ss5_ent θ U (μ t) + ((ENNReal.ofReal θ * ∫⁻ r in Icc (0 : ℝ) t, ss5_fish θ U (μ r) : ℝ≥0∞) : EReal)
        ≤ ss5_ent θ U (μ 0) := by
  sorry

/-- **9 (initial term, S).**  For `μ₀` carried by `cone σ`, the regularised chamber entropy of `toCh_σ#μ₀` is at most the
self-similar Gibbs entropy of `μ₀`. -/
theorem ss5_initial_bound (N : ℕ) (hN : 2 ≤ N) (invβ : ℝ) (hβ : 0 < invβ)
    {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q] (σ : Equiv.Perm (Fin N))
    {Y₀ : Ω → EucConfig 1 N} (hY₀ : Measurable Y₀) (h0 : ∀ᵐ ζ ∂Q, Y₀ ζ ∈ ss5_cone σ) {ε : ℝ} (hε : 0 < ε) :
    ss5_ent invβ (ss5_U N ε) (Q.map fun ζ => ss5_toCh σ (Y₀ ζ)) ≤
      gibbsEntropyW (selfSimWeight 1 0 invβ N 0) (law Q Y₀) := by
  sorry

/-- **10 (passage to the limit `ε → 0`, L).**  Lower semicontinuity of the entropy (moving references) and of the
Fisher information, initial term, transport to configuration space. -/
theorem ss5_limit (N : ℕ) (hN : 2 ≤ N) (invβ : ℝ) (hβ : 0 < invβ) (S : ℝ) (hS : 0 < S)
    {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q] (σ : Equiv.Perm (Fin N))
    {Y : ℝ≥0 → Ω → EucConfig 1 N} (hYm : ∀ t, Measurable (Y t))
    (hord : ∀ᵐ ζ ∂Q, ∀ t : ℝ≥0, (t : ℝ) ≤ S → ∀ k k' : Fin N, k ≤ k' → Y t ζ (σ k) 0 ≤ Y t ζ (σ k') 0)
    (h0 : ∀ᵐ ζ ∂Q, Y 0 ζ ∈ ss5_cone σ)
    {Z : ℕ → ℝ → Ω → Ch5 N} (hZc : ∀ n ζ, Continuous fun t => Z n t ζ)
    (hZm : ∀ n t, 0 ≤ t → Measurable (Z n t))
    (hZ0 : ∀ n, ∀ᵐ ζ ∂Q, Z n 0 ζ = ss5_toCh σ (Y 0 ζ))
    (hconv : ∀ᵐ ζ ∂Q, ∀ t ∈ Icc (0 : ℝ) S,
      Tendsto (fun n => Z n t ζ) atTop (𝓝 (ss5_toCh σ (Y (Real.toNNReal t) ζ))))
    (hdiss : ∀ n, ∀ t ∈ Icc (0 : ℝ) S,
      ss5_ent invβ (ss5_U N (ss5_eps n)) (Q.map (Z n t)) +
        ((ENNReal.ofReal invβ * ∫⁻ r in Icc (0 : ℝ) t,
          ss5_fish invβ (ss5_U N (ss5_eps n)) (Q.map (Z n r)) : ℝ≥0∞) : EReal)
        ≤ ss5_ent invβ (ss5_U N (ss5_eps n)) (Q.map (Z n 0))) :
    SSEntropyIneq 1 0 invβ N S Q Y := by
  sorry

/-! ### Assembly -/

theorem ss5_lip_neg {E : Type*} [NormedAddCommGroup E] {F : Type*} [PseudoMetricSpace F] {f : F → E}
    {K : ℝ≥0} (hf : LipschitzWith K f) : LipschitzWith K fun x => -f x :=
  LipschitzWith.of_dist_le_mul fun x y => by
    rw [dist_neg_neg]; exact hf.dist_le_mul x y

/-- **P5, assembly** (statement verbatim from `HRS.MP.SelfSim.ss_P5_entropy_cepa`; proved from the interface
lemmas 1-10). -/
theorem ss_P5_entropy_cepa_proof (N : ℕ) (hN : 2 ≤ N) (invβ : ℝ) (hβ : 0 < invβ) (S : ℝ) (hS : 0 < S)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ} {W : ℝ≥0 → Ω → (Fin N → Euc 1)}
    {Y : ℝ≥0 → Ω → EucConfig 1 N}
    (hY : SSAddSol P invβ (ssDrift 1 0 N) S ℱ W' W Y) (hord : SSOrdered P S Y)
    (hH0 : gibbsEntropyW (selfSimWeight 1 0 invβ N 0) (law P (Y 0)) < ⊤) :
    SSEntropyIneq 1 0 invβ N S P Y := by
  have hYm : ∀ t, Measurable (Y t) := fun t => (hY.filtered.adapted t).mono (ℱ.le _) le_rfl
  refine ss5_mixture N hN invβ hβ S hS P hYm hY.cont hord hY.init_distinct hH0 ?_
  intro σ hA hfin0
  set Q := ProbabilityTheory.cond P (Y 0 ⁻¹' ss5_cone σ) with hQ
  haveI : IsProbabilityMeasure Q := cond_isProbabilityMeasure_of_finite hA (measure_ne_top _ _)
  obtain ⟨ℱ', hYQ, hordQ, h0Q⟩ := ss5_cond_solution N hN invβ hβ S hS P hY hord σ hA
  obtain ⟨hBr, hz0m, hm0, hyc, hpath⟩ :=
    ss5_chamber_reading N hN invβ hβ S hS Q hYQ σ hordQ h0Q hfin0
  set z₀ : Ω → Ch5 N := fun ζ => ss5_toCh σ (Y 0 ζ) with hz₀
  -- the regularised strong solutions
  have hreg : ∀ n : ℕ, ∃ Zn : ℝ → Ω → Ch5 N,
      ss5_IsSol Q ℱ' (ss5_chNoise σ W') invβ (fun z => -(gradient (ss5_U N (ss5_eps n)) z)) z₀ Zn ∧
        ∀ ζ, Zn 0 ζ = z₀ ζ := by
    intro n
    obtain ⟨-, ⟨K, hK⟩, -, -⟩ := ss5_trunc_props N (ss5_eps_pos n) (ss5_eps_le_one n)
    exact ss5_regularised_sol hBr hβ (ss5_lip_neg hK) hz0m
  choose Z hZ hZ0 using hreg
  have hZm : ∀ n t, 0 ≤ t → Measurable (Z n t) := fun n t ht => ((hZ n).2.1 t ht).mono (ℱ'.le t) le_rfl
  -- the level-`n` entropy dissipation
  have hdiss : ∀ n, ∀ t ∈ Icc (0 : ℝ) S,
      ss5_ent invβ (ss5_U N (ss5_eps n)) (Q.map (Z n t)) +
        ((ENNReal.ofReal invβ * ∫⁻ r in Icc (0 : ℝ) t,
          ss5_fish invβ (ss5_U N (ss5_eps n)) (Q.map (Z n r)) : ℝ≥0∞) : EReal)
        ≤ ss5_ent invβ (ss5_U N (ss5_eps n)) (Q.map (Z n 0)) := by
    intro n
    obtain ⟨hC2, ⟨K, hK⟩, hconf, -⟩ := ss5_trunc_props N (ss5_eps_pos n) (ss5_eps_le_one n)
    obtain ⟨hfp, hmom, hnar⟩ := ss5_sde_weakFP hBr hC2 hK hβ hz0m hm0 (hZ n)
    have hprob : ∀ t, 0 ≤ t → IsProbabilityMeasure (Q.map (Z n t)) := fun t ht =>
      (Measure.isProbabilityMeasure_map_iff (hZm n t ht).aemeasurable).2 inferInstance
    have h0eq : Q.map (Z n 0) = Q.map z₀ := by
      congr 1; funext ζ; exact hZ0 n ζ
    have hfin : ss5_ent invβ (ss5_U N (ss5_eps n)) (Q.map (Z n 0)) < ⊤ := by
      rw [h0eq]
      exact lt_of_le_of_lt (ss5_initial_bound N hN invβ hβ Q σ (hYm 0) h0Q (ss5_eps_pos n)) hfin0
    exact ss5_dissipation_core hC2 hK hconf hβ hprob hS.le (hmom S) (fun g hg hb => hnar g hg hb S) hfp hfin
  -- pathwise convergence of the regularised flows
  have hconv : ∀ᵐ ζ ∂Q, ∀ t ∈ Icc (0 : ℝ) S,
      Tendsto (fun n => Z n t ζ) atTop (𝓝 (ss5_toCh σ (Y (Real.toNNReal t) ζ))) := by
    have hZae : ∀ᵐ ζ ∂Q, ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t → Z n t ζ = z₀ ζ +
        (∫ s in (0 : ℝ)..t, -(gradient (ss5_U N (ss5_eps n)) (Z n s ζ))) +
        Real.sqrt (2 * invβ) • WithLp.toLp 2 (ss5_chNoise σ W' (Real.toNNReal t) ζ) :=
      ae_all_iff.2 fun n => (hZ n).2.2
    filter_upwards [hpath, hZae] with ζ hζ hzeq
    obtain ⟨hyC, hgap, hyeq⟩ := hζ
    exact ss5_pathwise_conv (y := fun r => ss5_toCh σ (Y (Real.toNNReal r) ζ))
      (w := fun t => Real.sqrt (2 * invβ) • WithLp.toLp 2 (ss5_chNoise σ W' (Real.toNNReal t) ζ))
      (z := fun n t => Z n t ζ) hS.le (hyc ζ) hyC hgap hyeq (fun n => (hZ n).1 ζ)
      (fun n t ht => hzeq n t ht.1)
  exact ss5_limit N hN invβ hβ S hS Q σ hYm hordQ h0Q (fun n ζ => (hZ n).1 ζ) hZm
    (fun n => Filter.Eventually.of_forall fun ζ => hZ0 n ζ) hconv hdiss

example := (@ss_P5_entropy_cepa_proof : type_of% @HRS.MP.SelfSim.ss_P5_entropy_cepa)

end HRS.MP.SelfSimP5
