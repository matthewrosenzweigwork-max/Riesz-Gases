import HRS.Whole.AppendixALemmas
import HRS.Whole.AppendixA
import HRS.Main.TorusTheorems
import HRS.Stochastic.SelectedFlow
import HRS.Stochastic.Duality

/-!
# Appendix S.A (whole-space supplement), path-space lemmas and the selected-law remarks
(SPEC-WA2, second file)

Source: `HRS_whole_space_supplement_20261008T010000Z.tex` ("S"), Appendix S.A, Section
"Qualitative convergence on path space" and its neighbours:

* S.A.21 `B:lem:path-tightness-criterion`: `path_tightness_criterion` (in `AppendixALemmas.lean`);
* S.A.22 `B:lem:path-propagator-increment` (L10733-10755): `path_propagator_increment_torus`,
  `path_kernel_increment_torus`, `path_propagator_increment_rd`, `path_kernel_increment_rd`;
* S.A.23 `B:lem:path-initial-modulus` (L10794-10800): `path_initial_modulus_torus`,
  `path_initial_modulus_rd`, `path_initial_modulus_rd_limit` (and the Kolmogorov consequence
  `kolmogorov_modulus_tightness`);
* S.A.24 `B:lem:path-martingale-modulus` (L10827-10838): `path_martingale_modulus_torus`,
  `path_martingale_modulus_rd`;
* S.A.25 `B:lem:path-remainder` (L10861-10870): `path_remainder_torus`, `path_remainder_rd`;
* S.A.26 `B:lem:path-fidi` (L10884-10891): `path_fidi_torus`, `path_fidi_rd`;
* S.A.27 `B:cor:iid-init-path-rd` (L10903-10912): `iid_init_path_rd`;
* S.A.28 `B:cor:selected-law-selfsimilar` (L10931-10956): `selected_law_selfsimilar`;
* S.A.29 `B:rem:selfsimilar-initial-entropy` (L10958-10960): no formal content;
* S.A.30 `B:rem:selected-law-scope` (L10987-10989): no formal content.

## Representation decisions

* The whole-space data and assumptions are those of `HRS/Whole/AppendixA.lean` (`WholeMainData`,
  `RealizationRd`, `RdStanding`, `FieldDensityRd` (the index `Γ = fd.Gamma` links `Γ` and `m_0`: `H^{Γ+2}`
  embeds into the `C^{m_0+1}`-bounded functions), `InitialFluctuationRd`, `TransportedInitialFieldRd`,
  `CoeffConvergenceRd`, `WeightedPathInput`/`IsWeightedExtension`, `IsWholeFilteredSolution`, ...).  The only
  new assumption-level notions are `PathAdjointInput` / `LimitPathHyp` (the adjoint input two derivatives above
  the field theorem, for the particle sequence resp. a limiting coefficient), `IsInitReprRd` and
  `SelectedCommutatorInput`.
* **Fields on `ℝ^d` are random elements of `H^{-q}(ℝ^d)` (`HNeg d q`) *characterised by their pairings
  with the smooth tests*** `IsSobolevTest q` (a.s. at each fixed time), exactly as in `AppendixBField.lean`
  (S.B.2): the TeX defines `𝓘_{N,emp}^t, 𝓘_N^t, 𝕄_N^t, ℝ_N^t` by the functionals they extend, and the
  statements are for every such representative.  Time-indexed families are only defined a.s. for each
  fixed time; statements about paths (moduli, suprema, tightness) are made for *continuous versions*
  (`ContVersionTight`), as in the TeX ("continuous `H_q`-valued versions", S L10689, L10802).
* The stochastic convolution `𝕄_N^t` is a family of Itô integrals in the variable `r` for each fixed
  terminal time `t` (S L10778); it is represented by `HRS.itoIntegral` of the pairing integrand
  (`IsStochConvW`, `IsStochConvT`) on a Brownian filtration.
* The families are indexed by `N ≥ 1` (`R N` realizations); the limiting coefficients are a
  `LimitCoeffsRd` in a separate conjunct or theorem.  A WA definition that was not suitable is not used:
  `WeightedPathInput` bundles the limit and the particles, so for sequence-only statements the particle
  part (`PathAdjointInput.weighted`, i.e. `WeightedPathInput.particles`) is used directly.
* `q_T = γ + 2`, `q_R = Γ + 2` (S L10679-10682).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open HRS.Whole.AppendixA
open scoped ENNReal NNReal BigOperators ContDiff ComplexConjugate

namespace HRS.Whole.AppendixALemmas

variable {d : ℕ}

/-! ### Continuous versions with a uniform temporal modulus -/

/-- `Zc` is a family of *continuous versions* of the processes `Z_N` on `[0,T]` with a uniform temporal
modulus in probability, to which the tightness criterion `path_tightness_criterion` applies: for
`N ≥ 1` and `t ∈ [0,T]`, `Zc N t = Z N t` a.s.; `Zc N` has a.s. continuous paths on `[0,T]` and
measurable path map; for every `ε > 0`, `lim_{δ↓0} sup_N P(ω_E(Zc N, δ) > ε) = 0`; and if the
fixed-time marginals `{Z_N^t : N ≥ 1}` are tight in `E` for every `t ∈ [0,T]`, then the laws of the
paths `Zc N` are tight in `C([0,T]; E)`. -/
def ContVersionTight {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    (T : ℝ) {Ω : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)] (P : ∀ N, Measure (Ω N))
    (Z Zc : ∀ N, ℝ → Ω N → E) : Prop :=
  (∀ N : ℕ, 1 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ζ ∂(P N), Zc N t ζ = Z N t ζ) ∧
  (∀ N : ℕ, 1 ≤ N → ∀ᵐ ζ ∂(P N), Continuous fun t : Set.Icc (0 : ℝ) T => Zc N t ζ) ∧
  (∀ N : ℕ, 1 ≤ N → Measurable fun ζ => contPathOf T (fun t => Zc N t ζ)) ∧
  (∀ ε : ℝ, 0 < ε → Tendsto (fun δ : ℝ =>
      ⨆ N : ℕ, ⨆ (_ : 1 ≤ N), P N {ζ | ENNReal.ofReal ε < omegaE (fun t => Zc N t ζ) T δ})
    (𝓝[>] 0) (𝓝 0)) ∧
  ((∀ t ∈ Set.Icc (0 : ℝ) T, IsTightMeasureSet {μ | ∃ N : ℕ, 1 ≤ N ∧ μ = (P N).map (Z N t)}) →
    IsTightMeasureSet {μ | ∃ N : ℕ, 1 ≤ N ∧
      μ = (P N).map (fun ζ => contPathOf T (fun t => Zc N t ζ))})

/-- Kolmogorov's criterion in the form used in the proofs of S.A.23 and S.A.24 ("Kolmogorov's
criterion and fixed-time tightness give the last assertion", S L10823; "Kolmogorov's criterion gives a
modulus uniformly in `N`", S L10857): if `E‖Z_N^t - Z_N^s‖^p ≤ C|t-s|^{1+β}` (`p, β > 0`) uniformly in
`N ≥ 1`, `s, t ∈ [0,T]`, then the processes have continuous versions with a uniform temporal modulus
in probability and (by `path_tightness_criterion`) tight path laws whenever the fixed-time marginals
are tight.  (Used with `p = 2`, `β = 1` for `B:eq:path-initial-increments` and `p = 4`, `β = 1` for
`B:eq:path-martingale-fourth-torus`.)  Technical hypotheses: each `Z_N^t` is measurable (so the laws
are the true laws); `0 < T`. -/
theorem kolmogorov_modulus_tightness {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [TopologicalSpace.SeparableSpace E] [MeasurableSpace E] [BorelSpace E]
    (T : ℝ) (hT : 0 < T) {Ω : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)] (P : ∀ N, Measure (Ω N))
    [∀ N, IsProbabilityMeasure (P N)] (Z : ∀ N, ℝ → Ω N → E)
    (hZmeas : ∀ N : ℕ, 1 ≤ N → ∀ t, Measurable (Z N t)) (p β C : ℝ) (hp : 0 < p) (hβ : 0 < β)
    (hmom : ∀ N : ℕ, 1 ≤ N → ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∫⁻ ζ, ‖Z N t ζ - Z N s ζ‖ₑ ^ p ∂(P N) ≤ ENNReal.ofReal (C * |t - s| ^ (1 + β))) :
    ∃ Zc : ∀ N, ℝ → Ω N → E, ContVersionTight T P Z Zc := by
  sorry


/-! ### `B:lem:path-propagator-increment` (S.A.22) -/

/-- `q_T = γ + 2` (S L10679-10682), the torus path index (`γ = HRS.Main.gammaIdx d`). -/
def qT (d : ℕ) : ℕ := Main.gammaIdx d + 2

/-- Lemma S.A.22(i) (`S:B:lem:path-propagator-increment`, TeX S L10733-10741), torus: assume the adjoint
estimates and coefficient bounds two derivatives above the field theorem (`PDE.AdjointData` at the
level `γ + 2`, for every member `i` of a family of coefficients indexed by `ι`: the sequence in `N`
and/or the limiting coefficient, "the same estimates hold for the limiting propagator", S L10748).
Then for `0 ≤ r ≤ s ≤ t ≤ T` and `φ ∈ H^{q_T}(𝕋^d)`,
`‖U^{r,t}φ - U^{r,s}φ‖_{H^{q_T-2}} ≤ C|t-s|‖φ‖_{H^{q_T}}` (`B:eq:path-propagator-torus`); `C` depends only
on `d, s, Rg, ν₀, MB, Λ, VB, T`.
Technical hypothesis: `φ` continuous (`H^{q_T} ⊂ C²`; the classical adjoint solution needs a pointwise
datum).  The membership of the difference in `H^{q_T-2}` is part of the conclusion. -/
-- MP-STAT-REPAIRS (applied 2026-10-18 after the independent review of Chunk F): statement repaired; see ISSUES "MP: request MP-STAT-REPAIRS".
theorem path_propagator_increment_torus (s : ℝ) (Rg : PDE.Regime)
    (ν₀ MB Λ T VB νbar : ℝ) :
    ∃ C : ℝ, ∀ {ι : Type} (D : ι → DynData d) (ρ : ι → ℝ → Torus d → ℝ),
      (∀ i, PDE.AdjointData s (Main.gammaIdx d + 2) Rg MB Λ VB (D i) ν₀ T (ρ i)) →
      (∀ i, (D i).invβ ≤ νbar) →
      ∀ i : ι, ∀ r s' t : ℝ, 0 ≤ r → r ≤ s' → s' ≤ t → t ≤ T → ∀ φ : Torus d → ℝ,
        HRS.MemSobolev ((qT d : ℕ) : ℝ) φ → Continuous φ →
          HRS.MemSobolev ((qT d - 2 : ℕ) : ℝ) (fun x => propagator (D i) (ρ i) r t φ x -
              propagator (D i) (ρ i) r s' φ x) ∧
          HRS.sobolevNorm ((qT d - 2 : ℕ) : ℝ) (fun x => propagator (D i) (ρ i) r t φ x -
              propagator (D i) (ρ i) r s' φ x) ≤
            C * |t - s'| * HRS.sobolevNorm ((qT d : ℕ) : ℝ) φ := by
  sorry

/-- Lemma S.A.22, kernel part on the torus (TeX S L10752-10755): with the hypotheses of
`path_propagator_increment_torus`, let `K_{N,j;q}^{r,t}(x) ∈ H^{-q_T}(𝕋^d)` be the Riesz representative of
`φ ↦ ∂_jU^{r,t}φ(x)` on `H^{q_T}` (i.e. `⟨φ,K⟩ = ∂_jU^{r,t}φ(x)` for smooth mean-zero `φ`; the zero
mode is irrelevant since `U` fixes constants).  Then representatives exist, are unique, and
`‖K^{r,t}_{j;q}(x) - K^{r,s}_{j;q}(x)‖_{H^{-q_T}} ≤ C|t-s|` (`B:eq:path-kernel-increment`, indicator of
`ℝ^d` zero on the torus) and `sup ‖K^{r,t}_{j;q}(x)‖_{H^{-q_T}} ≤ C`. -/
-- MP-STAT-REPAIRS (applied 2026-10-18 after the independent review of Chunk F): statement repaired; see ISSUES "MP: request MP-STAT-REPAIRS".
theorem path_kernel_increment_torus (s : ℝ) (Rg : PDE.Regime)
    (ν₀ MB Λ T VB νbar : ℝ) :
    ∃ C : ℝ, ∀ {ι : Type} (D : ι → DynData d) (ρ : ι → ℝ → Torus d → ℝ),
      (∀ i, PDE.AdjointData s (Main.gammaIdx d + 2) Rg MB Λ VB (D i) ν₀ T (ρ i)) →
      (∀ i, (D i).invβ ≤ νbar) →
      (∀ i : ι, ∀ (j : Fin d) (r t : ℝ), 0 ≤ r → r ≤ t → t ≤ T → ∀ x : Torus d,
        ∃! k : NegSobolev d ((qT d : ℕ) : ℝ), ∀ φ : Torus d → ℝ, Torus.IsSmooth φ →
          Torus.mean φ = 0 → NegSobolev.eval k φ = (Torus.grad (propagator (D i) (ρ i) r t φ) x) j) ∧
      ∀ Kern : ι → Fin d → ℝ → ℝ → Torus d → NegSobolev d ((qT d : ℕ) : ℝ),
        (∀ i : ι, ∀ (j : Fin d) (r t : ℝ), 0 ≤ r → r ≤ t → t ≤ T → ∀ x : Torus d,
          ∀ φ : Torus d → ℝ, Torus.IsSmooth φ → Torus.mean φ = 0 →
            NegSobolev.eval (Kern i j r t x) φ = (Torus.grad (propagator (D i) (ρ i) r t φ) x) j) →
        ∀ i : ι, ∀ (j : Fin d) (r s' t : ℝ), 0 ≤ r → r ≤ s' → s' ≤ t → t ≤ T → ∀ x : Torus d,
          ‖Kern i j r t x - Kern i j r s' x‖ ≤ C * |t - s'| ∧ ‖Kern i j r t x‖ ≤ C := by
  sorry

/-- The coefficients' path-level adjoint input (S L10733-10735, S L9987-10002) for the sequence: the adjoint
estimates through order `m_0 + 1` at the level `q_R = Γ + 2` (`AdjointDerivInput`, constant `Kadj`) and
`B:ass:rd-path-weighted` for the particle propagators (`IsWeightedExtension`, `k = m_0 + 1`, constant `Cw`; the
limiting propagator is covered by `LimitPathHyp`). -/
structure PathAdjointInput (S : WholeMainData d) (Γ m₀ : ℕ) (Kadj Cw : ℝ) : Prop where
  adjoint : AdjointDerivInput ((Γ + 2 : ℕ) : ℝ) (m₀ + 1) S.coeff S.T Kadj
  weighted : ∀ N : ℕ, 1 ≤ N → ∃ U, IsWeightedExtension (S.coeff N) (m₀ + 1) (Γ + 2) S.T Cw U

/-- The path-level hypotheses on a limiting coefficient `L` (S L10748 "the same estimates hold for the limiting
propagator"; the limiting equation of `B:cor:true-limit`): the selected regime holds for the limit; the limit
trajectory solves the whole-space mean-field equation with datum `μ°` and is `(Γ+5, Λ)`-regular (`CoeffHypRd`,
`m = Γ + 2`); the adjoint input at the level `Γ + 2` (order `m_0 + 1`) and `B:ass:rd-path-weighted` hold for the
limiting propagator. -/
structure LimitPathHyp (S : WholeMainData d) (L : LimitCoeffsRd d) {s : ℝ} (fd : FieldDensityRd d s)
    (ν₀ Λ Kadj Cw : ℝ) (m₀ : ℕ) : Prop where
  regime : fd.HoldsAt S.s S.M L.invβ ν₀
  solution : IsWholeMeanFieldSolution (L.dyn S) S.T L.ρ
  datum : withDensityReal (L.ρ 0) = S.μ0
  coeff : CoeffHypRd S.s (fd.Gamma + 2) Λ S.T L.ρ
  adjoint : AdjointInputOneD ((fd.Gamma + 2 : ℕ) : ℝ) (m₀ + 1) (L.coeff S) S.T Kadj
  weighted : ∃ U, IsWeightedExtension (L.coeff S) (m₀ + 1) (fd.Gamma + 2) S.T Cw U

/-- The increment bound `B:eq:path-propagator-rd` for one coefficient `Cf`: for `0 ≤ r ≤ s ≤ t ≤ T`, smooth
`φ ∈ H^{q}(ℝ^d)` and `|α| ≤ m_0 + 1` (iterated partial derivatives),
`|∂^α(U^{r,t}φ - U^{r,s}φ)(x)| ≤ C|t-s|⟨x⟩‖φ‖_{H^q}`. -/
def IncrementBoundRd (Cf : WholeCoeff d) (T : ℝ) (q m₀ : ℕ) (C : ℝ) : Prop :=
  ∀ r s' t : ℝ, 0 ≤ r → r ≤ s' → s' ≤ t → t ≤ T → ∀ φ : Euc d → ℝ, IsSobolevTest (q : ℝ) φ →
    ∀ l ≤ m₀ + 1, ∀ (idx : Fin l → Fin d) (x : Euc d),
      |partialDeriv idx (fun y => propagatorW Cf r t φ y - propagatorW Cf r s' φ y) x| ≤
        C * |t - s'| * jbracket x * sobolevNorm (q : ℝ) φ

/-- The kernel statement of `B:lem:path-propagator-increment` on `ℝ^d` for one coefficient `Cf` and `q = q_R`:
the Riesz representatives `K_{j;q}^{r,t}(x) ∈ H^{-q}` of `φ ↦ ∂_jU^{r,t}φ(x)` on `H^q` (smooth tests) exist and
are unique, and any such family satisfies `‖K^{r,t}(x) - K^{r,s}(x)‖ ≤ C|t-s|(1+|x|)`
(`B:eq:path-kernel-increment`, `𝔻 = ℝ^d`) and `‖K^{r,t}(x)‖ ≤ C`. -/
def KernelBoundRd (Cf : WholeCoeff d) (T : ℝ) (q : ℕ) (C : ℝ) : Prop :=
  (∀ (j : Fin d) (r t : ℝ), 0 ≤ r → r ≤ t → t ≤ T → ∀ x : Euc d,
    ∃! k : HNeg d (q : ℝ), ∀ φ : Euc d → ℝ, IsSobolevTest (q : ℝ) φ →
      HNeg.pairing φ k = gradient (propagatorW Cf r t φ) x j) ∧
  ∀ Kern : Fin d → ℝ → ℝ → Euc d → HNeg d (q : ℝ),
    (∀ (j : Fin d) (r t : ℝ), 0 ≤ r → r ≤ t → t ≤ T → ∀ x : Euc d, ∀ φ : Euc d → ℝ,
      IsSobolevTest (q : ℝ) φ → HNeg.pairing φ (Kern j r t x) = gradient (propagatorW Cf r t φ) x j) →
    ∀ (j : Fin d) (r s' t : ℝ), 0 ≤ r → r ≤ s' → s' ≤ t → t ≤ T → ∀ x : Euc d,
      ‖Kern j r t x - Kern j r s' x‖ ≤ C * |t - s'| * (1 + ‖x‖) ∧ ‖Kern j r t x‖ ≤ C

/-- Lemma S.A.22(ii) and the kernel part (`S:B:lem:path-propagator-increment`, TeX S L10733-10755), `ℝ^d`,
`q_R = Γ + 2`, `Γ = fd.Gamma` the index of the selected field density (so that `H^{q_R}` embeds into
`C^{m_0+1}`-bounded functions: `Γ + 2 > m_* + d/2 + 4`, `m_0 ≤ m_*`; the TeX: "two derivatives above the
fixed-time field theorem").  Hypotheses (S L10733-10735, S L9998-10003): the coefficient bounds two derivatives
above `B:thm:main-rd-field`, i.e. `B:ass:mf-reg` at `r = q_R + 3 = Γ + 5` (`MeanFieldRegularityRd`) and `B:eq:V-assumption` with
`m_V = Γ + 5` (`VHypRd`); the adjoint estimates at that level (`AdjointDerivInput`) and `B:ass:rd-path-weighted`
(`PathAdjointInput`).  Conclusion: for the particle propagators (`N ≥ 1`) and, for every limiting coefficient
satisfying `LimitPathHyp`, the limiting propagator: `IncrementBoundRd` (`B:eq:path-propagator-rd`) and
`KernelBoundRd` (`B:eq:path-kernel-increment` and the uniform kernel bound), with `C` depending only on the
listed bounds (not on `S`, `L`, `N`).

Statement repair MP-RD-REPAIRS (ISSUES.md): the limit clause has the hypothesis `L.invβ ≤ νbar`, as the particle clauses have
(`∀ N, S.invβ N ≤ νbar`); `LimitPathHyp` gave no bound on `L.invβ`, but the generator carries `ν‖Δφ‖`. -/
theorem path_propagator_increment_rd (s : ℝ) (fd : FieldDensityRd d s)
    (ν₀ MB Λ ΛV G₀ νbar T Kadj Cw : ℝ) (m₀ : ℕ) (hm₀ : 1 ≤ m₀) (hm₀' : m₀ ≤ mStar d) :
    ∃ C : ℝ, ∀ (S : WholeMainData d), S.s = s → S.T = T → (∀ N, S.invβ N ≤ νbar) →
      fd.Holds S ν₀ → PDE.MatBound MB S.M → MeanFieldRegularityRd S (fd.Gamma + 5) Λ →
      VHypRd (fd.Gamma + 5) ΛV G₀ S.V → PathAdjointInput S fd.Gamma m₀ Kadj Cw →
      (∀ N : ℕ, 1 ≤ N →
        IncrementBoundRd (S.coeff N) T (fd.Gamma + 2) m₀ C ∧
        KernelBoundRd (S.coeff N) T (fd.Gamma + 2) C) ∧
      ∀ L : LimitCoeffsRd d, LimitPathHyp S L fd ν₀ Λ Kadj Cw m₀ → L.invβ ≤ νbar →
        IncrementBoundRd (L.coeff S) T (fd.Gamma + 2) m₀ C ∧
        KernelBoundRd (L.coeff S) T (fd.Gamma + 2) C := by
  sorry

/-! ### `B:lem:path-initial-modulus` (S.A.23) -/

/-- The transported empirical initial field on the torus, `𝓘_{N,emp}^t = A_N V_N^{t,0}(κ_NΞ_N^0)`
(S L10683-10688), as an element of `H^{-q}`, `q = q_T`. -/
def transportedEmpT (S : Main.MainData d) (R : ∀ N, Main.Realization d N) (q : ℕ) (N : ℕ) (t : ℝ)
    (ζ : (R N).Ω) : NegSobolev d (q : ℝ) :=
  S.AN N • Main.transportField (S.dyn N) (S.ρ N) t (q : ℝ)
    (S.κ N • NegSobolev.ofMeasureDiff (q : ℝ) (HRS.empirical ((R N).X₀ ζ)) S.μ0)

/-- The transported Gaussian-initial field on the torus, `𝓘_N^t = A_N V_N^{t,0}η°` (`η°` the
`H^{-γ}`-valued initial field `ηF`, embedded in `H^{-q}`). -/
def transportedGaussT (S : Main.MainData d) (R : ∀ N, Main.Realization d N) (q γ : ℕ)
    (ηF : ∀ N, (R N).Ω → NegSobolev d (γ : ℝ)) (N : ℕ) (t : ℝ) (ζ : (R N).Ω) :
    NegSobolev d (q : ℝ) :=
  S.AN N • Main.transportField (S.dyn N) (S.ρ N) t (q : ℝ) (NegSobolev.embed (q : ℝ) (ηF N ζ))

/-- Lemma S.A.23, torus part (`S:B:lem:path-initial-modulus`, TeX S L10794-10800 and proof L10803-10806):
under `B:ass:init`, `B:ass:init-field` and the path-level coefficient bounds (`TorusStanding` at the level
`γ + 2`, as for `HRS.Main.main_torus_path`),
`E‖𝓘_{N,emp}^t - 𝓘_{N,emp}^s‖²_{H_q} + E‖𝓘_N^t - 𝓘_N^s‖²_{H_q} ≤ C|t-s|²` (`B:eq:path-initial-increments`),
for all `N ≥ 1`, `s,t ∈ [0,T]`; the same estimate for the limiting transported initial field
`A(U_∞^{0,t})^*η°` (`η° ∼ νin`; `L : LimitCoeffs`, `CoeffConvergence`: the limiting coefficients satisfy the
same adjoint hypotheses); and (the "Consequently" sentence) all these processes have continuous
`H_q`-valued versions with a uniform temporal modulus in probability, whose path laws are tight whenever the
fixed-time marginals are (`ContVersionTight`, i.e. `path_tightness_criterion`).  `q = q_T = γ + 2`.
`C` depends only on `d, s, Rg, ν₀, MB, Λ, T, VB, C_in`.  (`Cc, C₀` are the constants of `B:ass:MF`
inside `TorusStanding`.) -/
-- MP-STAT-REPAIRS (applied 2026-10-18 after the independent review of Chunk F): statement repaired; see ISSUES "MP: request MP-STAT-REPAIRS".
theorem path_initial_modulus_torus (s : ℝ) (Rg : PDE.Regime)
    (ν₀ MB Λ T VB Cin C₀ Cc νbar : ℝ) :
    ∃ C : ℝ, ∀ (S : Main.MainData d), S.s = s → S.T = T → (∀ N, S.invβ N ≤ νbar) →
      ∀ (R : ∀ N, Main.Realization d N) (𝔈 : ℕ → ℝ),
        Main.TorusStanding S R Rg ν₀ MB Λ VB (Main.gammaIdx d + 2) C₀ Cc 𝔈 →
        ∀ (m₀ : ℕ) (ε : ℕ → ℝ) (Ψ : ℕ → Set (Torus d → ℝ)), Main.InitialFluctuation S R m₀ Cin ε Ψ →
        ∀ (εf : ℕ → ℝ) (ηF : ∀ N, (R N).Ω → NegSobolev d (Main.gammaIdx d : ℝ))
          (νin : Measure (NegSobolev d (Main.gammaIdx d : ℝ))),
          Main.InitialFluctuationField S R (Main.gammaIdx d) Cin εf ηF νin →
        (∀ N : ℕ, 1 ≤ N → ∀ s' ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T,
          ∫⁻ ζ, ‖transportedEmpT S R (qT d) N t ζ - transportedEmpT S R (qT d) N s' ζ‖ₑ ^ 2 ∂(R N).P +
            ∫⁻ ζ, ‖transportedGaussT S R (qT d) (Main.gammaIdx d) ηF N t ζ -
              transportedGaussT S R (qT d) (Main.gammaIdx d) ηF N s' ζ‖ₑ ^ 2 ∂(R N).P ≤
          ENNReal.ofReal (C * |t - s'| ^ 2)) ∧
        (∀ L : Main.LimitCoeffs d,
          Main.CoeffConvergence S L Rg ν₀ MB Λ VB (Main.gammaIdx d + 2) (Main.gammaIdx d) →
          ∀ s' ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T,
            ∫⁻ F, ‖L.A • Main.transportField (L.dyn S) L.ρ t ((qT d : ℕ) : ℝ)
                (NegSobolev.embed ((qT d : ℕ) : ℝ) F) -
              L.A • Main.transportField (L.dyn S) L.ρ s' ((qT d : ℕ) : ℝ)
                (NegSobolev.embed ((qT d : ℕ) : ℝ) F)‖ₑ ^ 2 ∂νin ≤
            ENNReal.ofReal (C * |t - s'| ^ 2)) ∧
        (∃ Zc, ContVersionTight (E := NegSobolev d ((qT d : ℕ) : ℝ)) T (fun N => (R N).P)
          (fun N t ζ => transportedEmpT S R (qT d) N t ζ) Zc) ∧
        (∃ Zc, ContVersionTight (E := NegSobolev d ((qT d : ℕ) : ℝ)) T (fun N => (R N).P)
          (fun N t ζ => transportedGaussT S R (qT d) (Main.gammaIdx d) ηF N t ζ) Zc) := by
  sorry


/-- The `H^{-q}(ℝ^d)`-valued transported initial fields at the index `q` (`B:eq:transported-initial-rd`):
`Iemp N t`, `Iη N t` are measurable `H`-valued random variables representing, a.s. for every `t ∈ [0,T]` and smooth
`φ ∈ H^q`, the functionals `φ ↦ A_Nκ_N⟨U_N^{0,t}φ, Ξ_N^0⟩`, `φ ↦ A_N η°(U_N^{0,t}φ)` (the representation part of
`TransportedInitialFieldRd`, without the moment and rate clauses). -/
def IsInitReprRd (S : WholeMainData d) (R : ∀ N, RealizationRd d N) (q : ℕ)
    (Iemp Iη : ∀ N, ℝ → (R N).Ω → HNeg d (q : ℝ)) : Prop :=
  (∀ N : ℕ, 1 ≤ N → ∀ t, Measurable (Iemp N t) ∧ Measurable (Iη N t)) ∧
  ∀ N : ℕ, 1 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) S.T, ∀ φ : Euc d → ℝ, IsSobolevTest (q : ℝ) φ →
    ∀ᵐ ζ ∂(R N).P,
      HNeg.pairing φ (Iemp N t ζ) = S.AN N * (S.κ N *
        (pair (empirical ((R N).X₀ ζ)) (propagatorW (S.coeff N) 0 t φ) -
          pair S.μ0 (propagatorW (S.coeff N) 0 t φ))) ∧
      HNeg.pairing φ (Iη N t ζ) = S.AN N * (R N).η ζ (propagatorW (S.coeff N) 0 t φ)

/-- Lemma S.A.23, `ℝ^d` part (`S:B:lem:path-initial-modulus`, TeX S L10794-10800 and proof L10807-10823): under
`B:ass:init` (`InitialFluctuationRd`, `Y_0 = H^{m_0}_uloc ∩ C_b^{0,1}`, `ϖ = ⟨x⟩^{-(d+3)}`),
`B:ass:init-field`(F-rd) (`TransportedInitialFieldRd`, `InitialFieldDist`, at the index `Γ = fd.Gamma`), and the
path-level coefficient bounds (`MeanFieldRegularityRd`, `VHypRd` at the level `Γ + 5`, `PathAdjointInput`, which
contains `B:ass:rd-path-weighted`): for representatives `Iq, Jq` of the transported fields in `H^{-q_R}`,
`q_R = Γ + 2` (`IsInitReprRd`), `E‖𝓘_{N,emp}^t - 𝓘_{N,emp}^s‖²_{H_q} + E‖𝓘_N^t - 𝓘_N^s‖²_{H_q} ≤ C|t-s|²`
(`B:eq:path-initial-increments`) for `N ≥ 1`, `s, t ∈ [0,T]`, and the consequence: continuous versions with a
uniform temporal modulus in probability and the tightness transfer (`ContVersionTight`).  `C` depends only on the
listed bounds and `χ`.  AMBIGUITY (S L10779): (F-rd) is stated at the index `Γ` while the increments are in
`H^{-q_R}`; only the existence of the `H^{-q_R}`-valued representatives is used (the proof uses (I2) only). -/
theorem path_initial_modulus_rd (s : ℝ) (fd : FieldDensityRd d s)
    (ν₀ MB Λ ΛV G₀ νbar T Kadj Cw Cin : ℝ) (m₀ : ℕ) (hm₀' : m₀ ≤ mStar d) (χ : Euc d → ℝ)
    (hχ : IsUlocCutoff χ) :
    ∃ C : ℝ, ∀ (S : WholeMainData d), S.s = s → S.T = T → (∀ N, S.invβ N ≤ νbar) →
      fd.Holds S ν₀ → PDE.MatBound MB S.M → MeanFieldRegularityRd S (fd.Gamma + 5) Λ →
      VHypRd (fd.Gamma + 5) ΛV G₀ S.V → PathAdjointInput S fd.Gamma m₀ Kadj Cw →
      ∀ (R : ∀ N, RealizationRd d N) (ε : ℕ → ℝ) (Ψ : ℕ → Set (Euc d → ℝ)),
        InitialFluctuationRd S R χ m₀ Cin ε Ψ →
      ∀ (εf : ℕ → ℝ) (Iemp I : ∀ N, ℝ → (R N).Ω → HNeg d (fd.Gamma : ℝ)),
        TransportedInitialFieldRd S R fd.Gamma Cin εf Iemp I →
        InitialFieldDist S R fd.Gamma εf Iemp I →
      ∀ (Iq Jq : ∀ N, ℝ → (R N).Ω → HNeg d ((fd.Gamma + 2 : ℕ) : ℝ)),
        IsInitReprRd S R (fd.Gamma + 2) Iq Jq →
        (∀ N : ℕ, 1 ≤ N → ∀ s' ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T,
          ∫⁻ ζ, ‖Iq N t ζ - Iq N s' ζ‖ₑ ^ 2 ∂(R N).P + ∫⁻ ζ, ‖Jq N t ζ - Jq N s' ζ‖ₑ ^ 2 ∂(R N).P ≤
            ENNReal.ofReal (C * |t - s'| ^ 2)) ∧
        (∃ Zc, ContVersionTight T (fun N => (R N).P) (fun N t ζ => Iq N t ζ) Zc) ∧
        (∃ Zc, ContVersionTight T (fun N => (R N).P) (fun N t ζ => Jq N t ζ) Zc) := by
  sorry

/-- Lemma S.A.23, the limiting transported initial field on `ℝ^d` (TeX S L10797: "The same estimate holds for the
limiting transported initial field"): for a limiting coefficient `L` with `LimitPathHyp`, a random functional `η°`
on `(Ω, P)` satisfying `E|⟨ψ,η°⟩|² ≤ C_in²‖ψ‖²_{H^{m_0}(ϖ)}` (the `η°`-part of (I2)) for `ψ ∈ Y_0`, and an
`H^{-q_R}`-valued process `J^t` representing `φ ↦ A η°(U_∞^{0,t}φ)`: `E‖J^t - J^s‖²_{H^{-q_R}} ≤ C|t-s|²`, and `J`
has a continuous version with the tightness transfer.

Statement repair MP-RD-REPAIRS (ISSUES.md): `νbar` (before `C`), `L.invβ ≤ νbar` and `L.A ≤ 1` are added. Without them the claim is false:
`LimitPathHyp` does not mention `L.A`, `C` is chosen before `L`, and `(A, J) ↦ (λA, λJ)` preserves all hypotheses and multiplies the left
side by `λ²`. Consumers obtain both bounds from `CoeffConvergenceRd`.

Statement repair MP-RD-REPAIRS-3 (ISSUES.md): the hypothesis that `η` is almost surely linear on `Y0Class` (the TeX calls `η°` a random
real-linear functional on `Y_0`) is added before the second-moment hypothesis; the proof uses it for countably many triples. -/
theorem path_initial_modulus_rd_limit (s : ℝ) (fd : FieldDensityRd d s)
    (ν₀ MB Λ ΛV G₀ νbar T Kadj Cw Cin : ℝ) (m₀ : ℕ) (hm₀' : m₀ ≤ mStar d) (χ : Euc d → ℝ)
    (hχ : IsUlocCutoff χ) :
    ∃ C : ℝ, ∀ (S : WholeMainData d), S.s = s → S.T = T → PDE.MatBound MB S.M →
      VHypRd (fd.Gamma + 5) ΛV G₀ S.V → ∀ L : LimitCoeffsRd d,
      LimitPathHyp S L fd ν₀ Λ Kadj Cw m₀ → L.invβ ≤ νbar → L.A ≤ 1 →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (η : Ω → (Euc d → ℝ) → ℝ),
      (∀ (ψ ψ' : Euc d → ℝ) (c : ℝ), Y0Class m₀ χ ψ → Y0Class m₀ χ ψ' →
        ∀ᵐ ζ ∂P, η ζ (c • ψ + ψ') = c * η ζ ψ + η ζ ψ') →
      (∀ ψ : Euc d → ℝ, Y0Class m₀ χ ψ → ∫⁻ ζ, ENNReal.ofReal ((η ζ ψ) ^ 2) ∂P ≤
        ENNReal.ofReal (Cin ^ 2 * (varpiNormE m₀ χ ψ).toReal ^ 2)) →
      ∀ J : ℝ → Ω → HNeg d ((fd.Gamma + 2 : ℕ) : ℝ), (∀ t, Measurable (J t)) →
        (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ φ : Euc d → ℝ, IsSobolevTest ((fd.Gamma + 2 : ℕ) : ℝ) φ →
          ∀ᵐ ζ ∂P, HNeg.pairing φ (J t ζ) = L.A * η ζ (propagatorW (L.coeff S) 0 t φ)) →
        (∀ s' ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T,
          ∫⁻ ζ, ‖J t ζ - J s' ζ‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal (C * |t - s'| ^ 2)) ∧
        ∃ Zc, ContVersionTight (Ω := fun _ : ℕ => Ω) T (fun _ => P) (fun _ t ζ => J t ζ) Zc := by
  sorry

/-! ### `B:lem:path-martingale-modulus` (S.A.24) -/

/-- `Yc` is a continuous version of `Y` on `[0,T]`: `Yc t = Y t` a.s. for each `t ∈ [0,T]`, and `Yc`
has a.s. continuous paths on `[0,T]`. -/
def HasContVersion {E : Type*} [TopologicalSpace E] {Ω : Type*} [MeasurableSpace Ω] (T : ℝ)
    (P : Measure Ω) (Y Yc : ℝ → Ω → E) : Prop :=
  (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ζ ∂P, Yc t ζ = Y t ζ) ∧
    ∀ᵐ ζ ∂P, ContinuousOn (fun t => Yc t ζ) (Set.Icc (0 : ℝ) T)

/-- The thermal stochastic convolution on the torus (S L10776-10779): for each terminal time `t`,
`𝕄_N^t = σ_N√(2/(N²β_N)) ∑_{i,j} ∫_0^t K_{N,j;q}^{r,t}(x_i^r) dW_{i,j}^r`, represented (kernel-free) by its
pairings with the smooth mean-zero tests: `⟨φ, 𝕄^t⟩ = σ · M_N^t[U^{·,t}φ]` with the empirical martingale
`HRS.empiricalMartingale` (integrand `N⁻¹√(2β⁻¹) ∇f^r(x_i^r)`, `σ = σ_N`), a.s. for each `t ∈ [0,T]`;
`𝕄^t` is measurable. -/
def IsStochConvT {Ω : Type*} {mΩ : MeasurableSpace Ω} {N : ℕ} (P : Measure Ω)
    (ℱ : Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (D : DynData d)
    (ρ : ℝ → Torus d → ℝ) (σ q T : ℝ) (X : ℝ≥0 → Ω → Config d N)
    (M : ℝ → Ω → NegSobolev d q) : Prop :=
  (∀ t, Measurable (M t)) ∧ ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ φ : Torus d → ℝ, Torus.IsSmooth φ →
    Torus.mean φ = 0 → ∀ᵐ ζ ∂P, NegSobolev.eval (M t ζ) φ =
      σ * empiricalMartingale P ℱ W' D t (fun r => propagator D ρ r t φ) X t ζ

/-- `Θ_N(u) = ∫_0^u ⟨1+|x|², μ_N^r⟩ dr` (S L10847-10849). -/
def thetaN {Ω : Type*} {N : ℕ} (X : ℝ≥0 → Ω → EucConfig d N) (ζ : Ω) (u : ℝ) : ℝ :=
  ∫ r in Set.Icc (0 : ℝ) u, (1 + secondMomentOf (empirical (X (Real.toNNReal r) ζ)))

open Classical in
/-- `τ_{N,L} = inf{u : Θ_N(u) > L} ∧ T` (S L10849-10851), `T` when no `u ∈ [0,T]` has `Θ_N(u) > L`. -/
def tauNL {Ω : Type*} {N : ℕ} (T L : ℝ) (X : ℝ≥0 → Ω → EucConfig d N) (ζ : Ω) : ℝ :=
  if ∃ u ∈ Set.Icc (0 : ℝ) T, L < thetaN X ζ u then
    sInf {u | u ∈ Set.Icc (0 : ℝ) T ∧ L < thetaN X ζ u} else T

/-- The (stopped) thermal stochastic convolution on `ℝ^d`: with `c_N = σ_N√(2/(N²β_N))`
(`cN = σ * √(2 invβ) / N`), `⟨φ, 𝕄^t_τ⟩ = c_N ∑_{i,j}∫_0^{t∧τ} ∂_jU^{r,t}φ(x_i^r) dW_{i,j}^r` (a.s., for each
`t ∈ [0,T]` and smooth `φ ∈ H^q`; Itô integral `HRS.itoIntegral`, integrand extended by `0` outside
`[0,t∧τ]`), as a measurable `H^{-q}(ℝ^d)`-valued random variable.  The unstopped convolution `𝕄_N` is the
case `τ ≡ T`; `𝕄_{N,L}` is `τ = τ_{N,L}` (S L10846-10852). -/
def IsStochConvW {Ω : Type*} {mΩ : MeasurableSpace Ω} {N : ℕ} (P : Measure Ω)
    (ℱ : Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (Cf : WholeCoeff d)
    (cN : ℝ) (q : ℕ) (T : ℝ) (X : ℝ≥0 → Ω → EucConfig d N) (τ : Ω → ℝ)
    (M : ℝ → Ω → HNeg d (q : ℝ)) : Prop :=
  (∀ t, Measurable (M t)) ∧ ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ φ : Euc d → ℝ, IsSobolevTest (q : ℝ) φ →
    ∀ᵐ ζ ∂P, HNeg.pairing φ (M t ζ) = itoIntegral P ℱ W'
      (fun r ζ' ia => if r ∈ Set.Icc (0 : ℝ) t ∧ r ≤ τ ζ' then
        cN * gradient (propagatorW Cf r t φ) (X (Real.toNNReal r) ζ' ia.1) ia.2 else 0) t ζ

/-- Lemma S.A.24, torus (`S:B:lem:path-martingale-modulus`, TeX S L10827-10838, `B:eq:path-martingale-fourth-torus`):
under the hypotheses of the torus field theorem at the path level (`TorusStanding` at `γ + 2`; the
selected flow carries a Brownian filtration, `IsFilteredSolution`), the thermal stochastic convolutions
`𝕄_N` in `H_q`, `q = q_T`, satisfy `E‖𝕄_N^t - 𝕄_N^s‖⁴_{H_q} ≤ C|t-s|²`, `s,t ∈ [0,T]`, `N ≥ 1`, have
continuous versions with a uniform temporal modulus in probability (`ContVersionTight`), and the limiting
Gaussian stochastic convolution (any process `Y` solving the linear equation with the limiting coefficients
and zero initial field, `IsLinearFluctuationProcess` with `Y_0 = 0`) has a continuous `H_q`-valued
version.  `σ_N = S.sigma N`; `C` depends only on `d, s, Rg, ν₀, MB, Λ, T, VB`. -/
-- MP-STAT-REPAIRS (applied 2026-10-18 after the independent review of Chunk F): statement repaired; see ISSUES "MP: request MP-STAT-REPAIRS".
theorem path_martingale_modulus_torus (s : ℝ) (Rg : PDE.Regime)
    (ν₀ MB Λ T VB C₀ Cc νbar : ℝ) :
    ∃ C : ℝ, ∀ (S : Main.MainData d), S.s = s → S.T = T → (∀ N, S.invβ N ≤ νbar) →
      ∀ (R : ∀ N, Main.Realization d N) (𝔈 : ℕ → ℝ),
        Main.TorusStanding S R Rg ν₀ MB Λ VB (Main.gammaIdx d + 2) C₀ Cc 𝔈 →
        ∀ (ℱ : ∀ N, Filtration ℝ (R N).mΩ) (W' : ∀ N, ℝ≥0 → (R N).Ω → (Fin N × Fin d) → ℝ),
        (∀ N : ℕ, 1 ≤ N → IsFilteredSolution (R N).P (ℱ N) (W' N) (R N).W (R N).X) →
        ∀ (Mq : ∀ N, ℝ → (R N).Ω → NegSobolev d ((qT d : ℕ) : ℝ)),
        (∀ N : ℕ, 1 ≤ N → IsStochConvT (R N).P (ℱ N) (W' N) (S.dyn N) (S.ρ N) (S.sigma N)
          ((qT d : ℕ) : ℝ) T (R N).X (Mq N)) →
        (∀ N : ℕ, 1 ≤ N → ∀ s' ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T,
          ∫⁻ ζ, ‖Mq N t ζ - Mq N s' ζ‖ₑ ^ 4 ∂(R N).P ≤ ENNReal.ofReal (C * |t - s'| ^ 2)) ∧
        (∃ Zc, ContVersionTight (E := NegSobolev d ((qT d : ℕ) : ℝ)) T (fun N => (R N).P) Mq Zc) ∧
        (∀ L : Main.LimitCoeffs d,
          Main.CoeffConvergence S L Rg ν₀ MB Λ VB (Main.gammaIdx d + 2) (Main.gammaIdx d) →
          ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
            (Y : ℝ → Ω' → NegSobolev d ((qT d : ℕ) : ℝ)),
          Main.IsLinearFluctuationProcess P' (L.dyn S) L.ρ ((qT d : ℕ) : ℝ) L.invβstar T
            (fun _ => 0) Y → ∃ Yc, HasContVersion T P' Y Yc) := by
  sorry

/-- Lemma S.A.24, `ℝ^d` (`S:B:lem:path-martingale-modulus`, TeX S L10827-10838, `B:eq:path-martingale-stop`):
under the hypotheses of the path-space theorem S.A.9 that enter the lemma (`RdStanding` at the level
`Γ + 5 = q_R + 3` for `Γ = fd.Gamma`: `B:ass:sde`, `B:ass:mf-reg`, `B:eq:V-assumption`, `B:ass:MF`,
`B:eq:initial-second-moment`; `PathAdjointInput`; `B:ass:sde` with a Brownian filtration), let `𝕄_N` be the thermal
stochastic convolutions in `H_q`, `q = q_R = Γ + 2` (`IsStochConvW`, `τ ≡ T`).  Then (a) `{𝕄_N}` has continuous
versions with a uniform temporal modulus in probability (`ContVersionTight`); (b) for every `L ≥ 1` and every family
`𝕄_{N,L}` of stopped convolutions (`IsStochConvW` with `τ = τ_{N,L}`) there are continuous versions with
`sup_N P(sup_{t≤T}‖𝕄̃_{N,L}^t - 𝕄̃_N^t‖_{H_q} > 0) ≤ C/L` and
`E‖𝕄_{N,L}^t - 𝕄_{N,L}^s‖⁴_{H_q} ≤ C_L|t-s|²` (`B:eq:path-martingale-stop`); (c) the limiting Gaussian stochastic
convolution (solution `Y` of `IsAdjointDualityLimitW` for a limiting coefficient with `LimitPathHyp`, `η° = 0`)
has a continuous `H_q`-valued version.  The constants `C, C_L` are quantified *after* the bounds `m20`
(`𝔪₂⁰ ≤ m20`, `InitialSecondMoment`) and `Ē` (`𝔈_N ≤ Ē` for all `N ≥ 1`): the proof of (b) uses
`sup_N E[Θ_N(T)] ≤ C` from `B:lem:moments` (S.A.18), which depends on `𝔪₂⁰` and `sup_N 𝔈_N`
(SUSPECTED ISSUE, as in `moments_lemma`: `B:ass:MF` alone does not bound `𝔈_N`). -/
theorem path_martingale_modulus_rd (s : ℝ) (fd : FieldDensityRd d s)
    (ν₀ MB Λ ΛV G₀ νbar T Kadj Cw C₀ m20 Ē : ℝ) (m₀ : ℕ) (hm₀' : m₀ ≤ mStar d) :
    ∃ (C : ℝ) (CL : ℝ → ℝ), ∀ (S : WholeMainData d), S.s = s → S.T = T → (∀ N, S.invβ N ≤ νbar) →
      fd.Holds S ν₀ → ∀ (R : ∀ N, RealizationRd d N) (𝔈 : ℕ → ℝ),
      RdStanding S R MB Λ ΛV G₀ m20 (fd.Gamma + 5) (fd.Gamma + 5) C₀ 𝔈 → (∀ N : ℕ, 1 ≤ N → 𝔈 N ≤ Ē) →
      PathAdjointInput S fd.Gamma m₀ Kadj Cw →
      ∀ (ℱ : ∀ N, Filtration ℝ (R N).mΩ) (W' : ∀ N, ℝ≥0 → (R N).Ω → (Fin N × Fin d) → ℝ),
      (∀ N : ℕ, 1 ≤ N → IsWholeFilteredSolution (R N).P (ℱ N) (W' N) (R N).W (R N).X) →
      ∀ (Mq : ∀ N, ℝ → (R N).Ω → HNeg d ((fd.Gamma + 2 : ℕ) : ℝ)),
      (∀ N : ℕ, 1 ≤ N → IsStochConvW (R N).P (ℱ N) (W' N) (S.coeff N)
        (S.sigma N * Real.sqrt (2 * S.invβ N) / N) (fd.Gamma + 2) T (R N).X (fun _ => T) (Mq N)) →
      (∃ Zc, ContVersionTight T (fun N => (R N).P) Mq Zc) ∧
      (∀ L : ℝ, 1 ≤ L → ∀ (MqL : ∀ N, ℝ → (R N).Ω → HNeg d ((fd.Gamma + 2 : ℕ) : ℝ)),
        (∀ N : ℕ, 1 ≤ N → IsStochConvW (R N).P (ℱ N) (W' N) (S.coeff N)
          (S.sigma N * Real.sqrt (2 * S.invβ N) / N) (fd.Gamma + 2) T (R N).X
          (tauNL T L (R N).X) (MqL N)) →
        (∃ (Zc ZcL : ∀ N, ℝ → (R N).Ω → HNeg d ((fd.Gamma + 2 : ℕ) : ℝ)),
          (∀ N : ℕ, 1 ≤ N → HasContVersion T (R N).P (Mq N) (Zc N)) ∧
          (∀ N : ℕ, 1 ≤ N → HasContVersion T (R N).P (MqL N) (ZcL N)) ∧
          (⨆ N : ℕ, ⨆ (_ : 1 ≤ N),
            (R N).P {ζ | ∃ t ∈ Set.Icc (0 : ℝ) T, ZcL N t ζ ≠ Zc N t ζ}) ≤ ENNReal.ofReal (C / L)) ∧
        (∀ N : ℕ, 1 ≤ N → ∀ s' ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T,
          ∫⁻ ζ, ‖MqL N t ζ - MqL N s' ζ‖ₑ ^ 4 ∂(R N).P ≤ ENNReal.ofReal (CL L * |t - s'| ^ 2))) ∧
      (∀ L : LimitCoeffsRd d, LimitPathHyp S L fd ν₀ Λ Kadj Cw m₀ →
        ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
          (Y : ℝ → Ω' → HNeg d ((fd.Gamma + 2 : ℕ) : ℝ)),
        IsAdjointDualityLimitW P' (L.coeff S) ((fd.Gamma + 2 : ℕ) : ℝ) L.A L.invβstar T
          (fun _ _ => 0) Y → ∃ Yc, HasContVersion T P' Y Yc) := by
  sorry

/-! ### `B:lem:path-remainder` (S.A.25) -/

/-- The quadratic commutator remainder `ℝ_N^t` on the torus (S L10776-10779, `B:eq:path-three-term`): the
`H^{-q}`-valued random variable representing the functional
`φ ↦ σ_N ∫_0^t B_{f^r}(Fluc_N^r, Fluc_N^r) dr`, `f^r = U^{r,t}φ`, i.e. the last term of the
duality identity `B:eq:duality-identity-final` (`HRS.flucInteraction`, which carries the factor `1/2`),
a.s. for each `t ∈ [0,T]` and smooth mean-zero `φ`. -/
def IsRemainderT {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (P : Measure Ω) (D : DynData d)
    (ρ : ℝ → Torus d → ℝ) (σ q T : ℝ) (X : ℝ≥0 → Ω → Config d N)
    (Rm : ℝ → Ω → NegSobolev d q) : Prop :=
  (∀ t, Measurable (Rm t)) ∧ ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ φ : Torus d → ℝ, Torus.IsSmooth φ →
    Torus.mean φ = 0 → ∀ᵐ ζ ∂P, NegSobolev.eval (Rm t ζ) φ =
      σ * ∫ r in (0 : ℝ)..t,
        flucInteraction D (propagator D ρ r t φ) (X (Real.toNNReal r) ζ) (ρ r)

/-- Lemma S.A.25, torus (`S:B:lem:path-remainder`, TeX S L10861-10870, `B:eq:path-remainder-torus`): in the
torus field regime (`TorusStanding` at the field level `γ`, i.e. the hypotheses of
`HRS.Main.main_torus_field`), the remainder `ℝ_N^t` in `H^{-q_T}` (any representative `Rm` of the
functional, and any continuous version `Rc` of it) satisfies
`E[sup_{0≤t≤T}‖ℝ_N^t‖_{H^{-q_T}}] ≤ C T σ_N 𝔈_N`, and `C T σ_N 𝔈_N → 0`.  `C` depends only on
`d, s, Rg, ν₀, MB, Λ, T, VB`.  The selected adjoint and commutator estimates of the torus field theorem
(cited in the TeX proof) are not re-stated: this is the same standing-assumption level as
`main_torus_field`. -/
-- MP-STAT-REPAIRS (applied 2026-10-18 after the independent review of Chunk F): statement repaired; see ISSUES "MP: request MP-STAT-REPAIRS".
theorem path_remainder_torus (s : ℝ) :
    ∃ C₀min : ℝ, ∀ (Rg : PDE.Regime) (ν₀ MB Λ T VB C₀ Cc : ℝ), C₀min ≤ C₀ →
    ∃ C : ℝ, ∀ (S : Main.MainData d), S.s = s → S.T = T →
      ∀ (R : ∀ N, Main.Realization d N) (𝔈 : ℕ → ℝ),
        Main.TorusStanding S R Rg ν₀ MB Λ VB (Main.gammaIdx d) C₀ Cc 𝔈 →
        ∀ (Rm Rc : ∀ N, ℝ → (R N).Ω → NegSobolev d ((qT d : ℕ) : ℝ)),
        (∀ N : ℕ, 1 ≤ N → IsRemainderT (R N).P (S.dyn N) (S.ρ N) (S.sigma N) ((qT d : ℕ) : ℝ) T
          (R N).X (Rm N)) →
        (∀ N : ℕ, 1 ≤ N → HasContVersion T (R N).P (Rm N) (Rc N)) →
        (∀ N : ℕ, 1 ≤ N →
          ∫⁻ ζ, ⨆ t ∈ Set.Icc (0 : ℝ) T, ‖Rc N t ζ‖ₑ ∂(R N).P ≤
            ENNReal.ofReal (C * T * S.sigma N * 𝔈 N)) ∧
        Tendsto (fun N => C * T * S.sigma N * 𝔈 N) atTop (𝓝 0) := by
  sorry

/-- The quadratic commutator remainder `ℝ_N^t` on `ℝ^d` in `H^{-q}(ℝ^d)`: the `H`-valued random variable
representing `φ ↦ (σ_N/2) ∫_0^t Comm_N(M^*∇U^{r,t}φ; X_N^r, μ_{β_N}^r) dr` (the last term of
`B:eq:duality-identity-final`, `Comm_N = 2 · B(Fluc,Fluc)` with the deleted particle diagonal,
`HRS.Whole.commN`), a.s. for each `t ∈ [0,T]` and smooth `φ ∈ H^q`. -/
def IsRemainderW (S : WholeMainData d) (R : ∀ N, RealizationRd d N) (N : ℕ) (q : ℕ)
    (Rm : ℝ → (R N).Ω → HNeg d (q : ℝ)) : Prop :=
  (∀ t, Measurable (Rm t)) ∧ ∀ t ∈ Set.Icc (0 : ℝ) S.T, ∀ φ : Euc d → ℝ, IsSobolevTest (q : ℝ) φ →
    ∀ᵐ ζ ∂(R N).P, HNeg.pairing φ (Rm t ζ) = (S.sigma N / 2) * ∫ r in (0 : ℝ)..t,
      commN d S.s (fun x => Torus.matVec S.M.transpose (gradient (propagatorW (S.coeff N) r t φ) x))
        ((R N).X (Real.toNNReal r) ζ) (withDensityReal (S.ρ N r))

/-- Lemma S.A.25, `ℝ^d` (`S:B:lem:path-remainder`, TeX S L10861-10870, `B:eq:path-remainder-rd`): for a
whole-space density `(𝒳, Γ, e_N)` (`fd`, `Γ = fd.Gamma`, `e_N = fd.eN N`; selected commutator estimate
`SelectedCommutatorInput`), under `RdStanding` at the level `Γ + 5` (`B:ass:sde`, `B:ass:mf-reg`,
`B:eq:V-assumption`, `B:ass:MF`, `B:eq:initial-second-moment`), the path-level adjoint input
(`PathAdjointInput`, needed for the representation at the index `q_R = Γ + 2`) and the smallness
`σ_N(𝔈_N + e_N) → 0` (a consequence of `B:eq:rd-path-smallness`, all terms being nonnegative), every continuous
version `Rc` of the remainder `ℝ_N^t ∈ H^{-q_R}` satisfies
`E[sup_{0≤t≤T}‖ℝ_N^t‖_{H^{-q_R}}] ≤ C T σ_N(𝔈_N + e_N)` and `C T σ_N(𝔈_N + e_N) → 0`.  `C` depends only on the
listed bounds (the constant `K'` of the commutator input).  Technical hypotheses: `N ≥ 2`; `X_N^t` a.s. pairwise
distinct at each fixed `t`. -/
theorem path_remainder_rd (s : ℝ) (fd : FieldDensityRd d s)
    (ν₀ MB Λ ΛV G₀ νbar T Kadj Cw C₀ K' : ℝ) (m₀ : ℕ) (hΛ : 1 ≤ Λ) :
    ∃ C : ℝ, ∀ (S : WholeMainData d), S.s = s → S.T = T → (∀ N, S.invβ N ≤ νbar) →
      fd.Holds S ν₀ → ∀ (R : ∀ N, RealizationRd d N) (𝔈 : ℕ → ℝ) (m20 : ℝ),
      RdStanding S R MB Λ ΛV G₀ m20 (fd.Gamma + 5) (fd.Gamma + 5) C₀ 𝔈 →
      PathAdjointInput S fd.Gamma m₀ Kadj Cw →
      SelectedCommutatorInput S (fd.Gamma : ℝ) T K' C₀ Λ fd.eN →
      Tendsto (fun N => S.sigma N * (𝔈 N + fd.eN N)) atTop (𝓝 0) →
      (∀ N : ℕ, 1 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ζ ∂(R N).P,
        (R N).X (Real.toNNReal t) ζ ∉ eucCollisionSet d N) →
      ∀ (Rm Rc : ∀ N, ℝ → (R N).Ω → HNeg d ((fd.Gamma + 2 : ℕ) : ℝ)),
      (∀ N : ℕ, 2 ≤ N → IsRemainderW S R N (fd.Gamma + 2) (Rm N)) →
      (∀ N : ℕ, 2 ≤ N → HasContVersion T (R N).P (Rm N) (Rc N)) →
      (∀ N : ℕ, 2 ≤ N →
        ∫⁻ ζ, ⨆ t ∈ Set.Icc (0 : ℝ) T, ‖Rc N t ζ‖ₑ ∂(R N).P ≤
          ENNReal.ofReal (C * T * S.sigma N * (𝔈 N + fd.eN N))) ∧
      Tendsto (fun N => C * T * S.sigma N * (𝔈 N + fd.eN N)) atTop (𝓝 0) := by
  sorry

/-! ### `B:lem:path-fidi` (S.A.26) -/

/-- A trigonometric polynomial on `𝕋^d`: a constant plus a finite real combination of the real trigonometric
modes `Torus.realMode k`. -/
def IsTrigPolyT (φ : Torus d → ℝ) : Prop :=
  ∃ (F : Finset (NonzeroLattice d)) (c : NonzeroLattice d → ℝ) (c0 : ℝ),
    ∀ x, φ x = c0 + ∑ k ∈ F, c k * Torus.realMode k x

/-- Lemma S.A.26, torus (`S:B:lem:path-fidi`, TeX S L10884-10891): under the hypotheses of the path-space
theorem on the torus (`HRS.Main.main_torus_path`: `TorusStanding` at `γ+2`, A.4 for the finite family, A.5,
`CoeffConvergence`, `ε_N^f → 0`), for every finite collection of times `t_a` and terminal tests
`φ_a` that are trigonometric polynomials (`IsTrigPolyT`), the statistics
`(⟨φ_a, Ξ_N^{t_a}⟩)_a ⟹ (⟨φ_a, η^{t_a}⟩)_a`, the law of the vector of a continuous solution `Y` of the
limiting linear equation with initial value `A η°` (`η° ∼ νin`, `IsLinearFluctuationSolution`; as in
`main_torus_path`).  The initial coupling of A.4 depends on the family (`Ψ N` = transported tests). -/
-- MP-STAT-REPAIRS (applied 2026-10-18 after the independent review of Chunk F): statement repaired; see ISSUES "MP: request MP-STAT-REPAIRS".
theorem path_fidi_torus (s : ℝ) :
    ∃ C₀min : ℝ, ∀ (Rg : PDE.Regime) (ν₀ MB Λ T VB Cin : ℝ) (C₀ Cc : ℝ), C₀min ≤ C₀ →
    ∀ (S : Main.MainData d) (hs : S.s = s) (hT : S.T = T)
    (R : ∀ N, Main.Realization d N) (𝔈 : ℕ → ℝ)
    (hstand : Main.TorusStanding S R Rg ν₀ MB Λ VB (Main.gammaIdx d + 2) C₀ Cc 𝔈)
    (p : ℕ) (ts : Fin p → ℝ) (φ : Fin p → Torus d → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) T)
    (hφ : ∀ a, IsTrigPolyT (φ a))
    (m₀ : ℕ) (ε : ℕ → ℝ) (hinit : Main.InitialFluctuation S R m₀ Cin ε (fun _ => ∅))
    (εf : ℕ → ℝ) (ηF : ∀ N, (R N).Ω → NegSobolev d (Main.gammaIdx d : ℝ))
    (νin : Measure (NegSobolev d (Main.gammaIdx d : ℝ)))
    (hfield : Main.InitialFluctuationField S R (Main.gammaIdx d) Cin εf ηF νin)
    (L : Main.LimitCoeffs d)
    (hcoef : Main.CoeffConvergence S L Rg ν₀ MB Λ VB (Main.gammaIdx d + 2) (Main.gammaIdx d))
    (hεf : Tendsto εf atTop (𝓝 0)),
    ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
      (Y₀ : Ω' → NegSobolev d ((qT d : ℕ) : ℝ)) (Y : ℝ → Ω' → NegSobolev d ((qT d : ℕ) : ℝ)),
      Measurable Y₀ → law P' Y₀ = νin.map (NegSobolev.embed ((qT d : ℕ) : ℝ)) →
      HRS.IsLinearFluctuationSolution P' (L.dyn S) L.ρ ((qT d : ℕ) : ℝ) L.invβstar T
        (fun ζ => L.A • Y₀ ζ) Y →
      Main.ConvergesInLaw
        (fun N => Main.fluctStatLaw (R N).P (S.sigma N) (R N).X (S.ρ N) ts φ)
        (law P' (fun ζ => (WithLp.toLp 2 fun a => NegSobolev.eval (Y (ts a) ζ) (φ a) :
          EuclideanSpace ℝ (Fin p)))) := by
  sorry

/-- Lemma S.A.26, `ℝ^d` (`S:B:lem:path-fidi`, TeX S L10884-10891): under the hypotheses of the whole-space
path-space theorem S.A.9 (`HRS.Whole.AppendixA.main_rd_path`, copied: a selected field density `fd`,
`RdStanding` at the level `Γ + 5`, `B:ass:init` for the empty family (`InitialFluctuationRd`) and, for the finite family
at hand, the law-level convergence of the transported empirical initial vector (`EmpiricalInitialVectorConverges`;
statement repair MP-RD-REPAIRS-4 (C)(a), docs/ISSUES.md, 2026-10-19: it replaces the family-dependent `InitialFluctuationRd`
with `Ψ N` = the transported tests `U_N^{0,t_a}φ_a`, `transportedTestsRd`, whose `L¹` coupling the conclusion does not
use), `B:ass:init-field`(F-rd), the coefficient convergence
`Δ_N^{(Γ)} → 0`, `B:ass:rd-path-weighted` for the limit, the smallness `B:eq:rd-path-smallness` and the fixed-time
convergence `B:eq:rd-path-initial-fixed-time`): for finitely many times `t_a ∈ [0,T]` and Schwartz terminal tests
`φ_a`, `(⟨φ_a, Ξ_N^{t_a}⟩)_a ⟹ (⟨φ_a, η^{t_a}⟩)_a`, the law of the vector of any adjoint-duality solution
`Y` of the limiting equation (`IsAdjointDualityLimitW`, S.B.7, at the index `Γ + 2`, initial functional `η°` of the
fixed law `νη`).  AMBIGUITY: the TeX proof splits by field density (S.A.2, S.A.4, and an argument for decaying
super-Coulomb densities); the density is represented by `fd` and its package.
M3 (decision of 2026-10-22): the extra hypotheses (after `WeightedPathInput`; `Kad, Kst` explicit arguments, free constants of the hypotheses; the conclusion has no constant but `C₀min`, which may depend on them) are the field input `FieldAdjointInputRd fd S Kad` (classical solutions, `C_b^{m_*}` bound at the index `Γ` including `t_a = 0`, measurability), the same estimate for the limit (`AdjointInputOneD` at `Γ`, order `m_*`, constant `Kad`) and the stability input `AdjointStabilityInputRd` (`C_b^{m_*}`, data `H^{Γ+2}`, `Δ_N^{(Γ)}`) for the covariance limit.  For the decaying densities these inputs are S.A.16 content, not S.A.12 (S.A.12 covers the nondecaying density only). 
Repair S.A.26 (2026-10-24, approved, review pending): `AEMeasurable η₀ P'` is added after `law P' η₀ = νη`: at this Mathlib pin `Measure.map` of a non-a.e.-measurable map is an arbitrary fixed Dirac mass (not `0`), so `law P' η₀ = νη` does not force `η₀` to be a.e.-measurable, and the identification `law Z = law U ∗ law G` of the finite-dimensional laws has no proof without it (same repair as S.B.7 uniqueness `AEMeasurable η₁ P₁`).-/
theorem path_fidi_rd (s : ℝ) (fd : FieldDensityRd d s) (ν₀ MB Λ ΛV G₀ νbar T Cin m20 : ℝ)
    (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) (Kad Kst : ℝ) :
    ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ →
    ∀ (S : WholeMainData d), S.s = s → S.T = T → (∀ N, S.invβ N ≤ νbar) → fd.Holds S ν₀ →
    ∀ (R : ∀ N, RealizationRd d N) (𝔈 : ℕ → ℝ),
      RdStanding S R MB Λ ΛV G₀ m20 (fd.Gamma + 5) (fd.Gamma + 5) C₀ 𝔈 →
      ∀ m₂ : ℝ, 0 ≤ m₂ → PropagatedSecondMoment S R m₂ →
      ∀ (p : ℕ) (ts : Fin p → ℝ) (φ : Fin p → Euc d → ℝ), (∀ a, ts a ∈ Set.Icc (0 : ℝ) T) →
        (∀ a, ∃ ψ : SchwartzMap (Euc d) ℝ, ⇑ψ = φ a) →
      ∀ (m₀ : ℕ) (ε : ℕ → ℝ), InitialFluctuationRd S R χ m₀ Cin ε (fun _ => ∅) →
      ∀ (εf : ℕ → ℝ) (Iemp I : ∀ N, ℝ → (R N).Ω → HNeg d (fd.Gamma : ℝ)),
        TransportedInitialFieldRd S R fd.Gamma Cin εf Iemp I →
        InitialFieldDist S R fd.Gamma εf Iemp I →
      ∀ L : LimitCoeffsRd d, fd.HoldsAt S.s S.M L.invβ ν₀ →
        CoeffConvergenceRd S L MB Λ ΛV G₀ νbar (fd.Gamma + 2) fd.Gamma →
        EmpiricalInitialVectorConverges S R L ts φ →
      ∀ K : ℝ, WeightedPathInput S (L.coeff S) (m₀ + 1) (fd.Gamma + 2) K →
      FieldAdjointInputRd fd S Kad →
        AdjointInputOneD (fd.Gamma : ℝ) (mStar d) (L.coeff S) S.T Kad →
        AdjointStabilityInputRd S L (fd.Gamma + 2) (mStar d) fd.Gamma Kst →
      Tendsto (fun N => εf N + S.sigma N * (𝔈 N + fd.eN N) + S.qN N * wN d N (𝔈 N) m₂) atTop (𝓝 0) →
      TransportedConvergesFixedTime S R L (fd.Gamma + 2) →
      ∀ νη : Measure ((Euc d → ℝ) → ℝ), (∀ N : ℕ, 1 ≤ N → law (R N).P (R N).η = νη) →
        ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
          (η₀ : Ω' → (Euc d → ℝ) → ℝ) (Y : ℝ → Ω' → HNeg d ((fd.Gamma + 2 : ℕ) : ℝ)),
        law P' η₀ = νη →
        AEMeasurable η₀ P' →
        IsAdjointDualityLimitW P' (L.coeff S) ((fd.Gamma + 2 : ℕ) : ℝ) L.A L.invβstar T η₀ Y →
        HRS.Main.ConvergesInLaw
          (fun N => fluctStatLawRd (R N).P (S.sigma N) (R N).X (S.ρ N) ts φ)
          (law P' (fun ζ => (WithLp.toLp 2 fun a => HNeg.pairing (φ a) (Y (ts a) ζ) :
            EuclideanSpace ℝ (Fin p)))) := by
  sorry

/-! ### `B:cor:iid-init-path-rd` (S.A.27) -/

/-- The law on `C([0,T]; E)` of the path of a process (the true law when the path map is measurable). -/
def pathLaw {E : Type*} [NormedAddCommGroup E] {Ω : Type*} [MeasurableSpace Ω] (T : ℝ)
    (P : Measure Ω) (Z : ℝ → Ω → E) : Measure C(Set.Icc (0 : ℝ) T, E) :=
  P.map fun ζ => contPathOf T fun t => Z t ζ

/-- Corollary S.A.27 (`S:B:cor:iid-init-path-rd`, TeX S L10903-10912).  Assume `B:ass:rd-path-weighted` and the
path-level coefficient bounds and the hypotheses of `B:lem:iid-init-field-rd` (S.B.2): the i.i.d. setting
(`IidSettingRd`: `X_N^0 ∼ (μ°)^{⊗N}`, `κ_N = √N`, `η°` the Gaussian bridge, `∫|x|²dμ° < ∞`) with a selected
field density `fd` (`RdStanding` at the level `Γ + 5`, `B:eq:initial-second-moment`, `B:ass:init`(`∅` family),
`B:ass:init-field`(F-rd) with `InitialFieldDist`, `PathAdjointInput`).  Let `q_R = Γ + 2`, and `Zemp, Zη`
continuous versions in `H^{-q_R}(ℝ^d)` of the transported empirical and Gaussian initial fields `𝓘_{N,emp}^·`,
`𝓘_N^·` (`IsInitReprRd`; S.A.23 guarantees their existence).  Then, under the coefficient convergence of `B:cor:true-limit` (`CoeffConvergenceRd`,
`Δ_N^{(Γ)} → 0`; limit `LimitPathHyp`): (1) `Zemp ⟹ A(U_∞^{0,·})^*η°` and, as a *separate* assertion, (2)
`Zη ⟹ A(U_∞^{0,·})^*η°` and (3) the path laws of `Zemp` and of `Zη` are tight in `C([0,T];H^{-q_R})` (the TeX states
tightness without limit hypotheses; see the Repair note), all in `C([0,T];H^{-q_R}(ℝ^d))`, the limit being any continuous version `Jc` of the
transported field `A η°(U_∞^{0,t}·)` of a bridge `η°` on `(Ω',P')` (`IsGaussianBridgeW`).  (The last sentence of
the corollary, `B:eq:rd-path-initial-fixed-time`, is the fixed-time marginal of (2).)
Technical hypotheses: measurability of the path maps (so the laws are the true laws).
Repair S.A.27 (2026-10-24, option (A) approved, review pending): the tightness conclusions (1) and (2) are moved under the hypotheses of the convergence statement (they are now the last two conjuncts, stated after the limit hypotheses): without the coefficient convergence and the limit data nothing in the hypotheses gives fixed-time tightness in `H^{-(Γ+2)}(ℝ^d)` (the embedding `H^{-Γ} → H^{-Γ-2}` is not compact on `ℝ^d`); the TeX proof (S L10903-10912) obtains tightness from convergence by coefficient stability.  (On the Polish path space a weakly convergent sequence of probability measures is tight, so the two tightness conjuncts follow from the two convergence conjuncts.)
M3: the extra hypothesis `AdjointStabilityInputRd S L (Γ+2) (m₀+1) Γ Kst` (`Kst` a free constant, like `Kadj, Cw`) for the limiting coefficient, after `LimitPathHyp` (S.A.12(d) for the nondecaying density, S.A.16 stability for the decaying ones). -/
theorem iid_init_path_rd (s : ℝ) (fd : FieldDensityRd d s)
    (ν₀ MB Λ ΛV G₀ νbar T Cin C₀ m20 Kadj Cw Kst : ℝ) (m₀ : ℕ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) :
    ∀ (S : WholeMainData d), S.s = s → S.T = T → (∀ N, S.invβ N ≤ νbar) → fd.Holds S ν₀ →
    ∀ (R : ∀ N, RealizationRd d N) (𝔈 : ℕ → ℝ), IidSettingRd S R →
      RdStanding S R MB Λ ΛV G₀ m20 (fd.Gamma + 5) (fd.Gamma + 5) C₀ 𝔈 →
      PathAdjointInput S fd.Gamma m₀ Kadj Cw →
      ∀ (ε : ℕ → ℝ), InitialFluctuationRd S R χ m₀ Cin ε (fun _ => ∅) →
      ∀ (εf : ℕ → ℝ) (Iemp I : ∀ N, ℝ → (R N).Ω → HNeg d (fd.Gamma : ℝ)),
        TransportedInitialFieldRd S R fd.Gamma Cin εf Iemp I →
        InitialFieldDist S R fd.Gamma εf Iemp I →
      ∀ (Iq Jq Zemp Zη : ∀ N, ℝ → (R N).Ω → HNeg d ((fd.Gamma + 2 : ℕ) : ℝ)),
        IsInitReprRd S R (fd.Gamma + 2) Iq Jq →
        (∀ N : ℕ, 1 ≤ N → HasContVersion T (R N).P (Iq N) (Zemp N) ∧
          Measurable fun ζ => contPathOf T fun t => Zemp N t ζ) →
        (∀ N : ℕ, 1 ≤ N → HasContVersion T (R N).P (Jq N) (Zη N) ∧
          Measurable fun ζ => contPathOf T fun t => Zη N t ζ) →
      ∀ L : LimitCoeffsRd d, LimitPathHyp S L fd ν₀ Λ Kadj Cw m₀ →
        AdjointStabilityInputRd S L (fd.Gamma + 2) (m₀ + 1) fd.Gamma Kst →
        CoeffConvergenceRd S L MB Λ ΛV G₀ νbar (fd.Gamma + 2) fd.Gamma →
        ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
          (η' : Ω' → (Euc d → ℝ) → ℝ), IsGaussianBridgeW P' S.μ0 η' →
        ∀ (J Jc : ℝ → Ω' → HNeg d ((fd.Gamma + 2 : ℕ) : ℝ)), (∀ t, Measurable (J t)) →
          (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ φ : Euc d → ℝ, IsSobolevTest ((fd.Gamma + 2 : ℕ) : ℝ) φ →
            ∀ᵐ ζ ∂P', HNeg.pairing φ (J t ζ) = L.A * η' ζ (propagatorW (L.coeff S) 0 t φ)) →
          HasContVersion T P' J Jc → (Measurable fun ζ => contPathOf T fun t => Jc t ζ) →
          HRS.Main.ConvergesInLaw (fun N => pathLaw T (R N).P (Zemp N)) (pathLaw T P' Jc) ∧
          HRS.Main.ConvergesInLaw (fun N => pathLaw T (R N).P (Zη N)) (pathLaw T P' Jc) ∧
          IsTightMeasureSet {μ | ∃ N : ℕ, 1 ≤ N ∧ μ = pathLaw T (R N).P (Zemp N)} ∧
          IsTightMeasureSet {μ | ∃ N : ℕ, 1 ≤ N ∧ μ = pathLaw T (R N).P (Zη N)} := by
  sorry

/-! ### `B:cor:selected-law-selfsimilar` (S.A.28) -/

/-- The self-similar process `X̄_N^τ = e^{-τ/2} X_N^{e^τ - 1}` (`B:eq:selected-selfsimilar-process`). -/
def selfSimProcess {Ω : Type*} {N : ℕ} (X : ℝ≥0 → Ω → EucConfig d N) (τ : ℝ) (ζ : Ω) :
    EucConfig d N :=
  fun i => Real.exp (-τ / 2) • X (Real.toNNReal (Real.exp τ - 1)) ζ i

/-- `a_s(τ) = e^{-sτ/2}`. -/
def aSelfSim (s τ : ℝ) : ℝ := Real.exp (-s * τ / 2)

/-- `Ū_N^τ(Ξ) = (a_s(τ)/(2N)) ∑_{i≠j} g(ξ_i-ξ_j) + ¼ ∑_i |ξ_i|²` (`B:eq:selected-selfsimilar-potential`). -/
def selfSimPotential (d : ℕ) (s : ℝ) (N : ℕ) (τ : ℝ) (Ξ : EucConfig d N) : ℝ :=
  (aSelfSim s τ / (2 * N)) * ∑ i, ∑ j ∈ Finset.univ.erase i, rieszKernel d s (Ξ i - Ξ j) +
    (1 / 4) * ∑ i, ‖Ξ i‖ ^ 2

open Classical in
/-- `Ḡ_N^τ = e^{-β_N Ū_N^τ} 1_{𝔇_N^c}` (`β_N = invβ⁻¹`). -/
def selfSimWeight (d : ℕ) (s invβ : ℝ) (N : ℕ) (τ : ℝ) (Ξ : EucConfig d N) : ℝ :=
  if Ξ ∈ eucCollisionSet d N then 0 else Real.exp (-(invβ⁻¹) * selfSimPotential d s N τ Ξ)

/-- `Z_G = ∫ G dX` as a `lintegral` (the TeX convention `0 < Z_G < ∞`, M L12016). -/
def gibbsPartitionW {N : ℕ} (G : EucConfig d N → ℝ) : ℝ≥0∞ :=
  ∫⁻ X : EucConfig d N, ENNReal.ofReal (G X)

/-- The normalised reference measure `Z_G⁻¹ G dX` on `(ℝ^d)^N`. -/
def gibbsRefW {N : ℕ} (G : EucConfig d N → ℝ) : Measure (EucConfig d N) :=
  (gibbsPartitionW G)⁻¹ • (volume : Measure (EucConfig d N)).withDensity fun X => ENNReal.ofReal (G X)

/-- `𝓗_G(P) = H(P | Z_G⁻¹ G dX) - log Z_G` (`B:eq:gibbs-entropy-measure-convention`, M L12018), `EReal`-valued;
`+∞` when `P` is not absolutely continuous with respect to the normalised Gibbs measure (the whole-space
counterpart of `HRS.gibbsEntropy`). -/
def gibbsEntropyW {N : ℕ} (G : EucConfig d N → ℝ) (P : Measure (EucConfig d N)) : EReal :=
  ((relEntropy P (gibbsRefW G) : ℝ≥0∞) : EReal) -
    ((Real.log (gibbsPartitionW G).toReal : ℝ) : EReal)

/-- Test fields of the variational formula `B:eq:selected-fisher-variational` on `(ℝ^d)^N`: smooth
`ζ : (ℝ^d)^N → (ℝ^d)^N` with compact support in the collision-free configuration space `Ω_N`. -/
structure IsFisherTestFieldW {N : ℕ} (ζ : EucConfig d N → EucConfig d N) : Prop where
  smooth : ContDiff ℝ ∞ ζ
  support : ∃ K : Set (EucConfig d N), IsCompact K ∧ Disjoint K (eucCollisionSet d N) ∧
    ∀ X, X ∉ K → ζ X = 0

/-- The divergence `Div ζ = ∑_{i,a} ∂_{x_{ia}} ζ_{ia}` of a vector field on `(ℝ^d)^N`. -/
def configDivW {N : ℕ} (ζ : EucConfig d N → EucConfig d N) (X : EucConfig d N) : ℝ :=
  ∑ k : Fin N × Fin d, fderiv ℝ (fun Z : EucConfig d N => ζ Z k.1 k.2) X (configBasis d N k)

/-- The relative Fisher information `𝓘_G(P) = sup_ζ ∫(-2 Div ζ - 2 ζ·∇log G - |ζ|²) dP`, over `ζ ∈
C_c^∞(Ω_N; ℝ^{dN})` (`B:eq:selected-fisher-variational`, M L12205-12209), the lower-semicontinuous extension
(`ζ = 0` is admissible, so the supremum is `≥ 0`; `+∞` for measures without a Sobolev density). -/
def fisherInfoW {N : ℕ} (G : EucConfig d N → ℝ) (P : Measure (EucConfig d N)) : ℝ≥0∞ :=
  ⨆ (ζ : EucConfig d N → EucConfig d N) (_ : IsFisherTestFieldW ζ),
    ENNReal.ofReal (∫ X : EucConfig d N,
      (-2 * configDivW ζ X - 2 * fderiv ℝ (fun Z : EucConfig d N => Real.log (G Z)) X (ζ X) -
        ∑ i, ‖ζ X i‖ ^ 2) ∂P)

/-- Test functions `Φ ∈ C_c^{1,2}([0,T) × Ω_N)` of the weak forward equation (jointly `C²`, a subclass of
`C^{1,2}`, vanishing for `r ≥ T' < T`, supported in a compact subset of the collision-free space). -/
structure IsFKETestW {N : ℕ} (T : ℝ) (Φ : ℝ → EucConfig d N → ℝ) : Prop where
  smooth : ContDiff ℝ 2 (fun p : ℝ × EucConfig d N => Φ p.1 p.2)
  time_support : ∃ T' < T, ∀ r, T' ≤ r → ∀ X, Φ r X = 0
  space_support : ∃ K : Set (EucConfig d N), IsCompact K ∧ Disjoint K (eucCollisionSet d N) ∧
    ∀ r X, X ∉ K → Φ r X = 0

/-- The weak forward Kolmogorov equation on the collision-free configuration space of `ℝ^d`
(whole-space counterpart of `HRS.SolvesSelectedFKE`) for the diffusion `dX = b(r,X)dr + √(2ν) dW`:
for every `Φ ∈ C_c^{1,2}([0,T) × Ω_N)`,
`-∫Φ(0,·) dμ_0 = ∫_0^T ∫ (∂_rΦ + νΔΦ + ∑_i b_i·∇_iΦ) dμ_r dr`. -/
def SolvesFKEW {N : ℕ} (ν : ℝ) (b : ℝ → EucConfig d N → EucConfig d N) (T : ℝ)
    (μ : ℝ → Measure (EucConfig d N)) : Prop :=
  ∀ Φ : ℝ → EucConfig d N → ℝ, IsFKETestW T Φ →
    - ∫ x, Φ 0 x ∂(μ 0) = ∫ r in (0 : ℝ)..T, ∫ x,
      (deriv (fun r' => Φ r' x) r +
        ν * ∑ k : Fin N × Fin d, iteratedFDeriv ℝ 2 (Φ r) x ![configBasis d N k, configBasis d N k] +
        fderiv ℝ (Φ r) x (b r x)) ∂(μ r)

/-- Corollary S.A.28 (`S:B:cor:selected-law-selfsimilar`, TeX S L10931-10956): `𝔻 = ℝ^d`, `V ≡ 0`,
`M = -I`, `0 ≤ s < d`, `β_N < ∞` (`0 < invβ`), `X_N` the canonical selected particle process
(`SelectedFlowRd`, `B:ass:sde`, on `[0,T]`), `X̄_N^τ = e^{-τ/2}X_N^{e^τ-1}`, `Ū_N^τ`, `Ḡ_N^τ` as above,
and the selected initial law has a density (`law X₀ ≪ vol`) with `𝓗_{Ḡ_N^0}(f_N^0) < ∞`
(`B:eq:selected-selfsimilar-initial-entropy`).  Then, for the self-similar time `τ ∈ [0, log(1+T)]`
(i.e. `e^τ - 1 ≤ T`): every deterministic-time law of `X̄_N` has a density (`≪ vol`); the family solves the
self-similar forward Kolmogorov equation on the collision-free configuration space
(`SolvesFKEW` with the drift `-(a_s(τ)N⁻¹∑_{j≠i}∇g(ξ_i-ξ_j) + ½ξ_i)`, the SDE of S L10943-10945); the entropy
inequality `𝓗_{Ḡ^τ}(f̄^τ) + β_N⁻¹∫_0^τ 𝓘_{Ḡ^r}(f̄^r)dr ≤ 𝓗_{Ḡ^0}(f^0)` (`B:eq:selected-selfsimilar-entropy`) holds
(`EReal`); and `P_N^t = Law(X_N^t)` solves the unconfined forward equation on the collision-free space
(`SolvesFKEW` with drift `particleDriftW`).  The last sentence of the corollary ("its self-similar density
satisfies the entropy/Fisher-information inequality required in the smooth-approximation proof of [Rosenzweig,
Thm 1]; this holds for every `d, s`") is the entropy inequality just stated: the external citation itself is
not formalized.  The case `d = 1`, `s = 0` (collisional Cépa--Lépingle flow) is a disjunct of
`SelectedFlowRd`.  Technical hypotheses: `2 ≤ N`, `0 < T`. -/
theorem selected_law_selfsimilar (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (N : ℕ)
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
  sorry

/-! ### Remarks S.A.29 and S.A.30 -/

/- S.A.29 `S:B:rem:selfsimilar-initial-entropy` (TeX S L10958-10960): no formal content.  The remark says
that the initial entropy hypothesis `B:eq:selected-selfsimilar-initial-entropy` is "a convenient sufficient
hypothesis", "not asserted to be optimal", cites `B:prop:selected-law-smoothing` (a deterministic pairwise
distinct start gives an instantaneous smooth density: that proposition is a separate row) and says that a
global positive-time relative-entropy estimate "remains open"; it contains no checkable claim of its own.

   S.A.30 `S:B:rem:selected-law-scope` (TeX S L10987-10989): no formal content.  It describes the scope of
`B:prop:selected-law-fke`, `B:prop:selected-law-smoothing`, `B:prop:sde-entropy-law`,
`B:cor:selected-law-selfsimilar` (each a separate row, already stated or stated above), says that no
labelled forward equation across the collision diagonal is needed, and that for non-gradient flows "no
entropy structure is asserted or used" and at zero temperature the law is a pushforward (a pathwise
identity). -/

end HRS.Whole.AppendixALemmas
