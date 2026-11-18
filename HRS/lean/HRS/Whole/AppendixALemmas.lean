import HRS.Whole.AppendixBField
import HRS.Whole.AppendixA
import HRS.Energy.Coercivity
import HRS.Whole.Q09AAux2
import HRS.Whole.Q09AAux8
import HRS.Whole.Q09AAux9
import HRS.Whole.Q09BAux4

/-!
# Appendix S.A (whole-space supplement), lemmas S.A.18-S.A.21 and S.A.31-S.A.34 (SPEC-WA2)

Source: `HRS_whole_space_supplement_20261008T010000Z.tex` ("S"), Appendix S.A:

* S.A.18 `B:lem:moments` (L10478-10484): `moments_lemma`;
* S.A.19 `B:lem:test-cutoff` (L10506-10517): `test_cutoff_pathwise`, `test_cutoff_expectation`;
* S.A.20 `B:lem:adjoint-field-kernel` (L10562-10581): `adjoint_field_kernel`;
* S.A.21 `B:lem:path-tightness-criterion` (L10697-10704): `path_tightness_criterion`;
* S.A.31 `B:lem:uloc-embedding` (L11001-11007): `uloc_embedding_cutoffs`, `uloc_embedding_modes`,
  `uloc_embedding_cb`, `uloc_embedding_weighted`;
* S.A.32 `B:lem:uloc-bilip` (L11013-11020): `uloc_bilip`;
* S.A.33 `B:lem:uloc-uniqueness` (L11026-11028): `uloc_uniqueness`;
* S.A.34 `B:lem:expanding-tori` (L11058-11060): `expanding_tori_kernel`, `expanding_tori_coefficients`.

(S.A.22-S.A.30 are in `HRS/Whole/AppendixALemmas2.lean`.)

## Representation decisions (shared with `AppendixALemmas2.lean`)

* **Standing assumptions are those of `HRS/Whole/AppendixA.lean`** (SPEC-WA, S.A.2-S.A.17): the data
  `WholeMainData d` / `RealizationRd d N`, the package `RdStanding` (A.1, A.3, `|M| ≤ MB`, `V` with `m_V`
  derivatives, A.6, `B:eq:initial-second-moment`), `SelectedFlowRd`, `MeanFieldRegularityRd`, `VHypRd`,
  `EnergySmallnessRd`, `InitialFluctuationRd`, `TransportedInitialFieldRd`, `CoeffHypRd`, `ulocNormE`,
  `varpiNormE`, `PropagatedSecondMoment`, `wN`, `FieldDensityRd`, `WeightedPathInput`.  Only the notions
  absent there are defined here (listed with the declarations).
* `H^{-Γ}(ℝ^d)` is `HRS.Whole.HNeg` (SPEC-WB), with the smooth-test pairing `HNeg.pairing`; its real inner
  product is `HNeg.innerR` below.
* Expectations of possibly non-integrable quantities are `lintegral`s of `ENNReal.ofReal`; suprema over `t`
  of such expectations are `ℝ≥0∞`-valued.  `β_N = ∞` is `invβ N = 0`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff ComplexConjugate

open HRS.Whole.AppendixA

namespace HRS.Whole.AppendixALemmas

variable {d : ℕ}

/-! ### Coercivity on `ℝ^d` (`B:prop:coercivity`) -/

/-- `‖ψ‖_{Ḣ^a(ℝ^d)}² = ∫ (2π|ξ|)^{2a}|ψ̂|² dξ` is finite (`ψ ∈ L²`, Plancherel transform). -/
def HasFiniteHomSobolevRd (a : ℝ) (ψ : Euc d → ℝ) : Prop :=
  MemLp ψ 2 volume ∧
    Integrable fun ξ : Euc d => (2 * Real.pi * ‖ξ‖) ^ (2 * a) *
      ‖HRS.PDE.ToolboxRd.fourierL2 ψ ξ‖ ^ 2

/-- `‖ψ‖_{Ḣ^a(ℝ^d)} = (∫ (2π|ξ|)^{2a}|ψ̂|² dξ)^{1/2}` (meaningful under
`HasFiniteHomSobolevRd`). -/
def homSobolevRd (a : ℝ) (ψ : Euc d → ℝ) : ℝ :=
  Real.sqrt (∫ ξ : Euc d, (2 * Real.pi * ‖ξ‖) ^ (2 * a) *
    ‖HRS.PDE.ToolboxRd.fourierL2 ψ ξ‖ ^ 2)

/-- `B:prop:coercivity` on `ℝ^d` (M L2842-2857), the pair `(C₀, C)`: the lower bound
`CompletionNonnegRd d s C₀` (`HRS.Whole.AppendixA`: `F_N + o_N ≥ 0`, `o_N = oNΛ`) and, for every compactly
supported Lipschitz `ψ` (constant `L`) with finite `Ḣ^{(d-s)/2}` seminorm,
`|∫ψ d(μ_N - μ)| ≤ C λ L + C ‖ψ‖_{Ḣ^{(d-s)/2}} (F_N + o_N(Λ))^{1/2}` with `λ = (NΛ)^{-1/d}`
(`HRS.smearScale`).  (**Technical restriction**: compact support of `ψ`, so that the Plancherel
transform of `ψ` is the true one; this is the only class of tests used in `B:lem:test-cutoff`.)  Statement repair
(docs/ISSUES.md, 2026-10-19): at `s = 0` the densities carry a finite logarithmic moment (as in `CompletionNonnegRd`). -/
def WholeCoercivityPair (d : ℕ) (s C₀ C : ℝ) : Prop :=
  CompletionNonnegRd d s C₀ ∧ 0 < C ∧
    ∀ Λ : ℝ, 1 ≤ Λ → ∀ N : ℕ, 2 ≤ N → ∀ ρ : Euc d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
    (s = 0 → Integrable (fun x : Euc d => Real.log (2 + ‖x‖)) (withDensityReal ρ)) →
    ∀ X : EucConfig d N, Function.Injective X →
    ∀ (ψ : Euc d → ℝ) (L : ℝ), 0 ≤ L → HRS.PDE.ToolboxRd.IsLipschitz L ψ → HasCompactSupport ψ →
      HasFiniteHomSobolevRd (((d : ℝ) - s) / 2) ψ →
        |pair (empirical X) ψ - pair (withDensityReal ρ) ψ| ≤
          C * smearScale d N Λ * L + C * homSobolevRd (((d : ℝ) - s) / 2) ψ *
            Real.sqrt (rieszModulatedEnergy d s X (withDensityReal ρ) + oNΛ d s C₀ Λ N)

/-- `B:prop:coercivity` on `ℝ^d` (M L2842-2857) as an existence statement: for `1 ≤ d` and `0 ≤ s < d` there are
constants `C₀'` and `C₁`, depending only on `(d, s)`, such that `WholeCoercivityPair d s C₀ C₁` holds for every
`C₀ ≥ C₀'` (the pair is upward closed in `C₀`: the right side of the test bound and `oNΛ` increase with `C₀`;
`0 ≤ C₀'` because `CompletionNonnegRd` contains `0 ≤ C₀`).  The proof cited in the TeX is
Nguyen–Rosenzweig–Serfaty, arXiv:2107.02592, Prop. 2.4 (test bound), Rosenzweig–Serfaty, arXiv:2407.15650,
Eq. (2.29), and Hess-Childs–Rosenzweig, arXiv:2511.13461, Rem. 2.13 (lower bound).  New statement, added in the
repair of 2026-10-19 (docs/ISSUES.md); it supplies the hypothesis `WholeCoercivityPair d s C₀ C₁` of
`test_cutoff_pathwise`, `pathwise_core` and `test_cutoff_expectation` (S.A.19).  Not verified: the test bound for
`s < d - 2`, where the cited Proposition 2.4 may cover only `d - 2 ≤ s < d`. -/
theorem whole_coercivity_pair (d : ℕ) (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C₀' C₁ : ℝ, 0 ≤ C₀' ∧ ∀ C₀ : ℝ, C₀' ≤ C₀ → WholeCoercivityPair d s C₀ C₁ := by
  sorry

/-! ### Uniformly local norms, `𝒩(h)`, weighted Sobolev norms -/

/-- A cutoff `χ ∈ C_c^∞(B(0,ρ₂); [0,1])` with `χ ≡ 1` on `\overline{B(0,ρ₁)}`. -/
def IsCutoffRad (ρ₁ ρ₂ : ℝ) (χ : Euc d → ℝ) : Prop :=
  ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ Metric.ball (0 : Euc d) ρ₂ ∧
    (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧ ∀ x ∈ Metric.closedBall (0 : Euc d) ρ₁, χ x = 1

/-- The lattice variant `sup_{z} ‖χ(·-z)u‖_{H^m}` of `B:lem:uloc-embedding`(i), over the cell centres
`cellPt d z = ⌈√d⌉⁻¹ • ℤ^d`.  Statement repair `MS-ULOC-LAT` (docs/ISSUES.md, 2026-10-19): the unit lattice `ℤ^d` makes
the third conjunct of `uloc_embedding_cutoffs` false for `d ≥ 5`. -/
def ulNormLat (m : ℕ) (χ : Euc d → ℝ) (u : Euc d → ℝ) : ℝ≥0∞ :=
  ⨆ z : Fin d → ℤ, sobolevNormE (m : ℝ) fun x => χ (x - cellPt d z) * u x

/-- `‖h‖_{C_b^{0,1}} = ‖h‖_∞ + [h]_{Lip}` in `ℝ≥0∞` (`⊤` for unbounded or non-Lipschitz `h`). -/
def lipNormE (h : Euc d → ℝ) : ℝ≥0∞ :=
  (⨆ x, ENNReal.ofReal |h x|) +
    ⨆ p : {p : Euc d × Euc d // p.1 ≠ p.2}, ENNReal.ofReal (|h p.1.1 - h p.1.2| / ‖p.1.1 - p.1.2‖)

/-- `𝒩(h) = ‖h‖_{C_b^{0,1}} + ‖h‖_{H^{m_*-1}_uloc}` (`B:eq:test-cutoff`, S L10514-10516), `ℝ≥0∞`-valued,
with the generating cutoff `χ`. -/
def cNormE (χ : Euc d → ℝ) (h : Euc d → ℝ) : ℝ≥0∞ :=
  lipNormE h + ulocNormE (mStar d - 1) χ h

/-- `‖u‖_{H^m(ϖ)}² = ∑_{|α| ≤ m} ∫ ϖ |∂^α u|²` (S L11006-11007, proof of (iv); the sum runs over
ordered index tuples, an equivalent norm), in `ℝ≥0∞`. -/
def weightedHE (m : ℕ) (ϖ : Euc d → ℝ) (u : Euc d → ℝ) : ℝ≥0∞ :=
  (∑ j ∈ Finset.range (m + 1), ∑ i : Fin j → Fin d,
    ∫⁻ x, ENNReal.ofReal (ϖ x * (partialDeriv i u x) ^ 2)) ^ (1 / 2 : ℝ)

/-- `∑_{z ∈ ℤ^d} sup_{z+[0,1]^d} ϖ` (`B:lem:uloc-embedding`(iv)), in `ℝ≥0∞`. -/
def cellSupSum (ϖ : Euc d → ℝ) : ℝ≥0∞ :=
  ∑' z : Fin d → ℤ, ⨆ x ∈ {x : Euc d | ∀ i, latticePt z i ≤ x i ∧ x i ≤ latticePt z i + 1},
    ENNReal.ofReal (ϖ x)

/-- The real inner product of `H^{-Γ}(ℝ^d)`: `(F,G)_{H^{-Γ}} = Re ∫ conj(F̂) Ĝ (1+4π²|ξ|²)^{-Γ} dξ`
(the inner product inducing the `L²(ℂ; (1+4π²|ξ|²)^{-Γ}dξ)` norm of `HNeg`). -/
def HNeg.innerR {Γ : ℝ} (F G : HNeg d Γ) : ℝ :=
  (∫ ξ, conj (F.fourier ξ) * G.fourier ξ ∂(sobolevMeasure d Γ)).re

/-! ### `B:lem:moments` (S.A.18) -/

/-- Lemma S.A.18 (`S:B:lem:moments`, TeX S L10478-10484).  Assume `B:ass:sde`, `B:ass:mf-reg`,
`B:ass:MF`, `B:eq:V-assumption` and `B:eq:initial-second-moment` (the package `RdStanding`, with `r` the
regularity level of A.3 (unspecified in the lemma) and `m_V ≥ 2` (the proof only uses the bounded Hessian)).
Then `𝔪₂ := sup_N sup_{t ∈ [0,T]} E⟨|x|², μ_N^t + μ_{β_N}^t⟩ < ∞` and `𝔪₂ ≤ C(1 + 𝔪₂⁰)`: in the form of
`PropagatedSecondMoment` (the sup is at most the real number): for every bound `m20` of
`𝔪₂⁰` (`InitialSecondMoment`) the real number `C(1 + m20)` bounds `𝔪₂` (apply it to `m20 = 𝔪₂⁰`).
`C` is quantified before `m20` and the data; it depends only on `d, s, T`, `|M| ≤ MB`, `Λ`, `Λ_V`,
`|∇V(0)| ≤ G₀`, `β_N⁻¹ ≤ ν̄`, `r`, `m_V` and `Ē`.
Technical-looking hypothesis that is actually needed (SUSPECTED ISSUE, TeX L10496-10501): `𝔈_N ≤ Ē` for
all `N ≥ 1`.  The proof bounds the pair energy by `C(F_N + o_N + 1)` and uses `E[F_N + o_N] ≤ 𝔈_N`, so the
bound is uniform in `N` only if `sup_N 𝔈_N < ∞`; `B:ass:MF` gives only `σ_N 𝔈_N → 0`, which does not bound
`𝔈_N` when `σ_N` may tend to `0`.  `C` is chosen after `Ē`. -/
theorem moments_lemma (s : ℝ) (MB Λ ΛV G₀ νbar T Ē : ℝ) (r mV : ℕ) (hmV : 2 ≤ mV) :
    ∃ C : ℝ, ∀ (S : WholeMainData d), S.s = s → S.T = T → (∀ N, S.invβ N ≤ νbar) →
      ∀ (R : ∀ N, RealizationRd d N) (𝔈 : ℕ → ℝ) (C₀ m20 : ℝ),
        RdStanding S R MB Λ ΛV G₀ m20 r mV C₀ 𝔈 → (∀ N : ℕ, 1 ≤ N → 𝔈 N ≤ Ē) →
        PropagatedSecondMoment S R (C * (1 + m20)) :=
  HRS.Whole.Q09B.q09b_moments s MB Λ ΛV G₀ νbar T Ē r mV hmV

/-! ### `B:lem:test-cutoff` (S.A.19) -/

theorem cnorm_unpack (χ : Euc d → ℝ) (h : Euc d → ℝ) (hh : cNormE χ h < ⊤) :
    ∃ b l Uv : ℝ, 0 ≤ b ∧ 0 ≤ l ∧ 0 ≤ Uv ∧ (cNormE χ h).toReal = b + l + Uv ∧
      (∀ x, |h x| ≤ b) ∧ (∀ x y : Euc d, |h x - h y| ≤ l * ‖x - y‖) ∧
      ∀ z : Euc d, HRS.PDE.ToolboxRd.MemSobolev ((mStar d - 1 : ℕ) : ℝ) (fun x => χ (x - z) * h x) ∧
        HRS.PDE.ToolboxRd.sobolevNormSq ((mStar d - 1 : ℕ) : ℝ) (fun x => χ (x - z) * h x) ≤ Uv ^ 2 := by
  classical
  -- unpack the finiteness of `𝒩(h)`
  unfold cNormE lipNormE at hh ⊢
  set A : ℝ≥0∞ := ⨆ x : Euc d, ENNReal.ofReal |h x| with hA
  set Q : ℝ≥0∞ := ⨆ p : {p : Euc d × Euc d // p.1 ≠ p.2},
    ENNReal.ofReal (|h p.1.1 - h p.1.2| / ‖p.1.1 - p.1.2‖) with hQ
  set Um : ℝ≥0∞ := ulocNormE (mStar d - 1) χ h with hUm
  have hAQU : A + Q + Um < ⊤ := hh
  have hA' : A < ⊤ := lt_of_le_of_lt (le_self_add.trans le_self_add) hAQU
  have hQ' : Q < ⊤ := lt_of_le_of_lt (le_add_self.trans le_self_add) hAQU
  have hU' : Um < ⊤ := lt_of_le_of_lt le_add_self hAQU
  set b : ℝ := A.toReal with hbdef
  set l : ℝ := Q.toReal with hldef
  set Uv : ℝ := Um.toReal with hUvdef
  have hn : (A + Q + Um).toReal = b + l + Uv := by
    rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hA'.ne, hQ'.ne⟩) hU'.ne,
      ENNReal.toReal_add hA'.ne hQ'.ne]
  have hb0 : 0 ≤ b := ENNReal.toReal_nonneg
  have hl0 : 0 ≤ l := ENNReal.toReal_nonneg
  have hU0 : 0 ≤ Uv := ENNReal.toReal_nonneg
  have hbd : ∀ x, |h x| ≤ b := by
    intro x
    have : ENNReal.ofReal |h x| ≤ A := le_iSup (fun x : Euc d => ENNReal.ofReal |h x|) x
    exact (ENNReal.ofReal_le_iff_le_toReal hA'.ne).mp this
  have hlip : ∀ x y : Euc d, |h x - h y| ≤ l * ‖x - y‖ := by
    intro x y
    by_cases hxy : x = y
    · subst hxy; simp
    · have : ENNReal.ofReal (|h x - h y| / ‖x - y‖) ≤ Q :=
        le_iSup (fun p : {p : Euc d × Euc d // p.1 ≠ p.2} =>
          ENNReal.ofReal (|h p.1.1 - h p.1.2| / ‖p.1.1 - p.1.2‖)) ⟨(x, y), hxy⟩
      have h2 := (ENNReal.ofReal_le_iff_le_toReal hQ'.ne).mp this
      have hpos : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
      rw [div_le_iff₀ hpos] at h2
      exact h2
  have hSob : ∀ z : Euc d, HRS.PDE.ToolboxRd.MemSobolev ((mStar d - 1 : ℕ) : ℝ)
        (fun x => χ (x - z) * h x) ∧
      HRS.PDE.ToolboxRd.sobolevNormSq ((mStar d - 1 : ℕ) : ℝ) (fun x => χ (x - z) * h x) ≤ Uv ^ 2 := by
    intro z
    have h1 : sobolevNormE ((mStar d - 1 : ℕ) : ℝ) (fun x => χ (x - z) * h x) ≤ Um :=
      le_iSup (fun z : Euc d => sobolevNormE ((mStar d - 1 : ℕ) : ℝ) fun x => χ (x - z) * h x) z
    have h2 : sobolevNormE ((mStar d - 1 : ℕ) : ℝ) (fun x => χ (x - z) * h x) ≠ ⊤ :=
      ne_top_of_le_ne_top hU'.ne h1
    unfold sobolevNormE at h1 h2
    by_cases hM : HRS.PDE.ToolboxRd.MemSobolev ((mStar d - 1 : ℕ) : ℝ) (fun x => χ (x - z) * h x)
    · rw [if_pos hM] at h1
      refine ⟨hM, ?_⟩
      have h3 := (ENNReal.ofReal_le_iff_le_toReal hU'.ne).mp h1
      exact ((Real.sqrt_le_iff.mp h3).2)
    · rw [if_neg hM] at h2
      exact absurd rfl h2
  refine ⟨b, l, Uv, hb0, hl0, hU0, ?_, hbd, hlip, hSob⟩
  exact hn

theorem pathwise_core (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (χ : Euc d → ℝ)
    (K Lp : ℝ) (hK0 : 0 ≤ K) (hLp0 : 0 ≤ Lp)
    (hK : ∀ (N : ℕ) (h : Euc d → ℝ) (U : ℝ),
      (∀ z : Euc d, HRS.PDE.ToolboxRd.MemSobolev ((mStar d - 1 : ℕ) : ℝ) (fun x => χ (x - z) * h x) ∧
        HRS.PDE.ToolboxRd.sobolevNormSq ((mStar d - 1 : ℕ) : ℝ) (fun x => χ (x - z) * h x) ≤ U ^ 2) →
      HRS.PDE.ToolboxRd.MemSobolev ((mStar d - 1 : ℕ) : ℝ) (fun x => Q09A.plat d N x * h x) ∧
        HRS.PDE.ToolboxRd.sobolevNormSq ((mStar d - 1 : ℕ) : ℝ) (fun x => Q09A.plat d N x * h x) ≤
          K ^ 2 * ((2 * N + 1 : ℝ) ^ d) * U ^ 2)
    (hLp : ∀ (N : ℕ) (x y : Euc d), |Q09A.plat d N x - Q09A.plat d N y| ≤ Lp * ‖x - y‖)
    (C₁ C₀ : ℝ) (hpair : WholeCoercivityPair d s C₀ C₁)
    (Λ : ℝ) (hΛ : 1 ≤ Λ) (N : ℕ) (hN : 2 ≤ N) (ρ : Euc d → ℝ) (hρ : IsProbDensity ρ)
    (hρΛ : ∀ x, ρ x ≤ Λ) (hmom : Integrable (fun x => ‖x‖ ^ 2 * ρ x))
    (X : EucConfig d N) (hX : Function.Injective X) (h : Euc d → ℝ) (b l Uv : ℝ)
    (hb0 : 0 ≤ b) (hl0 : 0 ≤ l) (hU0 : 0 ≤ Uv) (hbd : ∀ x, |h x| ≤ b)
    (hlip : ∀ x y : Euc d, |h x - h y| ≤ l * ‖x - y‖)
    (hSob : ∀ z : Euc d, HRS.PDE.ToolboxRd.MemSobolev ((mStar d - 1 : ℕ) : ℝ) (fun x => χ (x - z) * h x) ∧
      HRS.PDE.ToolboxRd.sobolevNormSq ((mStar d - 1 : ℕ) : ℝ) (fun x => χ (x - z) * h x) ≤ Uv ^ 2)
    (R : ℝ) (hR : 1 ≤ R) :
    |pair (empirical X) h - pair (withDensityReal ρ) h| ≤
      (|C₁| * (Lp + 1) + |C₁| * (K * Real.sqrt (((2 * d + 5 : ℕ) : ℝ) ^ d)) + 1) * (b + l + Uv) *
        (R ^ ((d : ℝ) / 2) * (smearScale d N Λ +
            Real.sqrt (rieszModulatedEnergy d s X (withDensityReal ρ) + oNΛ d s C₀ Λ N)) +
          (secondMomentOf (empirical X) + secondMomentOf (withDensityReal ρ)) / R ^ 2) := by
  classical
  set n : ℝ := b + l + Uv with hndef
  have hn0 : 0 ≤ n := by positivity
  have hcont : Continuous h :=
    HRS.PDE.ToolboxRd.FourierAux.continuous_of_isLipschitz (L := l) hlip
  have hRpos : 0 < R := by linarith
  set Nr : ℕ := ⌈(d : ℝ) * R⌉₊ + 1 with hNr
  have hNr1 : (d : ℝ) * R + 1 ≤ Nr := by
    have := Nat.le_ceil ((d : ℝ) * R)
    rw [hNr]; push_cast; linarith
  have hNr2 : (Nr : ℝ) ≤ (d : ℝ) * R + 2 := by
    have := Nat.ceil_lt_add_one (show 0 ≤ (d : ℝ) * R by positivity)
    rw [hNr]; push_cast; linarith
  set ψ : Euc d → ℝ := fun x => Q09A.plat d Nr x * h x with hψdef
  have hplat_cont : Continuous (Q09A.plat d Nr) := (Q09A.plat_contDiff d Nr).continuous
  have hψcont : Continuous ψ := hplat_cont.mul hcont
  have hψlip : HRS.PDE.ToolboxRd.IsLipschitz ((Lp + 1) * n) ψ := by
    intro x y
    have h1 := hLp Nr x y
    have h2 := hbd x
    have h3 := hlip x y
    have hp1 := Q09A.plat_nonneg d Nr y
    have hp2 := Q09A.plat_le_one d Nr y
    have e : ψ x - ψ y = (Q09A.plat d Nr x - Q09A.plat d Nr y) * h x +
        Q09A.plat d Nr y * (h x - h y) := by simp only [hψdef]; ring
    rw [e]
    calc |(Q09A.plat d Nr x - Q09A.plat d Nr y) * h x + Q09A.plat d Nr y * (h x - h y)|
        ≤ |(Q09A.plat d Nr x - Q09A.plat d Nr y) * h x| + |Q09A.plat d Nr y * (h x - h y)| :=
          abs_add_le _ _
      _ ≤ Lp * ‖x - y‖ * b + 1 * (l * ‖x - y‖) := by
          rw [abs_mul, abs_mul, abs_of_nonneg hp1]
          gcongr
      _ ≤ (Lp + 1) * n * ‖x - y‖ := by
          have hxy := norm_nonneg (x - y)
          have : b ≤ n := by simp only [hndef]; linarith
          have : l ≤ n := by simp only [hndef]; linarith
          nlinarith [mul_nonneg hLp0 hxy, mul_nonneg hxy hb0, mul_nonneg hLp0 (mul_nonneg hxy hb0)]
  have hψsupp : HasCompactSupport ψ := by
    have hps : HasCompactSupport (Q09A.plat d Nr) :=
      HasCompactSupport.intro (isCompact_closedBall (0 : Euc d) ((Nr : ℝ) + 2)) fun x hx => by
        by_contra hne
        exact hx (by simpa using Q09A.plat_support hd hne)
    exact hps.mul_right
  -- the Sobolev bound
  obtain ⟨hMS, hnorm⟩ := hK Nr h Uv hSob
  have hRd : ((2 * (Nr : ℝ) + 1) ^ d) ≤ (((2 * d + 5 : ℕ) : ℝ) * R) ^ d := by
    apply pow_le_pow_left₀ (by positivity)
    push_cast
    nlinarith
  have hha : (d : ℝ) / 2 ≤ ((mStar d - 1 : ℕ) : ℝ) := by
    have : d ≤ 2 * (mStar d - 1) := by unfold mStar; omega
    have h2 : ((d : ℕ) : ℝ) ≤ 2 * ((mStar d - 1 : ℕ) : ℝ) := by exact_mod_cast this
    linarith
  have ha0 : 0 ≤ ((d : ℝ) - s) / 2 := by linarith
  have ha1 : ((d : ℝ) - s) / 2 ≤ ((mStar d - 1 : ℕ) : ℝ) := by linarith
  obtain ⟨hI, hIle⟩ := Q09A.hom_le hMS ha0 ha1
  have hHom : HasFiniteHomSobolevRd (((d : ℝ) - s) / 2) ψ := ⟨hMS.1, hI⟩
  have hhomle : homSobolevRd (((d : ℝ) - s) / 2) ψ ≤
      K * Real.sqrt (((2 * d + 5 : ℕ) : ℝ) ^ d) * R ^ ((d : ℝ) / 2) * n := by
    unfold homSobolevRd
    refine (Real.sqrt_le_sqrt (hIle.trans hnorm)).trans ?_
    have h1 : K ^ 2 * ((2 * (Nr : ℝ) + 1) ^ d) * Uv ^ 2 ≤
        (K * Real.sqrt (((2 * d + 5 : ℕ) : ℝ) ^ d) * R ^ ((d : ℝ) / 2) * n) ^ 2 := by
      have hs : Real.sqrt (((2 * d + 5 : ℕ) : ℝ) ^ d) ^ 2 = ((2 * d + 5 : ℕ) : ℝ) ^ d :=
        Real.sq_sqrt (by positivity)
      have hP : (R ^ ((d : ℝ) / 2)) ^ 2 = R ^ d := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hRpos.le]
        norm_num
      have hUn : Uv ≤ n := by simp only [hndef]; linarith
      calc K ^ 2 * ((2 * (Nr : ℝ) + 1) ^ d) * Uv ^ 2
          ≤ K ^ 2 * ((((2 * d + 5 : ℕ) : ℝ) * R) ^ d) * n ^ 2 := by
            gcongr
        _ = (K * Real.sqrt (((2 * d + 5 : ℕ) : ℝ) ^ d) * R ^ ((d : ℝ) / 2) * n) ^ 2 := by
            have e : (K * Real.sqrt (((2 * d + 5 : ℕ) : ℝ) ^ d) * R ^ ((d : ℝ) / 2) * n) ^ 2 =
                K ^ 2 * (Real.sqrt (((2 * d + 5 : ℕ) : ℝ) ^ d)) ^ 2 * (R ^ ((d : ℝ) / 2)) ^ 2 *
                  n ^ 2 := by ring
            rw [e, hs, hP]
            ring
    calc Real.sqrt (K ^ 2 * ((2 * (Nr : ℝ) + 1) ^ d) * Uv ^ 2)
        ≤ Real.sqrt ((K * Real.sqrt (((2 * d + 5 : ℕ) : ℝ) ^ d) * R ^ ((d : ℝ) / 2) * n) ^ 2) :=
          Real.sqrt_le_sqrt h1
      _ = _ := Real.sqrt_sq (by positivity)
  -- coercivity for the compactly supported part
  obtain ⟨-, hC1pos, hcoer⟩ := hpair
  have hcor := hcoer Λ hΛ N hN ρ hρ hρΛ (fun _ => Q09A.log_integrable_withDensityReal hρ hmom) X hX ψ ((Lp + 1) * n) (by positivity) hψlip hψsupp hHom
  -- the far part
  have hμprob : IsProbabilityMeasure (withDensityReal ρ) := Q09A.measure_isProb hρ
  have hfar : ∀ x : Euc d, |h x - ψ x| ≤ b * ‖x‖ ^ 2 / R ^ 2 := by
    intro x
    by_cases hx : ‖x‖ ≤ R
    · have : Q09A.plat d Nr x = 1 := Q09A.plat_eq_one hNr1 hx
      simp only [hψdef, this, one_mul, sub_self, abs_zero]
      positivity
    · push Not at hx
      have hp0 := Q09A.plat_nonneg d Nr x
      have hp1 := Q09A.plat_le_one d Nr x
      have hR2 : 1 ≤ ‖x‖ ^ 2 / R ^ 2 := by
        rw [le_div_iff₀ (by positivity)]
        nlinarith
      calc |h x - ψ x| = (1 - Q09A.plat d Nr x) * |h x| := by
            simp only [hψdef]
            rw [show h x - Q09A.plat d Nr x * h x = (1 - Q09A.plat d Nr x) * h x by ring, abs_mul,
              abs_of_nonneg (by linarith)]
        _ ≤ 1 * b := by
            gcongr
            · linarith
            · exact hbd x
        _ ≤ b * (‖x‖ ^ 2 / R ^ 2) := by nlinarith
        _ = b * ‖x‖ ^ 2 / R ^ 2 := by ring
  have hψb : ∀ x, |ψ x| ≤ b := by
    intro x
    simp only [hψdef]
    rw [abs_mul, abs_of_nonneg (Q09A.plat_nonneg d Nr x)]
    calc Q09A.plat d Nr x * |h x| ≤ 1 * b :=
          mul_le_mul (Q09A.plat_le_one d Nr x) (hbd x) (abs_nonneg _) zero_le_one
      _ = b := one_mul b
  have hN0 : 0 < N := by omega
  have hfarE : |pair (empirical X) h - pair (empirical X) ψ| ≤
      b * secondMomentOf (empirical X) / R ^ 2 :=
    Q09A.pair_far _ h ψ b R hfar (Q09A.integrable_empirical hN0 X _) (Q09A.integrable_empirical hN0 X _)
      (Q09A.integrable_empirical hN0 X _)
  have hfarM : |pair (withDensityReal ρ) h - pair (withDensityReal ρ) ψ| ≤
      b * secondMomentOf (withDensityReal ρ) / R ^ 2 :=
    Q09A.pair_far _ h ψ b R hfar
      (Integrable.of_bound hcont.aestronglyMeasurable b (Eventually.of_forall fun x => by
        simpa using hbd x))
      (Integrable.of_bound hψcont.aestronglyMeasurable b (Eventually.of_forall fun x => by
        simpa using hψb x))
      (Q09A.integrable_sq_withDensityReal hρ hmom)
  -- assemble
  set lam : ℝ := smearScale d N Λ with hlam
  set E0 : ℝ := Real.sqrt (rieszModulatedEnergy d s X (withDensityReal ρ) + oNΛ d s C₀ Λ N) with hE0
  set P : ℝ := R ^ ((d : ℝ) / 2) with hP
  set M : ℝ := secondMomentOf (empirical X) + secondMomentOf (withDensityReal ρ) with hM
  have hlam0 : 0 ≤ lam := by rw [hlam]; unfold smearScale; exact Real.rpow_nonneg (by positivity) _
  have hE00 : 0 ≤ E0 := Real.sqrt_nonneg _
  have hP1 : 1 ≤ P := Real.one_le_rpow hR (by positivity)
  have hM0 : 0 ≤ M := add_nonneg (Q09A.secondMomentOf_nonneg _) (Q09A.secondMomentOf_nonneg _)
  have hhom0 : 0 ≤ homSobolevRd (((d : ℝ) - s) / 2) ψ := Real.sqrt_nonneg _
  have hbn : b ≤ n := by simp only [hndef]; linarith
  set cc : ℝ := |C₁| with hcc
  set s0 : ℝ := Real.sqrt (((2 * d + 5 : ℕ) : ℝ) ^ d) with hs0def
  have hs00 : 0 ≤ s0 := Real.sqrt_nonneg _
  have hcc0 : 0 ≤ cc := abs_nonneg _
  have h1 : |pair (empirical X) ψ - pair (withDensityReal ρ) ψ| ≤
      cc * (Lp + 1) * n * lam + cc * (K * s0) * P * n * E0 := by
    refine hcor.trans ?_
    have e1 : C₁ * lam * ((Lp + 1) * n) ≤ cc * (Lp + 1) * n * lam := by
      calc C₁ * lam * ((Lp + 1) * n) = C₁ * (lam * ((Lp + 1) * n)) := by ring
        _ ≤ |C₁| * (lam * ((Lp + 1) * n)) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
        _ = cc * (Lp + 1) * n * lam := by rw [hcc]; ring
    have e2 : C₁ * homSobolevRd (((d : ℝ) - s) / 2) ψ * E0 ≤ cc * (K * s0) * P * n * E0 := by
      calc C₁ * homSobolevRd (((d : ℝ) - s) / 2) ψ * E0
          ≤ |C₁| * homSobolevRd (((d : ℝ) - s) / 2) ψ * E0 := by
            gcongr
            exact le_abs_self _
        _ ≤ |C₁| * (K * s0 * P * n) * E0 := by gcongr
        _ = cc * (K * s0) * P * n * E0 := by rw [hcc]; ring
    linarith
  have h2 : |pair (empirical X) h - pair (empirical X) ψ| + |pair (withDensityReal ρ) h -
      pair (withDensityReal ρ) ψ| ≤ n * M / R ^ 2 := by
    refine (add_le_add hfarE hfarM).trans ?_
    rw [← add_div, ← mul_add]
    gcongr
  have htri : |pair (empirical X) h - pair (withDensityReal ρ) h| ≤
      |pair (empirical X) ψ - pair (withDensityReal ρ) ψ| +
      (|pair (empirical X) h - pair (empirical X) ψ| +
        |pair (withDensityReal ρ) h - pair (withDensityReal ρ) ψ|) := by
    have e : pair (empirical X) h - pair (withDensityReal ρ) h =
        (pair (empirical X) ψ - pair (withDensityReal ρ) ψ) +
        (pair (empirical X) h - pair (empirical X) ψ) -
        (pair (withDensityReal ρ) h - pair (withDensityReal ρ) ψ) := by ring
    rw [e]
    have h1 := abs_sub ((pair (empirical X) ψ - pair (withDensityReal ρ) ψ) +
        (pair (empirical X) h - pair (empirical X) ψ))
      (pair (withDensityReal ρ) h - pair (withDensityReal ρ) ψ)
    have h2 := abs_add_le (pair (empirical X) ψ - pair (withDensityReal ρ) ψ)
      (pair (empirical X) h - pair (empirical X) ψ)
    linarith
  have key := Q09A.final_ineq cc (Lp + 1) K s0 n lam E0 P M R hcc0 (by linarith) hK0 hs00 hn0 hlam0 hE00 hP1 hM0
  calc |pair (empirical X) h - pair (withDensityReal ρ) h|
      ≤ |pair (empirical X) ψ - pair (withDensityReal ρ) ψ| +
        (|pair (empirical X) h - pair (empirical X) ψ| +
          |pair (withDensityReal ρ) h - pair (withDensityReal ρ) ψ|) := htri
    _ ≤ (cc * (Lp + 1) * n * lam + cc * (K * s0) * P * n * E0) + n * M / R ^ 2 := by
        gcongr
    _ ≤ _ := key

/-- Lemma S.A.19 (`S:B:lem:test-cutoff`, TeX S L10506-10517), the pathwise inequality
`B:eq:test-cutoff`.  For a real `h ∈ C_b^{0,1}(ℝ^d) ∩ H^{m_*-1}_uloc(ℝ^d)` (`𝒩(h) < ∞`), every `R ≥ 1`:
`|⟨h, μ_N - μ⟩| ≤ C 𝒩(h) [R^{d/2}(λ_N + (F_N(X_N,μ) + o_N)^{1/2}) + ⟨|x|²/R², μ_N + μ⟩]`,
`λ_N = (NΛ)^{-1/d}` (`HRS.smearScale`), `o_N = o_N(Λ)` (`HRS.oNΛ`).  The inequality is a deterministic
statement about a pairwise distinct configuration `X_N` and a probability density `μ ≤ Λ`
(`Λ ≥ 1`, `N ≥ 2`, so that `λ_N < 1`); the trajectory `(X_N^t, μ^t)` is a special case.  It is derived
from `B:prop:coercivity`(ii), represented by the hypothesis `WholeCoercivityPair d s C₀ C₁` (the pair
`(C₀, C)` of the proposition, constants depending only on `d, s`); `C` depends only on `d, s, C₁`
and the cutoff `χ`.
Technical hypotheses: `0 ≤ s < d`, `1 ≤ d`; `μ` has a finite second moment (so that
`⟨|x|²/R², μ⟩` is not the junk value `0`). -/
theorem test_cutoff_pathwise (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) (C₁ : ℝ) :
    ∃ C : ℝ, ∀ C₀ : ℝ, WholeCoercivityPair d s C₀ C₁ →
      ∀ Λ : ℝ, 1 ≤ Λ → ∀ N : ℕ, 2 ≤ N → ∀ ρ : Euc d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      Integrable (fun x => ‖x‖ ^ 2 * ρ x) →
      ∀ X : EucConfig d N, Function.Injective X →
      ∀ h : Euc d → ℝ, cNormE χ h < ⊤ → ∀ R : ℝ, 1 ≤ R →
        |pair (empirical X) h - pair (withDensityReal ρ) h| ≤
          C * (cNormE χ h).toReal *
            (R ^ ((d : ℝ) / 2) * (smearScale d N Λ +
                Real.sqrt (rieszModulatedEnergy d s X (withDensityReal ρ) + oNΛ d s C₀ Λ N)) +
              (secondMomentOf (empirical X) + secondMomentOf (withDensityReal ρ)) / R ^ 2) := by
  classical
  have hm1 : 1 ≤ mStar d - 1 := by unfold mStar; omega
  obtain ⟨K, hK0, hK⟩ := Q09A.sobolev_plat_bound hd hm1 χ hχ.2.2.2.2
  obtain ⟨Lp, hLp0, hLp⟩ := Q09A.plat_lipschitz d
  refine ⟨|C₁| * (Lp + 1) + |C₁| * (K * Real.sqrt (((2 * d + 5 : ℕ) : ℝ) ^ d)) + 1,
    fun C₀ hpair Λ hΛ N hN ρ hρ hρΛ hmom X hX h hh R hR => ?_⟩
  obtain ⟨b, l, Uv, hb0, hl0, hU0, hn, hbd, hlip, hSob⟩ := cnorm_unpack χ h hh
  rw [hn]
  exact pathwise_core hd s hs0 hsd χ K Lp hK0 hLp0 hK hLp C₁ C₀ hpair Λ hΛ N hN ρ hρ hρΛ hmom X hX h
    b l Uv hb0 hl0 hU0 hbd hlip hSob R hR


/-- Lemma S.A.19 (`S:B:lem:test-cutoff`, TeX S L10506-10517), the consequence "`sup_{t ≤ T}
E|⟨h, Fluc_N^t⟩| ≤ C 𝒩(h) 𝔴_N`", `Fluc_N^t = μ_N^t - μ_{β_N}^t`.  Standing assumptions: `RdStanding`
(A.1, A.3, `V`, A.6, `B:eq:initial-second-moment`) with a completion constant `C₀` such that
`WholeCoercivityPair d s C₀ C₁`; `𝔴_N = wN d N 𝔈_N m₂` with a real `m₂` bounding the propagated second
moment (`PropagatedSecondMoment`, `m₂ = 𝔪₂` is the finite value of S.A.18; `wN` is monotone in `m₂`).  `C` depends
only on the bounds listed before it (`d, s, T, MB, Λ, Λ_V, G₀, ν̄, C₁, χ, r, m_V`), not on `N, h, m₂`.
Technical hypotheses: `1 ≤ Λ` (so `λ_N < 1`); `X_N^t` a.s. pairwise distinct at each fixed `t` (automatic in case
(a) of `B:ass:sde`, a.s. for deterministic times in (b), (c)); `2 ≤ N`; `𝒩(h) < ∞`. -/
theorem test_cutoff_expectation (s : ℝ) (MB Λ ΛV G₀ νbar T : ℝ) (hΛ : 1 ≤ Λ) (χ : Euc d → ℝ)
    (hχ : IsUlocCutoff χ) (C₁ : ℝ) (r mV : ℕ) (hmV : 2 ≤ mV) :
    ∃ C : ℝ, ∀ (S : WholeMainData d), S.s = s → S.T = T → (∀ N, S.invβ N ≤ νbar) →
      ∀ (R : ∀ N, RealizationRd d N) (𝔈 : ℕ → ℝ) (C₀ m20 : ℝ),
        RdStanding S R MB Λ ΛV G₀ m20 r mV C₀ 𝔈 → WholeCoercivityPair d s C₀ C₁ →
      ∀ m₂ : ℝ, PropagatedSecondMoment S R m₂ →
      (∀ N : ℕ, 1 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ζ ∂(R N).P,
        (R N).X (Real.toNNReal t) ζ ∉ eucCollisionSet d N) →
      ∀ h : Euc d → ℝ, cNormE χ h < ⊤ → ∀ N : ℕ, 2 ≤ N →
        ⨆ t ∈ Set.Icc (0 : ℝ) T,
          ∫⁻ ζ, ENNReal.ofReal (|pair (empirical ((R N).X (Real.toNNReal t) ζ)) h -
              pair (withDensityReal (S.ρ N t)) h|) ∂(R N).P ≤
          ENNReal.ofReal (C * (cNormE χ h).toReal * wN d N (𝔈 N) m₂) := by
  classical
  by_cases hgood : 1 ≤ d ∧ 0 ≤ s ∧ s < d
  swap
  · refine ⟨0, fun S hSs => ?_⟩
    exact absurd ⟨S.hd, hSs ▸ S.hs0, hSs ▸ S.hsd⟩ hgood
  obtain ⟨hd, hs0, hsd⟩ := hgood
  obtain ⟨Cp, hCp⟩ := test_cutoff_pathwise hd s hs0 hsd χ hχ C₁
  refine ⟨max Cp 0, fun S hSs hST hν Rl 𝔈 C₀ m20 hstd hpair m₂ hm2 hcol h hh N hN => ?_⟩
  have hN1 : 1 ≤ N := by omega
  have hN0 : 0 < N := by omega
  refine iSup₂_le fun t ht => ?_
  have ht' : t ∈ Set.Icc (0 : ℝ) S.T := by rwa [hST]
  set n : ℝ := (cNormE χ h).toReal with hn
  have hn0 : 0 ≤ n := ENNReal.toReal_nonneg
  have hC0 : 0 ≤ max Cp 0 := le_max_right _ _
  -- data of the mean-field density
  have hsol := hstd.mean_field.solution N hN1
  have hprob : IsProbDensity (S.ρ N t) := hsol.density t ht'
  have hmom : Integrable (fun x => ‖x‖ ^ 2 * S.ρ N t x) := hsol.second_moment t ht'
  have hρΛ : ∀ x, S.ρ N t x ≤ Λ := by
    obtain ⟨hmem, -, hle⟩ := (hstd.mean_field.regular N hN1).1 t ht'
    exact Q09A.rho_le_of_cbNorm hmem ENNReal.toReal_nonneg hle
  have : IsProbabilityMeasure (Rl N).P := (Rl N).isProb
  have hmeasX : Measurable ((Rl N).X (Real.toNNReal t)) :=
    Q09A.selectedFlow_measurable (hstd.flow N hN1) _
  have hmeas_m : Measurable fun ζ => secondMomentOf (empirical ((Rl N).X (Real.toNNReal t) ζ)) :=
    Q09A.measurable_secondMoment_empirical hN0 hmeasX
  -- the second-moment bound `m₂` is nonnegative
  have hm2pos : 0 < secondMomentOf (withDensityReal (S.ρ N t)) :=
    Q09A.secondMoment_withDensity_pos hd hprob hmom
  have hm₂ : 0 ≤ m₂ := by
    have h1 := hm2 N hN1 t ht'
    have h2 : ENNReal.ofReal (secondMomentOf (withDensityReal (S.ρ N t))) ≤
        ∫⁻ ζ, ENNReal.ofReal (secondMomentOf (empirical ((Rl N).X (Real.toNNReal t) ζ)) +
          secondMomentOf (withDensityReal (S.ρ N t))) ∂(Rl N).P := by
      calc ENNReal.ofReal (secondMomentOf (withDensityReal (S.ρ N t)))
          = ∫⁻ _ζ, ENNReal.ofReal (secondMomentOf (withDensityReal (S.ρ N t))) ∂(Rl N).P := by
            simp
        _ ≤ _ := lintegral_mono fun ζ => ENNReal.ofReal_le_ofReal
            (by have := Q09A.secondMomentOf_nonneg (empirical ((Rl N).X (Real.toNNReal t) ζ))
                linarith)
    have h3 := h2.trans h1
    have h4 : 0 < ENNReal.ofReal m₂ :=
      lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hm2pos) h3
    exact (ENNReal.ofReal_pos.mp h4).le
  have h𝔈 : 0 < 𝔈 N := hstd.energy.pos N hN1
  have hΛ0 : 0 < Λ := by linarith
  -- the bound for each cutoff scale
  have hbound : ∀ R : {R : ℝ // 1 ≤ R},
      ∫⁻ ζ, ENNReal.ofReal (|pair (empirical ((Rl N).X (Real.toNNReal t) ζ)) h -
          pair (withDensityReal (S.ρ N t)) h|) ∂(Rl N).P ≤
        ENNReal.ofReal ((max Cp 0) * n * (R.1 ^ ((d : ℝ) / 2) *
          ((N : ℝ) ^ (-(1 : ℝ) / d) + (𝔈 N) ^ ((1 : ℝ) / 2)) + m₂ / R.1 ^ 2)) := by
    intro R
    have hR1 : 1 ≤ R.1 := R.2
    have hR0 : 0 < R.1 := by linarith
    refine le_trans (Q09A.lintegral_bound (Rl N).P
      (fun ζ => pair (empirical ((Rl N).X (Real.toNNReal t) ζ)) h -
          pair (withDensityReal (S.ρ N t)) h)
      (fun ζ => correctedEnergyRd S C₀ Λ N ((Rl N).X (Real.toNNReal t) ζ) t)
      (fun ζ => secondMomentOf (empirical ((Rl N).X (Real.toNNReal t) ζ)) +
        secondMomentOf (withDensityReal (S.ρ N t)))
      (hmeas_m.add_const _) ((max Cp 0) * n) (R.1 ^ ((d : ℝ) / 2)) (smearScale d N Λ) R.1 (𝔈 N)
      m₂ (mul_nonneg hC0 hn0) (Real.rpow_nonneg hR0.le _) ?_ hR0 h𝔈 hm₂ ?_ ?_ ?_ (hm2 N hN1 t ht') ?_)
      (ENNReal.ofReal_le_ofReal ?_)
    · unfold smearScale
      exact Real.rpow_nonneg (by positivity) _
    · filter_upwards [hcol N hN1 t ht] with ζ hζ
      exact (hstd.energy.completion.2 Λ hΛ N hN (S.ρ N t) hprob hρΛ (fun _ => Q09A.log_integrable_withDensityReal hprob hmom) _ hζ |> fun h0 => by
        simpa only [correctedEnergyRd, hSs] using h0)
    · intro ζ
      have := Q09A.secondMomentOf_nonneg (empirical ((Rl N).X (Real.toNNReal t) ζ))
      linarith
    · exact hstd.energy.bound N hN1 t ht'
    · filter_upwards [hcol N hN1 t ht] with ζ hζ
      have hinj : Function.Injective ((Rl N).X (Real.toNNReal t) ζ) := by
        intro i j hij
        by_contra hne
        exact hζ ⟨i, j, hne, hij⟩
      have key := hCp C₀ hpair Λ hΛ N hN (S.ρ N t) hprob hρΛ hmom _ hinj h hh R.1 hR1
      simp only [correctedEnergyRd, hSs]
      refine key.trans ?_
      have hb : 0 ≤ R.1 ^ ((d : ℝ) / 2) * (smearScale d N Λ +
          Real.sqrt (rieszModulatedEnergy d s ((Rl N).X (Real.toNNReal t) ζ)
            (withDensityReal (S.ρ N t)) + oNΛ d s C₀ Λ N)) +
          (secondMomentOf (empirical ((Rl N).X (Real.toNNReal t) ζ)) +
            secondMomentOf (withDensityReal (S.ρ N t))) / R.1 ^ 2 := by
        have := Q09A.secondMomentOf_nonneg (empirical ((Rl N).X (Real.toNNReal t) ζ))
        have := Q09A.secondMomentOf_nonneg (withDensityReal (S.ρ N t))
        have : 0 ≤ smearScale d N Λ := by
          unfold smearScale; exact Real.rpow_nonneg (by positivity) _
        positivity
      calc Cp * n * _ = Cp * (n * _) := by ring
        _ ≤ max Cp 0 * (n * _) := mul_le_mul_of_nonneg_right (le_max_left _ _)
            (mul_nonneg hn0 hb)
        _ = _ := by ring
    · -- compare with the constant of `wN`
      have h1 : smearScale d N Λ ≤ (N : ℝ) ^ (-(1 : ℝ) / d) := by
        unfold smearScale
        refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ ?_
        · have : (1 : ℝ) ≤ Λ := hΛ
          have : (0 : ℝ) < N := by exact_mod_cast hN0
          nlinarith
        · have : (0 : ℝ) ≤ 1 / (d : ℝ) := by positivity
          rw [neg_div]; linarith
      have h2 : Real.sqrt (𝔈 N) = (𝔈 N) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow _
      rw [h2]
      have h3 : 0 ≤ R.1 ^ ((d : ℝ) / 2) := Real.rpow_nonneg hR0.le _
      have h4 : 0 ≤ (max Cp 0) * n := mul_nonneg hC0 hn0
      have := mul_le_mul_of_nonneg_left (add_le_add_right h1 ((𝔈 N) ^ ((1 : ℝ) / 2))) h3
      exact mul_le_mul_of_nonneg_left (by linarith) h4
  unfold wN
  refine Q09A.inf_bound _ ?_ _ _ (mul_nonneg hC0 hn0) hbound
  intro R
  have hR0 : 0 < R.1 := by have := R.2; linarith
  have : 0 ≤ (N : ℝ) ^ (-(1 : ℝ) / d) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have : 0 ≤ (𝔈 N) ^ ((1 : ℝ) / 2) := Real.rpow_nonneg h𝔈.le _
  positivity

/-! ### `B:lem:adjoint-field-kernel` (S.A.20) -/

/-- Lemma S.A.20 (`S:B:lem:adjoint-field-kernel`, TeX S L10562-10581).  For a field density `(𝒳, Γ)`
(represented by the index `Γ` and `AdjointDerivInput` at the order `j = m_*`, see there), `1 ≤ j ≤ d`,
`0 ≤ r ≤ t ≤ T`, `x ∈ ℝ^d`, `|α| ≤ m_* - 1`:
(1) there is a unique `K^{(α)}_{N,j}{}^{r,t}(x) ∈ H^{-Γ}(ℝ^d)` with `⟨φ, K^{(α)}⟩ = ∂^α∂_jU_N^{r,t}φ(x)` for
smooth `φ ∈ H^Γ` (a dense class; `α = 0` is `K_{N,j}^{r,t}(x)` of `B:eq:intrinsic-kernel`; for general `α`
this is the Riesz representative of the differentiated evaluation functional, which is what the TeX proves
for `∂_x^αK` in `B:eq:intrinsic-kernel-bound`: "applying it to the differentiated evaluation functional");
(2) `‖K^{(α)}‖_{H^{-Γ}} ≤ C` uniformly in `N, r, t, x`;
for every family `K = K^{(0)}`: (3) `(r,t,x) ↦ K_{N,j}^{r,t}(x)` is measurable on `{0 ≤ r ≤ t ≤ T} × ℝ^d`
(`H^{-Γ}` is separable, so this is strong measurability), and (4) for self-adjoint `B ∈ L(H^{-Γ})` with
`‖B‖ ≤ 1`, `h_{B,r}(x) := ∑_j (B K_{N,j}^{r,t}(x), K_{N,j}^{r,t}(x))_{H^{-Γ}}` has `𝒩(h_{B,r}) ≤ C` (cutoff `χ`).
`C` depends only on `d, Γ, T, K` (the constant of the adjoint input) and `χ`.
AMBIGUITY: the TeX writes `∂_x^αK ∈ H^{-Γ}` and then differentiates `h_{B,r}` by the Leibniz rule; the
differentiation of `x ↦ K(x)` in the norm of `H^{-Γ}` (with derivative `K^{(e_i)}`) is not part of (1)-(2), it is the
step of the TeX proof "differentiating `h_{B,r}` and applying Cauchy-Schwarz", and its conclusion is (4).  `Γ ∈ ℕ`.
Repair P9 (2026-10-20): the extra hypothesis is the joint measurability of `(r,t,x) ↦ ∂_jU^{r,t}φ(x)` for each test `φ` (the TeX's "the
unique solution is continuous in `t`", L10574-10575); `propagatorW` is a separate `choose` for each `(t,φ)`, so nothing in
`AdjointDerivInput` links them and (3) (Pettis, via a countable dense family of tests) is not derivable without it. -/
theorem adjoint_field_kernel (Γ : ℕ) (T K : ℝ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) :
    ∃ C : ℝ, ∀ Cf : ℕ → WholeCoeff d, AdjointDerivInput (Γ : ℝ) (mStar d) Cf T K →
      (∀ N : ℕ, 1 ≤ N → ∀ (j : Fin d) (φ : Euc d → ℝ), IsSobolevTest (Γ : ℝ) φ →
        Measurable (fun p : {p : ℝ × ℝ × Euc d // 0 ≤ p.1 ∧ p.1 ≤ p.2.1 ∧ p.2.1 ≤ T} =>
          partialDeriv (fun _ : Fin 1 => j) (propagatorW (Cf N) p.1.1 p.1.2.1 φ) p.1.2.2)) →
      (∀ N : ℕ, 1 ≤ N → ∀ (j : Fin d) (l : ℕ), l ≤ mStar d - 1 → ∀ i : Fin l → Fin d,
        ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T → ∀ x : Euc d,
          ∃! k : HNeg d (Γ : ℝ), ∀ φ : Euc d → ℝ, IsSobolevTest (Γ : ℝ) φ →
            HNeg.pairing φ k = partialDeriv (Fin.cons j i : Fin (l + 1) → Fin d)
              (propagatorW (Cf N) r t φ) x) ∧
      (∀ N : ℕ, 1 ≤ N → ∀ (j : Fin d) (l : ℕ), l ≤ mStar d - 1 → ∀ i : Fin l → Fin d,
        ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T → ∀ x : Euc d, ∀ k : HNeg d (Γ : ℝ),
          (∀ φ : Euc d → ℝ, IsSobolevTest (Γ : ℝ) φ →
            HNeg.pairing φ k = partialDeriv (Fin.cons j i : Fin (l + 1) → Fin d)
              (propagatorW (Cf N) r t φ) x) → ‖k‖ ≤ C) ∧
      ∀ Kern : ℕ → ℝ → ℝ → Euc d → Fin d → HNeg d (Γ : ℝ),
        (∀ N : ℕ, 1 ≤ N → ∀ (j : Fin d) (r t : ℝ), 0 ≤ r → r ≤ t → t ≤ T → ∀ x : Euc d,
          ∀ φ : Euc d → ℝ, IsSobolevTest (Γ : ℝ) φ →
            HNeg.pairing φ (Kern N r t x j) =
              partialDeriv (fun _ : Fin 1 => j) (propagatorW (Cf N) r t φ) x) →
        (∀ N : ℕ, 1 ≤ N → ∀ j : Fin d,
          Measurable (fun p : {p : ℝ × ℝ × Euc d // 0 ≤ p.1 ∧ p.1 ≤ p.2.1 ∧ p.2.1 ≤ T} =>
            Kern N p.1.1 p.1.2.1 p.1.2.2 j)) ∧
        ∀ (B : HNeg d (Γ : ℝ) →L[ℝ] HNeg d (Γ : ℝ)), (∀ u v, HNeg.innerR (B u) v = HNeg.innerR u (B v)) →
          ‖B‖ ≤ 1 → ∀ N : ℕ, 1 ≤ N → ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T →
            cNormE χ (fun x => ∑ j : Fin d, HNeg.innerR (B (Kern N r t x j)) (Kern N r t x j)) ≤
              ENNReal.ofReal C := by
  sorry

/-! ### `B:lem:path-tightness-criterion` (S.A.21) -/

/-- `ω_E(z, δ) = sup_{s,t ∈ [0,T], |t-s| ≤ δ} ‖z(t) - z(s)‖_E` (S L10690-10695), in `ℝ≥0∞`
(so that "`ω_E > ε`" means `∃ s t, |t-s| ≤ δ ∧ ‖z t - z s‖ > ε`, with no junk value for unbounded
paths). -/
def omegaE {E : Type*} [NormedAddCommGroup E] (z : ℝ → E) (T δ : ℝ) : ℝ≥0∞ :=
  ⨆ s ∈ Set.Icc (0 : ℝ) T, ⨆ t ∈ Set.Icc (0 : ℝ) T, ⨆ (_ : |t - s| ≤ δ), ‖z t - z s‖ₑ

open Classical in
/-- The path `t ↦ z(t)`, `t ∈ [0,T]`, as an element of `C([0,T]; E)` (the zero path if it is not
continuous; statements assert continuity separately). -/
def contPathOf {E : Type*} [NormedAddCommGroup E] (T : ℝ) (z : ℝ → E) : C(Set.Icc (0 : ℝ) T, E) :=
  if h : Continuous fun t : Set.Icc (0 : ℝ) T => z t then ⟨_, h⟩ else 0

/-- Lemma S.A.21 (`S:B:lem:path-tightness-criterion`, TeX S L10697-10704): `Z_N` are `E`-valued
continuous processes (`E` a separable Hilbert space); suppose `{Z_N^t : N ≥ 1}` is tight in `E` for every
`t` in a dense subset `D` of `[0,T]` and, for every `ε > 0`,
`lim_{δ↓0} sup_N P(ω_E(Z_N, δ) > ε) = 0` (`B:eq:path-modulus-criterion`).  Then the laws of `Z_N` are
tight in `C([0,T]; E)`.  The probability spaces may depend on `N`.
Technical hypotheses (so that the pushforward laws are the true laws, not the junk measure `0` of a
non-measurable map, and "continuous process" is read a.s.): each `Z_N^t` is measurable, `Z_N` has
a.s. continuous paths, the path map `ζ ↦ Z_N^·(ζ) ∈ C([0,T];E)` is measurable; `0 < T`. -/
theorem path_tightness_criterion {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [TopologicalSpace.SeparableSpace E] [MeasurableSpace E] [BorelSpace E]
    (T : ℝ) (hT : 0 < T) {Ω : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)] (P : ∀ N, Measure (Ω N))
    [∀ N, IsProbabilityMeasure (P N)] (Z : ∀ N, ℝ → Ω N → E)
    (hZmeas : ∀ N : ℕ, 1 ≤ N → ∀ t, Measurable (Z N t))
    (hcont : ∀ N : ℕ, 1 ≤ N → ∀ᵐ ζ ∂(P N), Continuous fun t : Set.Icc (0 : ℝ) T => Z N t ζ)
    (hpath : ∀ N : ℕ, 1 ≤ N → Measurable fun ζ => contPathOf T (fun t => Z N t ζ))
    (D : Set ℝ) (hDT : D ⊆ Set.Icc (0 : ℝ) T) (hD : Set.Icc (0 : ℝ) T ⊆ closure D)
    (htight : ∀ t ∈ D, IsTightMeasureSet {μ | ∃ N : ℕ, 1 ≤ N ∧ μ = (P N).map (Z N t)})
    (hmod : ∀ ε : ℝ, 0 < ε → Tendsto (fun δ : ℝ =>
      ⨆ N : ℕ, ⨆ (_ : 1 ≤ N), P N {ζ | ENNReal.ofReal ε < omegaE (fun t => Z N t ζ) T δ})
      (𝓝[>] 0) (𝓝 0)) :
    IsTightMeasureSet {μ | ∃ N : ℕ, 1 ≤ N ∧
      μ = (P N).map (fun ζ => contPathOf T (fun t => Z N t ζ))} := by
  sorry


/-! ### `B:lem:uloc-embedding` (S.A.31) -/

/-- Lemma S.A.31(i) (`S:B:lem:uloc-embedding`, TeX S L11001-11007): for an integer `m ≥ 0`, different
generating cutoffs `χ, χ'` in `B:eq:uloc-def`, and the lattice variant `sup_{z ∈ ℤ^d}`, give equivalent
norms (in `ℝ≥0∞`, with a constant `C` depending on `m, d, χ, χ'`; the three inequalities include the
case `χ' = χ`, i.e. real versus lattice supremum). -/
theorem uloc_embedding_cutoffs (m : ℕ) (χ χ' : Euc d → ℝ) (hχ : IsUlocCutoff χ) (hχ' : IsUlocCutoff χ') :
    ∃ C : ℝ, ∀ u : Euc d → ℝ,
      ulocNormE m χ u ≤ ENNReal.ofReal C * ulocNormE m χ' u ∧
      ulNormLat m χ u ≤ ENNReal.ofReal C * ulocNormE m χ' u ∧
      ulocNormE m χ u ≤ ENNReal.ofReal C * ulNormLat m χ' u := by
  sorry

/-- Lemma S.A.31(ii) (TeX S L11005): `‖e_k‖_{H^m_uloc} ≤ C_{m,d}(1+|k|)^m` for the plane waves
`e_k(x) = e^{2πi k·x}`.  AMBIGUITY/representation: `H^m` here is the real Sobolev space of the project, so
the complex-valued `e_k` is represented by its real and imaginary parts `cos(2π k·x)`, `sin(2π k·x)`
(the TeX itself applies the estimate to `Re e_k, Im e_k`, M L1976-1977).  `C` depends on `m, d, χ`. -/
theorem uloc_embedding_modes (m : ℕ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) :
    ∃ C : ℝ, ∀ k : Euc d,
      ulocNormE m χ (fun x => Real.cos (2 * Real.pi * inner ℝ k x)) ≤
        ENNReal.ofReal (C * (1 + ‖k‖) ^ m) ∧
      ulocNormE m χ (fun x => Real.sin (2 * Real.pi * inner ℝ k x)) ≤
        ENNReal.ofReal (C * (1 + ‖k‖) ^ m) := by
  sorry

/-- Lemma S.A.31(iii) (TeX S L11006): if `m > j + d/2` then `H^m_uloc ↪ C_b^j` with
`‖u‖_{C_b^j} ≤ C‖u‖_{H^m_uloc}`: every `u` of finite uniformly local norm has a representative
`v` (`v = u` a.e.) in `C_b^j` with `‖v‖_{C_b^j} ≤ C ‖u‖_{H^m_uloc}` (`C_b^j` norm: the project's sum
convention `HRS.cbNorm`, equivalent to the maximum up to the factor `j+1`). -/
theorem uloc_embedding_cb (m j : ℕ) (hmj : (j : ℝ) + (d : ℝ) / 2 < m) (χ : Euc d → ℝ)
    (hχ : IsUlocCutoff χ) :
    ∃ C : ℝ, ∀ u : Euc d → ℝ, ulocNormE m χ u < ⊤ →
      ∃ v : Euc d → ℝ, v =ᵐ[volume] u ∧ MemCb j v ∧ cbNorm j v ≤ C * (ulocNormE m χ u).toReal := by
  sorry

/-- Lemma S.A.31(iv) (TeX S L11006-11007): `H^m_uloc ⊂ H^m(ϖ)` for any weight `ϖ ≥ 0` with
`∑_{z ∈ ℤ^d} sup_{z+[0,1]^d} ϖ < ∞`, namely `‖u‖_{H^m(ϖ)} ≤ C (∑_z sup ϖ)^{1/2} ‖u‖_{H^m_uloc}`
(the bound the TeX proves), the sum is finite for `ϖ = ⟨x⟩^{-(d+3)}`, and, for this weight, `‖u‖_{H^m(ϖ)} ≤ C‖u‖_{H^m_uloc}` in the junk-free cell form
`varpiNormE` of `HRS.Whole.AppendixA` (no smoothness needed).  `C` depends on `m, d, χ`.
Technical hypothesis: `u ∈ C^m` (so that `∂^α u` are the classical partial derivatives, as in the
TeX's proof; the weighted norm is an integral of `|∂^α u|²`). -/
theorem uloc_embedding_weighted (m : ℕ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) :
    (∃ C : ℝ, ∀ ϖ : Euc d → ℝ, (∀ x, 0 ≤ ϖ x) → ∀ u : Euc d → ℝ, ContDiff ℝ m u →
      weightedHE m ϖ u ≤ ENNReal.ofReal C * (cellSupSum ϖ) ^ (1 / 2 : ℝ) * ulocNormE m χ u) ∧
    cellSupSum (fun x : Euc d => jbracket x ^ (-((d : ℝ) + 3))) < ⊤ ∧
    (∃ C : ℝ, ∀ u : Euc d → ℝ, varpiNormE m χ u ≤ ENNReal.ofReal C * ulocNormE m χ u) := by
  sorry

/-! ### `B:lem:uloc-bilip` (S.A.32) -/

/-- The drift hypotheses `B:eq:drift-bounds-rd` (S L10121-10126) at index `m` for `b ∈
C([0,T]×ℝ^d; ℝ^d)`: `‖∇^{⊗j}b^τ‖_{L^∞} ≤ Λ` for `1 ≤ j ≤ m+1` and `|b^τ(x)| ≤ Λ(1+|x|)`
(`b^τ` is `C^{m+1}` in `x`: technical, the derivative bounds presuppose it). -/
structure IsDriftBounds (T : ℝ) (m : ℕ) (Λ : ℝ) (b : ℝ → Euc d → Euc d) : Prop where
  cont : ContinuousOn (fun p : ℝ × Euc d => b p.1 p.2) (Set.Icc (0 : ℝ) T ×ˢ Set.univ)
  smooth : ∀ τ ∈ Set.Icc (0 : ℝ) T, ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (b τ)
  deriv_bound : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ j : ℕ, 1 ≤ j → j ≤ m + 1 → ∀ x : Euc d,
    ‖iteratedFDeriv ℝ j (b τ) x‖ ≤ Λ
  growth : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ x : Euc d, ‖b τ x‖ ≤ Λ * (1 + ‖x‖)

/-- `Ψ_τ` is the flow of `-b` on `[0,T]`: `∂_τΨ_τ(x) = -b^τ(Ψ_τ(x))`, `Ψ_0 = id`. -/
structure IsNegDriftFlow (T : ℝ) (b : ℝ → Euc d → Euc d) (Ψ : ℝ → Euc d → Euc d) : Prop where
  init : ∀ x, Ψ 0 x = x
  eqn : ∀ x : Euc d, ∀ τ ∈ Set.Icc (0 : ℝ) T,
    HasDerivWithinAt (fun τ' => Ψ τ' x) (-(b τ (Ψ τ x))) (Set.Icc (0 : ℝ) T) τ

/-- The unit cell `z + [0,1]^d`, `z ∈ ℤ^d`. -/
def latticeCell (z : Fin d → ℤ) : Set (Euc d) :=
  {x | ∀ i, latticePt z i ≤ x i ∧ x i ≤ latticePt z i + 1}

/-- Lemma S.A.32 (`S:B:lem:uloc-bilip`, TeX S L11013-11020).  Let `b ∈ C([0,T]×ℝ^d;ℝ^d)` satisfy
`B:eq:drift-bounds-rd` and let `Ψ_τ` be the flow of `-b` (existence and uniqueness: global
solvability by the linear growth, TeX proof L11022; existence is the first conjunct).  Let `χ ∈
C_c^∞(B(0,2);[0,1])`, `χ ≡ 1` on `\overline{B(0,1)}`, `χ̂ ∈ C_c^∞(B(0,8);[0,1])`, `χ̂ ≡ 1` on
`\overline{B(0,6)}`, `χ_z^τ = χ(Ψ_τ^{-1}(·) - z)` (`B:eq:advected-cutoffs`).  Then for `τ ∈ [0,T]`:
(i) `Ψ_τ` is a `C^{m+1}`-diffeomorphism (inverse `Ψ_τ^{-1}`) with `‖∇Ψ_τ^{±1}‖_∞ ≤ e^{Cτ}` and
`‖∇^{⊗j}Ψ_τ^{±1}‖_∞ ≤ C e^{Cmτ}` for `2 ≤ j ≤ m+1`;
(ii) `∂_τχ_z^τ = b·∇χ_z^τ` pointwise (`z ∈ ℝ^d`), and `‖χ_z^τ‖_{C^{m+1}} ≤ C e^{Cmτ}` uniformly in `z`;
(iii) `|x-y| ≥ 4e^{-Cτ}` for `x ∈ supp χ_z^τ`, `y ∈ supp(1-χ̂_z^τ)`;
(iv) the cells `Ψ_τ(z+[0,1]^d)`, `z ∈ ℤ^d`, cover `ℝ^d` with overlap number `≤ Ce^{Cdτ}`; for every
(measurable, `ℝ≥0∞`-valued: more general than "nonnegative locally integrable") `G`,
`∫G ≤ ∑_z ∫_{Ψ_τ(z+[0,1]^d)} G ≤ Ce^{Cdτ}∫G`; and any set of (extended) diameter `≤ ρ` (`Metric.ediam`, so that unbounded sets are not
confused with diameter `0`) meets at most
`C(1+ρ)^d e^{Cdτ}` of the supports `supp χ_z^τ`, `z ∈ ℤ^d`;
(v) `c e^{-C(m+d)τ}‖F‖_{H^m_uloc} ≤ sup_{z ∈ ℝ^d}‖χ_z^τ F‖_{H^m} ≤ C e^{C(m+d)τ}‖F‖_{H^m_uloc}`.
All constants (`C, c > 0` quantified before `b`) depend only on `d, m, T, Λ, χ, χ̂`. (The TeX's
different constants `C_j, C` are merged into one `C`; `x ↦ "number" ≤ N` is `encard ≤ ⌊N⌋`.) -/
theorem uloc_bilip (m : ℕ) (T Λ : ℝ) (hT : 0 < T) (χ χh : Euc d → ℝ) (hχ : IsUlocCutoff χ)
    (hχh : IsCutoffRad 6 8 χh) :
    ∃ C c : ℝ, 0 < c ∧ ∀ b : ℝ → Euc d → Euc d, IsDriftBounds T m Λ b →
      (∃ Ψ, IsNegDriftFlow T b Ψ) ∧
      ∀ Ψ : ℝ → Euc d → Euc d, IsNegDriftFlow T b Ψ →
        ∃ Ψinv : ℝ → Euc d → Euc d, ∀ τ ∈ Set.Icc (0 : ℝ) T,
          -- (i)
          ((∀ x, Ψinv τ (Ψ τ x) = x) ∧ (∀ y, Ψ τ (Ψinv τ y) = y) ∧
            ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (Ψ τ) ∧
            ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (Ψinv τ) ∧
            (∀ x, ‖fderiv ℝ (Ψ τ) x‖ ≤ Real.exp (C * τ)) ∧
            (∀ y, ‖fderiv ℝ (Ψinv τ) y‖ ≤ Real.exp (C * τ)) ∧
            ∀ j : ℕ, 2 ≤ j → j ≤ m + 1 → ∀ x : Euc d,
              ‖iteratedFDeriv ℝ j (Ψ τ) x‖ ≤ C * Real.exp (C * m * τ) ∧
              ‖iteratedFDeriv ℝ j (Ψinv τ) x‖ ≤ C * Real.exp (C * m * τ)) ∧
          -- (ii)
          (∀ z : Euc d, (∀ x, HasDerivWithinAt (fun τ' => χ (Ψinv τ' x - z))
              (inner ℝ (b τ x) (gradient (fun y => χ (Ψinv τ y - z)) x)) (Set.Icc (0 : ℝ) T) τ) ∧
            MemCb (m + 1) (fun x => χ (Ψinv τ x - z)) ∧
            cbNorm (m + 1) (fun x => χ (Ψinv τ x - z)) ≤ C * Real.exp (C * m * τ)) ∧
          -- (iii)
          (∀ z : Euc d, ∀ x y : Euc d, x ∈ tsupport (fun x => χ (Ψinv τ x - z)) →
            y ∈ tsupport (fun y => 1 - χh (Ψinv τ y - z)) →
            4 * Real.exp (-(C * τ)) ≤ ‖x - y‖) ∧
          -- (iv)
          ((⋃ z : Fin d → ℤ, Ψ τ '' latticeCell z) = Set.univ ∧
            (∀ y : Euc d, {z : Fin d → ℤ | y ∈ Ψ τ '' latticeCell z}.encard ≤
              ((⌊C * Real.exp (C * d * τ)⌋₊ : ℕ) : ℕ∞)) ∧
            (∀ G : Euc d → ℝ≥0∞, Measurable G →
              ∫⁻ x, G x ≤ ∑' z : Fin d → ℤ, ∫⁻ x in Ψ τ '' latticeCell z, G x ∧
              (∑' z : Fin d → ℤ, ∫⁻ x in Ψ τ '' latticeCell z, G x) ≤
                ENNReal.ofReal (C * Real.exp (C * d * τ)) * ∫⁻ x, G x) ∧
            ∀ (A : Set (Euc d)) (ρ : ℝ), 0 ≤ ρ → Metric.ediam A ≤ ENNReal.ofReal ρ →
              {z : Fin d → ℤ | (A ∩ tsupport (fun x => χ (Ψinv τ x - latticePt z))).Nonempty}.encard ≤
                ((⌊C * (1 + ρ) ^ d * Real.exp (C * d * τ)⌋₊ : ℕ) : ℕ∞)) ∧
          -- (v)
          (∀ F : Euc d → ℝ,
            ENNReal.ofReal (c * Real.exp (-(C * (m + d) * τ))) * ulocNormE m χ F ≤
              ⨆ z : Euc d, sobolevNormE (m : ℝ) (fun x => χ (Ψinv τ x - z) * F x) ∧
            (⨆ z : Euc d, sobolevNormE (m : ℝ) (fun x => χ (Ψinv τ x - z) * F x)) ≤
              ENNReal.ofReal (C * Real.exp (C * (m + d) * τ)) * ulocNormE m χ F) := by
  sorry


/-! ### `B:lem:uloc-uniqueness` (S.A.33) -/

/-- `(g * ∂_iψ)(y) = ∫ g(y-x) ∂_iψ(x) dx`, which equals `(∂_i g * ψ)(y)` for `ψ ∈ C_c^∞` and is
absolutely convergent for every `0 ≤ s < d` (it replaces the distributional convolution `∂_ig * ·`
against a test function). -/
def kernelConvDeriv (d : ℕ) (s : ℝ) (i : Fin d) (ψ : Euc d → ℝ) (y : Euc d) : ℝ :=
  ∫ x, rieszKernel d s (y - x) * fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ))

/-- The pairing `⟨𝓛^σ z, ψ⟩` of the forward operator of `B:eq:adjoint-forward` on `ℝ^d`,
`∂_τF = νΔF + b^τ·∇F - 𝒢^τ[F]`, `b^τ = M∇g*μ^{t-τ} - ∇V`, `𝒢^τ[F] = ∑_{ij} M^*_{ij} ∂_ig*(μ^{t-τ}∂_jF)`,
with a test function `ψ ∈ C_c^∞` and all derivatives moved to `ψ`: with `μ = μ^{t-σ}`,
`⟨𝓛z,ψ⟩ = ν∫zΔψ - ∫ z div(bψ) - ∑_{ij} M_{ji} ∫ z ∂_j(μ · (g*∂_iψ))`
(since `∫(∂_ig*h)ψ = -∫h (g*∂_iψ)`, `∂_ig` odd). -/
def forwardPairing (D : WholeDyn d) (ρ : ℝ → Euc d → ℝ) (t σ : ℝ) (z ψ : Euc d → ℝ) : ℝ :=
  D.invβ * (∫ x, z x * Laplacian.laplacian ψ x) -
    (∫ x, z x * ∑ i : Fin d, fderiv ℝ (fun y => meanFieldDriftW D (ρ (t - σ)) y i * ψ y) x
        (EuclideanSpace.single i (1 : ℝ))) -
    ∑ i : Fin d, ∑ j : Fin d, D.M j i *
      ∫ x, z x * fderiv ℝ (fun y => ρ (t - σ) y * kernelConvDeriv d D.s i ψ y) x
        (EuclideanSpace.single j (1 : ℝ))

/-- `z : [0,t] → L^∞_loc` solves the adjoint forward equation `B:eq:adjoint-forward` (terminal time `t`,
coefficients `(D, ρ)`) in the distributional sense with `z(0) = 0`: in integrated form tested against
every `ψ ∈ C_c^∞(ℝ^d)`, `⟨z(τ),ψ⟩ = ⟨z(0),ψ⟩ + ∫_0^τ ⟨𝓛^σ z(σ),ψ⟩ dσ` for `τ ∈ [0,t]` with an integrable
integrand, and `z(0) = 0` a.e.  (As in the torus file `HRS.PDE.ForwardEq`, where the equation is tested
coefficientwise.)  Membership in `L^∞([0,t];H^1_uloc)` is `IsUlBounded` below. -/
structure IsForwardDistSolutionW (D : WholeDyn d) (ρ : ℝ → Euc d → ℝ) (t : ℝ)
    (z : ℝ → Euc d → ℝ) : Prop where
  init : z 0 =ᵐ[volume] 0
  integrable : ∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
    IntegrableOn (fun σ => forwardPairing D ρ t σ (z σ) ψ) (Set.Icc 0 t)
  eq : ∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → ∀ τ ∈ Set.Icc (0 : ℝ) t,
    ∫ x, z τ x * ψ x = (∫ x, z 0 x * ψ x) +
      ∫ σ in Set.Icc (0 : ℝ) τ, forwardPairing D ρ t σ (z σ) ψ

/-- `z ∈ L^∞([0,t]; H^1_uloc)`: `sup_{τ ∈ [0,t]} ‖z(τ)‖_{H^1_uloc} < ∞`. -/
def IsUlBounded (χ : Euc d → ℝ) (m : ℕ) (t : ℝ) (z : ℝ → Euc d → ℝ) : Prop :=
  ∃ B : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) t, ulocNormE m χ (z τ) ≤ ENNReal.ofReal B

/-- Lemma S.A.33 (`S:B:lem:uloc-uniqueness`, TeX S L11026-11028).  Under `B:eq:coeff-hypothesis-rd`
(`CoeffHypRd`: `μ` is `(m+3,Λ)`-regular on `[0,T]` with the decay of `S:eq:mf-regularity-whole`; and `V`
satisfies `B:eq:V-assumption` with `m_V = m+3`, `VHypRd`; `ν = β⁻¹ ∈ [0, ν̄]`) and one of the
regimes R1, R2a, R2c, R3 (`RdRegimeHolds`, `R2b` excluded), every `z ∈ L^∞([0,t]; H^1_uloc(ℝ^d))` solving
`B:eq:adjoint-forward` distributionally (`IsForwardDistSolutionW`) with `z(0) = 0` vanishes
identically: `z(τ) = 0` a.e. for every `τ ∈ [0,t]`.
Technical hypotheses: `1 ≤ m`, `0 ≤ s < d`, `1 ≤ d`; `t ∈ [0,T]`.  `m_V = m+3 ≥ 2` makes `V ∈ C^∞` with
bounded Hessian. -/
theorem uloc_uniqueness (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m)
    (Rg : PDE.Regime) (T Λ ΛV G₀ MB νbar ν₀ : ℝ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ)
    (M : Matrix (Fin d) (Fin d) ℝ) (V : Euc d → ℝ) (invβ : ℝ) (ρ : ℝ → Euc d → ℝ)
    (hM : PDE.MatBound MB M) (hV : VHypRd (m + 3) ΛV G₀ V) (hν : 0 ≤ invβ ∧ invβ ≤ νbar)
    (hρ : CoeffHypRd s m Λ T ρ)
    (hRg : RdRegimeHolds Rg d s M invβ ν₀) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T)
    (z : ℝ → Euc d → ℝ) (hzb : IsUlBounded χ 1 t z)
    (hz : IsForwardDistSolutionW (⟨s, M, V, invβ⟩ : WholeDyn d) ρ t z) :
    ∀ τ ∈ Set.Icc (0 : ℝ) t, z τ =ᵐ[volume] 0 := by
  sorry


/-! ### `B:lem:expanding-tori` (S.A.34) -/

/-- The fundamental box `[0,L)^d` of `𝕋_L^d = ℝ^d/Lℤ^d`. -/
def periodBox (d : ℕ) (L : ℝ) : Set (Euc d) := {x | ∀ i, 0 ≤ x i ∧ x i < L}

/-- `γ` (a function on `ℝ^d`) is the mean-zero kernel on `𝕋_L^d` with Fourier coefficients
`c_{d,s}(2π|k|)^{s-d}`, `k ∈ L^{-1}ℤ^d ∖ {0}`, for the unnormalized Fourier transform
`f̂(k) = ∫_{𝕋_L^d} f(x) e^{-2πik·x} dx` (`B:lem:expanding-tori`, S L11058): `γ` is `Lℤ^d`-periodic,
locally integrable, smooth off the lattice `Lℤ^d` (so that the pointwise derivative bounds of the lemma
make sense), `∫_{[0,L)^d} γ = 0`, and `∫_{[0,L)^d} γ(x) e^{-2πi(k/L)·x}dx = c_{d,s}(2π|k|/L)^{s-d}` for
`k ∈ ℤ^d ∖ {0}`.  Such a `γ` is unique a.e. (Fourier coefficients), hence everywhere by continuity off
the lattice. -/
structure IsPeriodicRieszKernel (d : ℕ) (s L : ℝ) (γ : Euc d → ℝ) : Prop where
  periodic : ∀ (x : Euc d) (z : Fin d → ℤ), γ (x + L • latticePt z) = γ x
  smooth : ContDiffOn ℝ ∞ γ {x : Euc d | ∀ z : Fin d → ℤ, x ≠ L • latticePt z}
  locInt : LocallyIntegrable γ volume
  meanZero : ∫ x in periodBox d L, γ x = 0
  coeff : ∀ k : Fin d → ℤ, k ≠ 0 →
    ∫ x in periodBox d L, (γ x : ℂ) *
        Complex.exp (-(2 * Real.pi * Complex.I * ((∑ i, ((k i : ℝ) / L) * x i : ℝ) : ℂ))) =
      ((rieszConst d s * (2 * Real.pi * (‖(WithLp.toLp 2 fun i => (k i : ℝ) : Euc d)‖ / L)) ^
        (s - d) : ℝ) : ℂ)

/-- Lemma S.A.34, kernel part (`S:B:lem:expanding-tori`, TeX S L11058-11059): for `L ≥ 1` let `γ_L` be
the mean-zero kernel on `𝕋_L^d` with Fourier coefficients `c_{d,s}(2π|k|)^{s-d}`
(`IsPeriodicRieszKernel`; it exists for every `L`: first conjunct).  Then, with `C` independent of `L`:
(a) for `|x| ≤ L/2` (`x ≠ 0`), `0 ≤ n ≤ m+2`, `n + s > 0`:
`|∇^{⊗n}γ_L(x)| ≤ C(|x|^{-s-n} + L^{-s-n}1_{s>0} + L^{-n}1_{s=0})`;
(b) if `s = 0`: `|γ_L(x) - log L| ≤ C(1 + |log|x||)` for `0 < |x| ≤ L/2` (the case `s = n = 0`);
(c) for every compact `K ⊆ ℝ^d ∖ {0}` and `0 ≤ n ≤ m+2`, `∇^{⊗n}γ_L → ∇^{⊗n}γ_E` uniformly on `K`
as `L → ∞`, `γ_E = HRS.rieszKernel d s` the Euclidean kernel, up to an additive constant `c_L` when
`n = 0`, `s = 0` (`n + s > 0` otherwise).  `∇^{⊗n}` is `iteratedFDeriv` (operator norm). -/
theorem expanding_tori_kernel (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) :
    (∀ L : ℝ, 1 ≤ L → ∃ γ : Euc d → ℝ, IsPeriodicRieszKernel d s L γ) ∧
    (∃ C : ℝ, ∀ L : ℝ, 1 ≤ L → ∀ γ : Euc d → ℝ, IsPeriodicRieszKernel d s L γ →
      (∀ n : ℕ, n ≤ m + 2 → 0 < (n : ℝ) + s → ∀ x : Euc d, x ≠ 0 → ‖x‖ ≤ L / 2 →
        ‖iteratedFDeriv ℝ n γ x‖ ≤ C * (‖x‖ ^ (-s - n) + (if 0 < s then L ^ (-s - n) else 0) +
          (if s = 0 then L ^ (-(n : ℝ)) else 0))) ∧
      (s = 0 → ∀ x : Euc d, x ≠ 0 → ‖x‖ ≤ L / 2 →
        |γ x - Real.log L| ≤ C * (1 + |Real.log ‖x‖|))) ∧
    ∀ K : Set (Euc d), IsCompact K → (∀ x ∈ K, x ≠ 0) → ∀ n : ℕ, n ≤ m + 2 → ∀ ε : ℝ, 0 < ε →
      ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → ∀ γ : Euc d → ℝ, IsPeriodicRieszKernel d s L γ →
        ((0 < (n : ℝ) + s → ∀ x ∈ K,
            ‖iteratedFDeriv ℝ n γ x - iteratedFDeriv ℝ n (rieszKernel d s) x‖ ≤ ε) ∧
          (n = 0 → s = 0 → ∃ c : ℝ, ∀ x ∈ K, |γ x - rieszKernel d s x - c| ≤ ε)) := by
  sorry

/-- The periodization on `𝕋_L^d` of a function on `ℝ^d`: `(perL L f)(x) = ∑_{z ∈ ℤ^d} f(x - Lz)`. -/
def perL (L : ℝ) (f : Euc d → ℝ) (x : Euc d) : ℝ :=
  ∑' z : Fin d → ℤ, f (x - L • latticePt z)

/-- The convolution `G * ρ` on `𝕋_L^d` by the cancellation convention `B:eq:nabla-g-convolution`, for
`L`-periodic `G, ρ`, computed on the period cell centred at `x` (on which the torus distance is
`|x-y|`): `∫_{y-x ∈ [-L/2,L/2)^d} (ρ(y) - ρ(x)) G(x-y) 1_{|x-y| ≤ 1/4} + ρ(y) G(x-y) 1_{|x-y|>1/4} dy`. -/
def convGradConvL (L : ℝ) (G : Euc d → Euc d) (ρ : Euc d → ℝ) (x : Euc d) : Euc d :=
  ∫ y in {y : Euc d | ∀ i, -(L / 2) ≤ (x - y) i ∧ (x - y) i < L / 2},
    (if ‖x - y‖ ≤ 1 / 4 then (ρ y - ρ x) • G (x - y) else ρ y • G (x - y))

/-- The drift `b_L = M ∇γ_L * μ_L - ∇V_L` on `𝕋_L^d`, for the coefficients `μ_L, V_L` (`L`-periodic). -/
def torusDriftL (M : Matrix (Fin d) (Fin d) ℝ) (L : ℝ) (γ : Euc d → ℝ) (μL VL : Euc d → ℝ)
    (x : Euc d) : Euc d :=
  Torus.matVec M (convGradConvL L (gradient γ) μL x) - gradient VL x

/-- Lemma S.A.34, coefficient part (`S:B:lem:expanding-tori`, TeX S L11059-11060, with the cutoff
periodization of Step 3 of `B:sec:adjoint-rd-proof`, S L10436-10441: `ζ ∈ C_c^∞(B(0,1/3))`, `ζ ≡ 1` on
`B(0,1/4)`, `ζ_L = ζ(·/L)`, `μ_L = Z_L^{-1} ζ_L μ`, `V_L = ζ_L V`, `Z_L = ∫ ζ_L μ`, periodized).  Let
`μ` be `(m+3,Λ)`-regular on `[0,T]` (`CoeffHypRd`, the decay of `S:eq:mf-regularity-whole` built
in) and `V` satisfy `B:eq:V-assumption` with `m_V = m+3`; let `γ_L` be the kernels of
`expanding_tori_kernel`.  Then there are `Λ', C` independent of `L ≥ 1` and `t ∈ [0,T]` such that
(`B:eq:coeff-hypothesis-rd`, `B:eq:drift-bounds-rd` uniformly in `L`):
* `μ_L^t ∈ C^{m+3}` with `‖μ_L^t‖_{C^{m+3}} ≤ Λ'` and the decay `⟨x⟩^{d+3}|∇^jμ_L^t(x)| ≤ Λ'` on the
  central cube `|x| ≤ L/2`, `j ≤ m+3`; and `‖∇^{⊗j}V_L‖_∞ ≤ Λ'` for `2 ≤ j ≤ m+3`;
* `‖∇^{⊗j}b_L^t‖_∞ ≤ C` for `1 ≤ j ≤ m+1` and `|b_L^t(x)| ≤ C(1+|x|)` for `|x| ≤ L/2`;
and `b_L^t → b^t = M∇g*μ^t - ∇V` (`HRS.Whole.meanFieldDriftW`) locally uniformly with all derivatives up to
order `m+1`, for each `t ∈ [0,T]`.  (`Λ'` depends on `d, s, m, Λ, Λ_V, |V(0)| ≤ V₀, ζ`; `C` also on `|M|`, `|∇V(0)| ≤ G₀`: the derivatives of
`V_L = ζ_LV` involve `V` itself on the annulus `|x| ≍ L`, where `|V(x)| ≤ |V(0)| + C⟨x⟩²`, so `|V(0)|` enters the
constants and is bounded by `V₀` before they are chosen.)  Technical hypotheses: `0 ≤ s < d`, `1 ≤ d`;
`Z_L > 0` is part of the facts (`Z_L = 1 + O(L^{-2})`, so for
`L` large; stated for `L ≥ L₀`). -/
theorem expanding_tori_coefficients (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ)
    (T Λ ΛV MB G₀ V₀ : ℝ) (ζ : Euc d → ℝ) (hζ : IsCutoffRad (1 / 4) (1 / 3) ζ) :
    ∃ Λ' C L₀ : ℝ, ∀ (M : Matrix (Fin d) (Fin d) ℝ) (V : Euc d → ℝ) (ρ : ℝ → Euc d → ℝ),
      PDE.MatBound MB M → VHypRd (m + 3) ΛV G₀ V → |V 0| ≤ V₀ → CoeffHypRd s m Λ T ρ →
      ∀ γ : ℝ → Euc d → ℝ, (∀ L : ℝ, 1 ≤ L → IsPeriodicRieszKernel d s L (γ L)) →
      let μL : ℝ → ℝ → Euc d → ℝ := fun L t =>
        perL L fun x => (∫ y, ζ (L⁻¹ • y) * ρ t y)⁻¹ * (ζ (L⁻¹ • x) * ρ t x)
      let VL : ℝ → Euc d → ℝ := fun L => perL L fun x => ζ (L⁻¹ • x) * V x
      ∀ L : ℝ, max 1 L₀ ≤ L → ∀ t ∈ Set.Icc (0 : ℝ) T,
        (0 < ∫ y, ζ (L⁻¹ • y) * ρ t y) ∧
        (ContDiff ℝ ((m + 3 : ℕ) : WithTop ℕ∞) (μL L t) ∧ MemCb (m + 3) (μL L t) ∧
          cbNorm (m + 3) (μL L t) ≤ Λ' ∧
          ∀ j ≤ m + 3, ∀ x : Euc d, ‖x‖ ≤ L / 2 →
            jbracket x ^ ((d : ℝ) + 3) * ‖iteratedFDeriv ℝ j (μL L t) x‖ ≤ Λ') ∧
        (ContDiff ℝ ∞ (VL L) ∧
          ∀ j : ℕ, 2 ≤ j → j ≤ m + 3 → ∀ x : Euc d, ‖iteratedFDeriv ℝ j (VL L) x‖ ≤ Λ') ∧
        ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (torusDriftL M L (γ L) (μL L t) (VL L)) ∧
        (∀ j : ℕ, 1 ≤ j → j ≤ m + 1 → ∀ x : Euc d,
          ‖iteratedFDeriv ℝ j (torusDriftL M L (γ L) (μL L t) (VL L)) x‖ ≤ C) ∧
        (∀ x : Euc d, ‖x‖ ≤ L / 2 →
          ‖torusDriftL M L (γ L) (μL L t) (VL L) x‖ ≤ C * (1 + ‖x‖)) := by
  sorry

/-- Lemma S.A.34, convergence of the drifts (`S:B:lem:expanding-tori`, TeX S L11060): under the
hypotheses of `expanding_tori_coefficients`, `b_L^t → b^t` locally uniformly with all derivatives up to
order `m+1`, for every `t ∈ [0,T]`: for every compact `K`, `j ≤ m+1`, `ε > 0` there is `L₀` with
`‖∇^{⊗j}(b_L^t - b^t)(x)‖ ≤ ε` for all `L ≥ L₀`, `x ∈ K`. -/
theorem expanding_tori_drift_convergence (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ)
    (T Λ ΛV MB G₀ : ℝ) (ζ : Euc d → ℝ) (hζ : IsCutoffRad (1 / 4) (1 / 3) ζ)
    (M : Matrix (Fin d) (Fin d) ℝ) (V : Euc d → ℝ) (ρ : ℝ → Euc d → ℝ)
    (hM : PDE.MatBound MB M) (hV : VHypRd (m + 3) ΛV G₀ V)
    (hρ : CoeffHypRd s m Λ T ρ)
    (γ : ℝ → Euc d → ℝ) (hγ : ∀ L : ℝ, 1 ≤ L → IsPeriodicRieszKernel d s L (γ L))
    (invβ : ℝ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) (K : Set (Euc d)) (hK : IsCompact K)
    (j : ℕ) (hj : j ≤ m + 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ L₀ : ℝ, ∀ L : ℝ, max 1 L₀ ≤ L → ∀ x ∈ K,
      ‖iteratedFDeriv ℝ j (torusDriftL M L (γ L)
          (perL L fun x => (∫ y, ζ (L⁻¹ • y) * ρ t y)⁻¹ * (ζ (L⁻¹ • x) * ρ t x))
          (perL L fun x => ζ (L⁻¹ • x) * V x)) x -
        iteratedFDeriv ℝ j (meanFieldDriftW (⟨s, M, V, invβ⟩ : WholeDyn d) (ρ t)) x‖ ≤ ε := by
  sorry

end HRS.Whole.AppendixALemmas
