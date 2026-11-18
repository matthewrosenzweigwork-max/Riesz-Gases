import HRS.Whole.AppendixBField
import HRS.Whole.Orbits
import HRS.Whole.MovingDyn
import HRS.Whole.RegMF
import HRS.Main.TorusTheorems
import HRS.Energy.Coercivity
import HRS.Kernel.Riesz

/-!
# Appendix S.A of the whole-space supplement: the main `ℝ^d` theorems (SPEC-WA, part 1)

Specification file (statements with `sorry` proofs).  Sources (`HRS_whole_space_supplement_20261008T010000Z.tex`, "S";
the standing assumptions `B:ass:*` are those of the main manuscript Appendix A, `HRS_periodic_main_...`, "M",
read on `𝔻 = ℝ^d` with the whole-space modifications of S L9617-9700):

* S.A.2 `B:thm:main-rd-stat` (S L9864-9879): `main_rd_stat`;
* S.A.3 `B:cor:fourier-statistics` (S L9881-9891): `fourier_statistics_rd`;
* S.A.4 `B:thm:main-rd-dec-stat` (S L9893-9905): `main_rd_dec_stat`;
* S.A.5 `B:rem:density-tradeoff` (S L9907-9913): `sqrtN_errorRate_tendsto_iff` (the only checkable claim);
* S.A.6 `B:thm:main-rd-field` (S L9915-9949): `main_rd_field`;
* S.A.7 `B:cor:rd-field-wasserstein` (S L9951-9981): `rd_field_wasserstein_one`, `rd_field_wasserstein_two`;
* S.A.8 `B:ass:rd-path-weighted` (S L9987-10002): `WeightedPathInput`;
* S.A.9 `B:thm:main-rd-path` (S L10004-10022): `main_rd_path`;
* S.A.10 `B:cor:iid-path-rd` (S L10024-10026): `iid_path_rd`;
* S.A.11 `B:cor:zero-temp-decaying-field` (S L10028-10046): `zero_temp_decaying_field`.
(S.A.12-S.A.17, the adjoint theory, are in `HRS/Whole/AppendixAAdjoint.lean`.)

## Shape of the statements (mirrors `HRS/Main/{Assumptions,Linearization,TorusTheorems}.lean`)

* **Data.**  `WholeMainData d` (deterministic data), `RealizationRd d N` (random data at particle number `N`),
  a sequence of realizations is `R : ∀ N, RealizationRd d N`; per-`N` assumptions are imposed for `1 ≤ N`.
  `β_N = ∞` is `invβ N = 0`.  Expectations of possibly non-integrable quantities are `lintegral`s of `ofReal`.
* **Constants.**  "There are `C, Λ_T` depending only on ..." is `∃ C ΛT, 0 < C ∧ 0 < ΛT ∧ ∀ data ...`, placed after
  the bounds `(d, s, regime, ν₀, |M|, Λ, Λ_V, |∇V(0)|, ν̄, T, C_in, C₀)` and the cutoff `χ` of the uniformly local
  norm, and before the data (so they cannot depend on `M, V, κ_N, β_N, ρ_N`, the sequences `ε_N, 𝔈_N`, the
  realization, nor on the propagated second-moment number `𝔪₂` (`m₂`); they may depend on the bound `m20` of the initial
  second moment `𝔪₂⁰` (a standing assumption), which is therefore quantified before them).
* **`𝔪₂` and `𝔴_N`** (`B:eq:wN-def`): `𝔪₂` is the propagated bound of `B:lem:moments` (S.A.18, drafted elsewhere).  It
  enters the rate only through the explicit function `wN`; the statements take a real number `m₂ ≥ 0` with
  `PropagatedSecondMoment` (`sup_N sup_{t ≤ T} E⟨|x|², μ_N^t + μ_{β_N}^t⟩ ≤ m₂`).  `𝔴_N` is monotone in `m₂`, so the
  statement for the exact supremum (finite by S.A.18) is the instance `m₂ = 𝔪₂`.
* **Uniformly local norms** are `ulocNormE` (`B:eq:uloc-def`, S L9617-9622: `sup_{z ∈ ℝ^d} ‖χ(·-z)u‖_{H^m}`), valued in
  `ℝ≥0∞` (`⊤` if the norm is infinite).  `H^m(ϖ)`, `ϖ = ⟨x⟩^{-(d+3)}` is `varpiNormE` (cell form with `2P = d+3`).
* **Fields** live in `H^{-Γ}(ℝ^d) = HNeg d Γ` (`HRS/Whole/SobolevDual.lean`); a random element representing the
  particle field `σ_NΞ_N^t` is any measurable `Ξ` with `⟨φ,Ξ⟩ = σ_N(μ_N^t(φ) - μ_{β_N}^t(φ))` a.s. for every smooth
  `φ ∈ H^Γ` (`IsFluctFieldRepr`); its existence is part of the conclusions (it holds since `Γ > d/2`).  The same
  representation is used for the transported initial fields of `B:eq:transported-initial-rd` (`TransportedInitialFieldRd`).
* The laws of the linear approximation are the explicit convolutions of `HRS/Main/Linearization.lean`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff MeasureTheory

namespace HRS.Whole.AppendixA

variable {d : ℕ}

/-! ### Global notation of Appendix S.A -/

/-- `m_nd = m_* + ⌊d/2⌋ + 1` (`B:eq:nd-field-index`, S L9847-9849), `m_* = ⌊d/2⌋ + 3` (`HRS.Whole.mStar`). -/
def mNd (d : ℕ) : ℕ := mStar d + d / 2 + 1

/-- `Γ_nd = m_nd + 2` (`B:eq:nd-field-index`, S L9847-9849). -/
def gammaNd (d : ℕ) : ℕ := mNd d + 2

/-- The cutoff of `B:eq:uloc-def` (S L9617-9619): `χ ∈ C_c^∞(B(0,2); [0,1])`, `χ ≡ 1` on `closedBall 0 1`. -/
def IsUlocCutoff (χ : Euc d → ℝ) : Prop :=
  ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ Metric.ball (0 : Euc d) 2 ∧
    (∀ x, χ x ∈ Set.Icc (0 : ℝ) 1) ∧ ∀ x ∈ Metric.closedBall (0 : Euc d) 1, χ x = 1

/-- `‖u‖_{H^m_uloc(ℝ^d)} = sup_{z ∈ ℝ^d} ‖χ(·-z) u‖_{H^m(ℝ^d)}` (`B:eq:uloc-def`, S L9620-9622), `m ∈ ℕ`, valued in
`ℝ≥0∞` (`⊤` if `χ(·-z)u ∉ H^m` for some `z`, or the supremum is infinite).  The Sobolev norm is
`HRS.Whole.sobolevNormE`. -/
def ulocNormE (m : ℕ) (χ : Euc d → ℝ) (u : Euc d → ℝ) : ℝ≥0∞ :=
  ⨆ z : Euc d, sobolevNormE (m : ℝ) fun x => χ (x - z) * u x

/-- `‖u‖_{H^m(ϖ)}`, `ϖ(x) = ⟨x⟩^{-(d+3)}` (S L9683, L10104-10106), in the equivalent, junk-free (Sobolev-based) form
`(∑_{z ∈ ℤ^d} ⟨z⟩^{-(d+3)}‖χ(·-z)u‖²_{H^m})^{1/2}` (the cell decomposition of S L10456-10458,
`B:eq:weighted-cell-equivalence`: `∑_{|α|≤m}∫ϖ|∂^αu|² ≍ ∑_z ω_z‖χ_zu‖²_{H^m}`, `ω_z = ⟨z⟩^{-(d+3)}`), with the uloc cutoff
`χ`; valued in `ℝ≥0∞` (`⊤` if some `χ(·-z)u ∉ H^m` or the sum diverges); defined for every function (no classical
derivatives are used).

Statement repair MH-REPAIRS-1 (docs/ISSUES.md, 2026-10-19): the centres are `cellPt d z = ⌈√d⌉⁻¹ • z` instead of `z`, so that
the supports of the cutoffs cover `ℝ^d` for every `d` (the unit lattice covers only for `d ≤ 4`); the weights are
`⟨cellPt d z⟩^{-(d+3)}`. -/
def varpiNormE (m : ℕ) (χ : Euc d → ℝ) (u : Euc d → ℝ) : ℝ≥0∞ :=
  (∑' z : Fin d → ℤ, ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3))) *
    sobolevNormE (m : ℝ) (fun x => χ (x - cellPt d z) * u x) ^ 2) ^ (1 / 2 : ℝ)

/-- `u` is bounded and Lipschitz (`u ∈ C_b^{0,1}`). -/
def IsBddLip (u : Euc d → ℝ) : Prop :=
  (∃ B : ℝ, ∀ x, |u x| ≤ B) ∧ ∃ L : ℝ, HRS.PDE.ToolboxRd.IsLipschitz L u

/-- The test class `Y_0 = H^{m_0}_uloc(ℝ^d) ∩ C_b^{0,1}(ℝ^d)` (`S:eq:initial-statistics-space`, S L9680-9683). -/
def Y0Class (m₀ : ℕ) (χ : Euc d → ℝ) (u : Euc d → ℝ) : Prop :=
  ulocNormE m₀ χ u < ⊤ ∧ IsBddLip u

/-- `‖ψ‖_{Y_0} = ‖ψ‖_{H^{m_0}(ϖ)} + ‖ψ‖_{C_b^{0,1}}` (S L9682); `C_b^{0,1}` norm `‖ψ‖_∞ + [ψ]_{Lip}`
(`HRS.PDE.ToolboxRd.c01Norm`).  Used for `ψ ∈ Y0Class` only (then both terms are finite). -/
def y0Norm (m₀ : ℕ) (χ : Euc d → ℝ) (ψ : Euc d → ℝ) : ℝ :=
  (varpiNormE m₀ χ ψ).toReal + HRS.PDE.ToolboxRd.c01Norm ψ

/-- The assumption `B:eq:V-assumption` on `𝔻 = ℝ^d` (S L9647-9655): `V ∈ C^∞(ℝ^d)` with
`‖∇^{⊗j}V‖_{L^∞} ≤ Λ_V` for `2 ≤ j ≤ m_V`, together with the bound `|∇V(0)| ≤ G₀` on which the constants of
`B:sec:adjoint-rd` depend (S L10084: "constants depend on `(d,s,m,|M|,Λ,Λ_V,|∇V(0)|,ν̄,T)`"). -/
def VHypRd (mV : ℕ) (ΛV G₀ : ℝ) (V : Euc d → ℝ) : Prop :=
  ContDiff ℝ ∞ V ∧ (∀ j : ℕ, 2 ≤ j → j ≤ mV → ∀ x, ‖iteratedFDeriv ℝ j V x‖ ≤ ΛV) ∧
    ‖gradient V 0‖ ≤ G₀

/-- The coefficient hypothesis `B:eq:coeff-hypothesis-rd` for the density path (S L10077-10083): `μ^r` probability
densities, `μ` is `(m+3, Λ)`-regular on `[0,T]` (with the decay of `S:eq:mf-regularity-whole`), and
`r ↦ μ^r` is weakly continuous into `𝒫(ℝ^d)` (against bounded continuous tests).  The hypothesis on `V`
(`m_V = m + 3`) is `VHypRd`. -/
structure CoeffHypRd (s : ℝ) (m : ℕ) (Λ T : ℝ) (μ : ℝ → Euc d → ℝ) : Prop where
  prob : ∀ r ∈ Set.Icc (0 : ℝ) T, IsProbDensity (μ r)
  regular : IsRegularMFRd s (m + 3) Λ T μ
  cont : ∀ ψ : Euc d → ℝ, Continuous ψ → (∃ B, ∀ x, |ψ x| ≤ B) →
    ContinuousOn (fun r => ∫ x, ψ x * μ r x) (Set.Icc (0 : ℝ) T)

/-! ### The deterministic data and the realizations -/

/-- The deterministic data of Appendix A on `𝔻 = ℝ^d` (M L10156, S L9617-9700): `d ≥ 1`, `0 ≤ s < d`, the
matrix `M`, the potential `V : ℝ^d → ℝ` (possibly of linear-gradient growth), the horizon `T > 0`, the datum `μ°`
(a probability measure), `β_N⁻¹ ∈ [0,∞)` with the standing bound `sup_N β_N⁻¹ < ∞` (`invβ_bdd`), `κ_N > 0`,
and the mean-field densities `μ_{β_N}^t = ρ N t dx`.  (Whole-space analogue of `HRS.Main.MainData`.) -/
structure WholeMainData (d : ℕ) where
  s : ℝ
  hs0 : 0 ≤ s
  hsd : s < d
  hd : 1 ≤ d
  M : Matrix (Fin d) (Fin d) ℝ
  V : Euc d → ℝ
  T : ℝ
  hT : 0 < T
  μ0 : Measure (Euc d)
  hμ0 : IsProbabilityMeasure μ0
  invβ : ℕ → ℝ
  hinvβ : ∀ N, 0 ≤ invβ N
  /-- the standing bound `sup_N β_N⁻¹ < ∞` (`ν̄ = 1/inf_N β_N`, S L10084) -/
  invβ_bdd : ∃ B : ℝ, ∀ N, invβ N ≤ B
  κ : ℕ → ℝ
  hκ : ∀ N, 0 < κ N
  ρ : ℕ → ℝ → Euc d → ℝ

namespace WholeMainData

variable (S : WholeMainData d)

/-- The dynamics data at particle number `N`. -/
def dyn (N : ℕ) : WholeDyn d := ⟨S.s, S.M, S.V, S.invβ N⟩

/-- The coefficients of the linear (backward) generator at particle number `N`
(`b = M∇g*μ_{β_N} - ∇V`, density `μ_{β_N}`). -/
def coeff (N : ℕ) : WholeCoeff d := (S.dyn N).coeff (S.ρ N)

/-- `σ_N = min{κ_N, √(Nβ_N)}` (`H:eq:intro-scales`). -/
def sigma (N : ℕ) : ℝ := sigmaScale N (S.κ N) (S.invβ N)

/-- `A_N = σ_N / κ_N`. -/
def AN (N : ℕ) : ℝ := Ascale N (S.κ N) (S.invβ N)

/-- `q_N = σ_N² / (N β_N)`. -/
def qN (N : ℕ) : ℝ := qScale N (S.κ N) (S.invβ N)

/-- Assumption A.2 for the whole sequence, in the regime `Rg` (`ν₀` for R3), for every `N ≥ 1`. -/
def RegimeHolds (Rg : PDE.Regime) (ν₀ : ℝ) : Prop :=
  ∀ N : ℕ, 1 ≤ N → RdRegimeHolds Rg d S.s S.M (S.invβ N) ν₀

end WholeMainData

/-- The random data at particle number `N` on `ℝ^d`: probability space, `X_N^0`, Brownian motions, the particle
flow `X_N`, and the initial fluctuation functional `η°` (a random real-linear functional on the test class). -/
structure RealizationRd (d N : ℕ) where
  Ω : Type
  [mΩ : MeasurableSpace Ω]
  P : Measure Ω
  [isProb : IsProbabilityMeasure P]
  X₀ : Ω → EucConfig d N
  W : ℝ≥0 → Ω → (Fin N → Euc d)
  X : ℝ≥0 → Ω → EucConfig d N
  η : Ω → (Euc d → ℝ) → ℝ

attribute [instance] RealizationRd.mΩ RealizationRd.isProb

/-! ### Assumption A.1 on `ℝ^d` -/

/-- Pathwise uniqueness among collision-free whole-space strong solutions (`HRS.PathwiseUnique`, on `ℝ^d`). -/
def WholePathwiseUnique {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (P : Measure Ω) (D : WholeDyn d)
    (T : ℝ) (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) : Prop :=
  ∀ X X' : ℝ≥0 → Ω → EucConfig d N, IsWholeStrongSolution P D T X₀ W X →
    IsWholeStrongSolution P D T X₀ W X' → ∀ᵐ ζ ∂P, ∀ t : ℝ≥0, (t : ℝ) ≤ T → X t ζ = X' t ζ

/-- A whole-space strong solution **without** the collision-free clause (case (c) of A.1, and the
Cépa-Lépingle flow; `HRS.IsContactStrongSolution` on `ℝ^d`). -/
structure IsWholeContactStrongSolution {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (P : Measure Ω)
    (D : WholeDyn d) (T : ℝ) (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d))
    (X : ℝ≥0 → Ω → EucConfig d N) : Prop where
  init : ∀ᵐ ζ ∂P, X 0 ζ = X₀ ζ
  eqn : ∀ᵐ ζ ∂P, ∀ t : ℝ≥0, (t : ℝ) ≤ T →
    (∀ i, IntegrableOn (fun s : ℝ => particleDriftW D (X (Real.toNNReal s) ζ) i)
      (Set.Icc 0 (t : ℝ))) ∧
    ∀ i, X t ζ i = X 0 ζ i +
      (∫ s in Set.Icc (0 : ℝ) t, particleDriftW D (X (Real.toNNReal s) ζ) i) +
      Real.sqrt (2 * D.invβ) • (W t ζ i - W 0 ζ i)
  cont : ∀ᵐ ζ ∂P, ∀ i, Continuous fun t => X t ζ i
  adapted : ∀ t : ℝ≥0, Measurable (X t)

/-- The ordered Cépa-Lépingle flow on the line (S L9724-9737, `d = 1`): a contact-allowing strong solution that is
ordered for all times by a (random, measurable) labelling fixed at time `0`, whose contact set has Lebesgue measure
zero a.s. (`HRS.IsCepaLepingleFlow` without the periodic spread condition). -/
structure IsWholeCepaLepingleFlow {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (P : Measure Ω)
    (D : WholeDyn d) (T : ℝ) (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d))
    (X : ℝ≥0 → Ω → EucConfig d N) : Prop where
  toContact : IsWholeContactStrongSolution P D T X₀ W X
  ordered : ∃ π : Ω → Equiv.Perm (Fin N), (∀ σ, MeasurableSet {ζ | π ζ = σ}) ∧
    ∀ᵐ ζ ∂P, ∀ t : ℝ≥0, (t : ℝ) ≤ T → ∀ j : Fin d, ∀ k k' : Fin N, k ≤ k' →
      X t ζ (π ζ k) j ≤ X t ζ (π ζ k') j
  occupation : ∀ᵐ ζ ∂P, volume {s : ℝ | s ∈ Set.Icc 0 T ∧ X (Real.toNNReal s) ζ ∈ eucCollisionSet d N} = 0

/-- Assumption A.1 `B:ass:sde` (M L10127-10143, valid on `𝔻 = ℝ^d`, with the whole-space construction of
S L9698-9737) for one `N`: `X_N^0` is a.s. pairwise distinct and independent of `(W_i)`, and the flow is
(a)/(d) the pathwise unique collision-free strong solution, (b) `d = 1`, `s = 0`, `β_N < ∞`, `M = -a`: the ordered
Cépa-Lépingle flow, or (c) `d = 1`, `s = 0`, `β_N < ∞`, `M = 0`: a contact-allowing strong solution (the cases (a)
and (d) of the TeX collapse as in `HRS.SelectedFlow`). -/
structure SelectedFlowRd {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (P : Measure Ω) (D : WholeDyn d)
    (T : ℝ) (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d))
    (X : ℝ≥0 → Ω → EucConfig d N) : Prop where
  init_meas : Measurable X₀
  init_distinct : ∀ᵐ ζ ∂P, X₀ ζ ∉ eucCollisionSet d N
  brownian : IsVectorBrownian P W
  indep : IndepFun X₀ (fun ζ => fun t => W t ζ) P
  flow :
    (IsWholeStrongSolution P D T X₀ W X ∧ WholePathwiseUnique P D T X₀ W) ∨
    (d = 1 ∧ D.s = 0 ∧ 0 < D.invβ ∧ (∃ a : ℝ, 0 < a ∧ D.M = -(a • 1)) ∧
      IsWholeCepaLepingleFlow P D T X₀ W X) ∨
    (d = 1 ∧ D.s = 0 ∧ 0 < D.invβ ∧ D.M = 0 ∧ IsWholeContactStrongSolution P D T X₀ W X)

/-- Assumption A.1 for a sequence of realizations: for every `N ≥ 1`. -/
def SelectedFlowsRd (S : WholeMainData d) (R : ∀ N, RealizationRd d N) : Prop :=
  ∀ N : ℕ, 1 ≤ N → SelectedFlowRd (R N).P (S.dyn N) S.T (R N).X₀ (R N).W (R N).X

/-! ### Assumption A.3 on `ℝ^d` -/

/-- Assumption A.3 `B:ass:mf-reg` (M L10201-10203) on `ℝ^d` at the derivative index `r` (`r = m + 3`; S L9660-9665):
for each `N ≥ 1`, `μ_{β_N}` solves the whole-space mean-field equation with viscosity `β_N⁻¹` and datum `μ°` (weak
form `B:eq:mf-weak` on `ℝ^d`, `IsWholeMeanFieldSolution`), is `(r,Λ)`-regular in the sense of
`S:eq:mf-regularity-whole` (with the proviso for `d-1 ≤ s < d`), and `∂_tμ_{β_N} ∈ C([0,T]; C_b^0)` uniformly in
`N`. -/
structure MeanFieldRegularityRd (S : WholeMainData d) (r : ℕ) (Λ : ℝ) : Prop where
  solution : ∀ N : ℕ, 1 ≤ N → IsWholeMeanFieldSolution (S.dyn N) S.T (S.ρ N)
  datum : ∀ N : ℕ, 1 ≤ N → withDensityReal (S.ρ N 0) = S.μ0
  regular : ∀ N : ℕ, 1 ≤ N → IsRegularMFRd S.s r Λ S.T (S.ρ N)
  time_derivative : ∃ (B : ℝ) (ρt : ℕ → ℝ → Euc d → ℝ), ∀ N : ℕ, 1 ≤ N →
    (∀ t ∈ Set.Icc (0 : ℝ) S.T, ∀ x : Euc d,
      HasDerivWithinAt (fun u => S.ρ N u x) (ρt N t x) (Set.Icc (0 : ℝ) S.T) t) ∧
    ContinuousOn (fun p : ℝ × Euc d => ρt N p.1 p.2) (Set.Icc (0 : ℝ) S.T ×ˢ Set.univ) ∧
    ∀ t ∈ Set.Icc (0 : ℝ) S.T, ∀ x : Euc d, |ρt N t x| ≤ B

/-! ### The second-moment conditions -/

/-- The empirical second moment `⟨|x|², μ⟩`. -/
def secondMomentOf (μ : Measure (Euc d)) : ℝ := pair μ (fun x => ‖x‖ ^ 2)

/-- `B:eq:initial-second-moment` (S L9851-9852): `𝔪₂⁰ := sup_N E[⟨|x|², μ_N^0⟩] < ∞`, as: the real `B` (`m20`) bounds
`E[⟨|x|², μ_N^0⟩]` for all `N ≥ 1` (`lintegral` form). -/
def InitialSecondMoment (S : WholeMainData d) (R : ∀ N, RealizationRd d N) (B : ℝ) : Prop :=
  ∀ N : ℕ, 1 ≤ N →
    ∫⁻ ζ, ENNReal.ofReal (secondMomentOf (empirical ((R N).X₀ ζ))) ∂(R N).P ≤ ENNReal.ofReal B

/-- `m₂` bounds the propagated second moment of `B:lem:moments` (S.A.18, S L10478-10484):
`sup_N sup_{t ∈ [0,T]} E[⟨|x|², μ_N^t + μ_{β_N}^t⟩] ≤ m₂`. -/
def PropagatedSecondMoment (S : WholeMainData d) (R : ∀ N, RealizationRd d N) (m₂ : ℝ) : Prop :=
  ∀ N : ℕ, 1 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) S.T,
    ∫⁻ ζ, ENNReal.ofReal (secondMomentOf (empirical ((R N).X (Real.toNNReal t) ζ)) +
        secondMomentOf (withDensityReal (S.ρ N t))) ∂(R N).P ≤ ENNReal.ofReal m₂

/-- `𝔴_N := inf_{R ≥ 1} [R^{d/2}(N^{-1/d} + 𝔈_N^{1/2}) + 𝔪₂/R²]` (`B:eq:wN-def`, S L9854-9858), with `E = 𝔈_N`,
`m₂ = 𝔪₂`. -/
def wN (d : ℕ) (N : ℕ) (E m₂ : ℝ) : ℝ :=
  ⨅ R : {R : ℝ // 1 ≤ R},
    R.1 ^ ((d : ℝ) / 2) * ((N : ℝ) ^ (-(1 : ℝ) / d) + E ^ ((1 : ℝ) / 2)) + m₂ / R.1 ^ 2

/-- The error bound `𝔯^{ℝ^d}_{N,nd} = ε_N + (σ_N²/(Nβ_N))^{1/2} 𝔴_N^{1/2} + σ_N 𝔈_N` (`B:eq:master-rate-rd-nd`,
S L9869-9873) and its variants `B:eq:master-rate-rd-dec` (`e = e_N^𝔠`, last term `σ_N(𝔈_N + e_N^𝔠)`), the `W₂`
version (`𝔈'_N` in place of `𝔈_N` in the last term): `rdRate ε q σ 𝔴 E e = ε + √q √𝔴 + σ (E + e)`. -/
def rdRate (ε q σ w E e : ℝ) : ℝ := ε + Real.sqrt q * Real.sqrt w + σ * (E + e)

/-! ### Assumption A.4 on `ℝ^d` -/

/-- Assumption A.4 `B:ass:init` (M L10207-10218) with the whole-space test class
`Y_0 = H^{m_0}_uloc ∩ C_b^{0,1}`, `‖ψ‖_{Y_0} = ‖ψ‖_{H^{m_0}(ϖ)} + ‖ψ‖_{C_b^{0,1}}` (S L9680-9690): the coupling
`(X_N^0, η°)` for the finite family whose transported terminal tests span `span (Ψ N)`, `m₀ ∈ {1,…,m_*}`,
`C_in ≥ 1`, `ε_N ↓ 0`:
(I1) `E|⟨ψ,κ_NΞ_N^0⟩ - ⟨ψ,η°⟩| ≤ ε_N ‖ψ‖_{Y_0}` for `ψ ∈ span (Ψ N)`, `ψ ∈ Y_0`;
(I2) `E|⟨ψ,κ_NΞ_N^0⟩|² + E|⟨ψ,η°⟩|² ≤ C_in² ‖ψ‖²_{H^{m_0}(ϖ)}` for every real `ψ ∈ Y_0` (S L9686-9687: the second-moment
bound uses `‖ψ‖_{H^{m_0}(ϖ)}` on the right);
(I3) `(X_N^0, η°)` is independent of the Brownian motions.  `η°` is a random real-linear functional on `Y_0` of fixed
law.  The cutoff `χ` of `Y_0` is the parameter `χ`.  Expectations are `lintegral`s of `ofReal`. -/
structure InitialFluctuationRd (S : WholeMainData d) (R : ∀ N, RealizationRd d N) (χ : Euc d → ℝ)
    (m₀ : ℕ) (Cin : ℝ) (ε : ℕ → ℝ) (Ψ : ℕ → Set (Euc d → ℝ)) : Prop where
  cutoff : IsUlocCutoff χ
  m₀_pos : 1 ≤ m₀
  m₀_le : m₀ ≤ mStar d
  Cin_ge : 1 ≤ Cin
  eps_anti : Antitone ε
  eps_tendsto : Tendsto ε atTop (𝓝 0)
  family_finite : ∀ N, (Ψ N).Finite
  linear : ∀ N : ℕ, ∀ ζ, ∀ ψ ψ' : Euc d → ℝ, ∀ c : ℝ, Y0Class m₀ χ ψ → Y0Class m₀ χ ψ' →
    (R N).η ζ (c • ψ + ψ') = c * (R N).η ζ ψ + (R N).η ζ ψ'
  η_meas : ∀ N : ℕ, ∀ ψ : Euc d → ℝ, Measurable fun ζ => (R N).η ζ ψ
  fixed_law : ∃ νη : Measure ((Euc d → ℝ) → ℝ), ∀ N : ℕ, 1 ≤ N → law (R N).P (R N).η = νη
  I1 : ∀ N : ℕ, 1 ≤ N → ∀ ψ ∈ Submodule.span ℝ (Ψ N), Y0Class m₀ χ ψ →
    ∫⁻ ζ, ENNReal.ofReal |S.κ N * (pair (empirical ((R N).X₀ ζ)) ψ - pair S.μ0 ψ) - (R N).η ζ ψ|
        ∂(R N).P ≤ ENNReal.ofReal (ε N * y0Norm m₀ χ ψ)
  I2 : ∀ N : ℕ, 1 ≤ N → ∀ ψ : Euc d → ℝ, Y0Class m₀ χ ψ →
    ∫⁻ ζ, ENNReal.ofReal ((S.κ N * (pair (empirical ((R N).X₀ ζ)) ψ - pair S.μ0 ψ)) ^ 2)
        ∂(R N).P +
      ∫⁻ ζ, ENNReal.ofReal (((R N).η ζ ψ) ^ 2) ∂(R N).P ≤
    ENNReal.ofReal (Cin ^ 2 * (varpiNormE m₀ χ ψ).toReal ^ 2)
  I3 : ∀ N : ℕ, 1 ≤ N →
    IndepFun (fun ζ => ((R N).X₀ ζ, (R N).η ζ)) (fun ζ => fun t => (R N).W t ζ) (R N).P

/-! ### Assumptions A.6, A.7 on `ℝ^d` -/

/-- The corrected energy `F_N(X_N^t, μ_{β_N}^t) + 𝔬_N(Λ)` along a particle path (whole-space modulated energy
`HRS.Whole.rieszModulatedEnergy`, `𝔬_N(Λ) = oNΛ d s C₀ Λ N`, `B:eq:hrs-coercivity-exact-correction`). -/
def correctedEnergyRd (S : WholeMainData d) (C₀ Λ : ℝ) (N : ℕ) (X : EucConfig d N) (t : ℝ) : ℝ :=
  rieszModulatedEnergy d S.s X (withDensityReal (S.ρ N t)) + oNΛ d S.s C₀ Λ N

/-- "The corrected energy is nonnegative" (M L10251-10252, the property of a heat-kernel completion `C₀`
`H:eq:energy-completion` chosen once): for all `Λ ≥ 1`, `N ≥ 2`, probability densities `ρ ≤ Λ` and collision-free
configurations, `F_N(X,ρ) + oNΛ ≥ 0`.  Statement repair (docs/ISSUES.md, 2026-10-19, repair note): at `s = 0` the densities
`ρ` carry the finite logarithmic moment `∫ log(2+|x|) dρ < ∞` (TeX: "admissible μ"); without it the Bochner integrals in the
interaction energy are junk `0` and the inequality fails for every `C₀` (`RdStanding` was unsatisfiable at `s = 0`).
(Technical hypothesis: the whole-space counterpart of
`HRS.Main.IsCoercivityPair`, whose lower bound is `B:eq:hrs-periodic-coercivity-lower`; the whole-space coercivity is
used in S L10520 as `B:prop:coercivity`.) -/
def CompletionNonnegRd (d : ℕ) (s C₀ : ℝ) : Prop :=
  0 ≤ C₀ ∧ ∀ Λ : ℝ, 1 ≤ Λ → ∀ N : ℕ, 2 ≤ N → ∀ ρ : Euc d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
    (s = 0 → Integrable (fun x : Euc d => Real.log (2 + ‖x‖)) (withDensityReal ρ)) →
    ∀ X : EucConfig d N, X ∉ eucCollisionSet d N →
      0 ≤ rieszModulatedEnergy d s X (withDensityReal ρ) + oNΛ d s C₀ Λ N

/-- Assumption A.6 `B:ass:MF` (M L10235-10247) on `ℝ^d`: a sequence `𝔈_N > 0` with
`sup_{t ≤ T} E[F_N(X_N^t, μ_{β_N}^t) + 𝔬_N] ≤ 𝔈_N` (`lintegral` of `ofReal`; the corrected energy is
nonnegative by `completion`) and `σ_N 𝔈_N → 0`. -/
structure EnergySmallnessRd (S : WholeMainData d) (R : ∀ N, RealizationRd d N) (C₀ Λ : ℝ)
    (𝔈 : ℕ → ℝ) : Prop where
  completion : CompletionNonnegRd d S.s C₀
  pos : ∀ N : ℕ, 1 ≤ N → 0 < 𝔈 N
  bound : ∀ N : ℕ, 1 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) S.T,
    ∫⁻ ζ, ENNReal.ofReal (correctedEnergyRd S C₀ Λ N ((R N).X (Real.toNNReal t) ζ) t) ∂(R N).P ≤
      ENNReal.ofReal (𝔈 N)
  small : Tendsto (fun N => S.sigma N * 𝔈 N) atTop (𝓝 0)

/-- Assumption A.7 `B:ass:MF2` (M L10249-10259) on `ℝ^d`: `sup_{t≤T} E[(F_N + 𝔬_N)²] ≤ (𝔈'_N)²`,
`σ_N𝔈'_N → 0`, and (I1) in `L²` with `ε_N^{(2)}` on the span of the transported tests `Ψ N`. -/
structure EnergySmallness2Rd (S : WholeMainData d) (R : ∀ N, RealizationRd d N) (C₀ Λ : ℝ)
    (χ : Euc d → ℝ) (m₀ : ℕ) (Ψ : ℕ → Set (Euc d → ℝ)) (𝔈' ε2 : ℕ → ℝ) : Prop where
  𝔈'_nonneg : ∀ N : ℕ, 1 ≤ N → 0 ≤ 𝔈' N
  ε2_nonneg : ∀ N : ℕ, 1 ≤ N → 0 ≤ ε2 N
  bound : ∀ N : ℕ, 1 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) S.T,
    ∫⁻ ζ, ENNReal.ofReal
        ((correctedEnergyRd S C₀ Λ N ((R N).X (Real.toNNReal t) ζ) t) ^ 2) ∂(R N).P ≤
      ENNReal.ofReal ((𝔈' N) ^ 2)
  small : Tendsto (fun N => S.sigma N * 𝔈' N) atTop (𝓝 0)
  I1_L2 : ∀ N : ℕ, 1 ≤ N → ∀ ψ ∈ Submodule.span ℝ (Ψ N), Y0Class m₀ χ ψ →
    ∫⁻ ζ, ENNReal.ofReal
        ((S.κ N * (pair (empirical ((R N).X₀ ζ)) ψ - pair S.μ0 ψ) - (R N).η ζ ψ) ^ 2)
        ∂(R N).P ≤
      ENNReal.ofReal ((ε2 N) ^ 2 * y0Norm m₀ χ ψ ^ 2)

/-! ### The common package of the whole-space theorems -/

/-- The hypotheses shared by the whole-space theorems S.A.2-S.A.11, besides the regime (which is part of each
statement): A.1, A.3 at the derivative index `r` with `‖μ‖ ≤ Λ`, the bounds `|M| ≤ MB` (entrywise) and
`V` with `m_V` derivatives (`VHypRd mV ΛV G₀`), A.6 with `Λ`, and the second-moment condition
`B:eq:initial-second-moment`. -/
structure RdStanding (S : WholeMainData d) (R : ∀ N, RealizationRd d N) (MB Λ ΛV G₀ m20 : ℝ)
    (r mV : ℕ) (C₀ : ℝ) (𝔈 : ℕ → ℝ) : Prop where
  flow : SelectedFlowsRd S R
  mean_field : MeanFieldRegularityRd S r Λ
  matrix_bound : PDE.MatBound MB S.M
  potential : VHypRd mV ΛV G₀ S.V
  energy : EnergySmallnessRd S R C₀ Λ 𝔈
  second_moment : InitialSecondMoment S R m20
  /-- Strong-solution adaptedness of the selected flows (A.1, "strong solution"; added 2026-10-15, ISSUES §I). -/
  filtered : ∀ N, ∃ (ℱ : Filtration ℝ (R N).mΩ) (W' : ℝ≥0 → (R N).Ω → (Fin N × Fin d) → ℝ),
    IsWholeFilteredSolution (R N).P ℱ W' (R N).W (R N).X


/-! ### Statistics and their laws on `ℝ^d` -/

section Statistics

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The transported terminal tests `{U_N^{0,t_a} φ_a}` of the finite family `(φ_a, t_a)` (the generators of the
finite-dimensional span in A.4, M L10208), with the whole-space adjoint propagator `propagatorW`. -/
def transportedTestsRd (S : WholeMainData d) (ts : ι → ℝ) (φ : ι → Euc d → ℝ) (N : ℕ) :
    Set (Euc d → ℝ) :=
  Set.range fun a => propagatorW (S.coeff N) 0 (ts a) (φ a)

/-- The particle statistics `(⟨φ_a, σ Ξ_N^{t_a}⟩)_a`, `Ξ_N^t = μ_N^t - μ_{β_N}^t`, a vector in `ℝ^ι`. -/
def fluctStatRd {Ω : Type*} {N : ℕ} (σ : ℝ) (X : ℝ≥0 → Ω → EucConfig d N) (ρ : ℝ → Euc d → ℝ)
    (ts : ι → ℝ) (φ : ι → Euc d → ℝ) (ζ : Ω) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 fun a =>
    σ * (pair (empirical (X (Real.toNNReal (ts a)) ζ)) (φ a) - pair (withDensityReal (ρ (ts a))) (φ a))

/-- The law of the particle statistics. -/
def fluctStatLawRd {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (P : Measure Ω) (σ : ℝ)
    (X : ℝ≥0 → Ω → EucConfig d N) (ρ : ℝ → Euc d → ℝ) (ts : ι → ℝ) (φ : ι → Euc d → ℝ) :
    Measure (EuclideanSpace ℝ ι) :=
  law P (fluctStatRd σ X ρ ts φ)

/-- The law of the linear approximation `𝔖_N^t[φ⃗] = (A_N ⟨U_N^{0,t_a}φ_a, η°⟩ + G_a)_a` (`B:eq:surrogate-def`,
M L10266-10270) with the whole-space coefficients `C` (`β_N, μ_{β_N}`), `G` centered Gaussian independent of `η°`
with covariance `𝗏_N^t[φ_a,φ_b] = 2q ∫_0^{t_a∧t_b}⟨∇U^{r,t_a}φ_a·∇U^{r,t_b}φ_b, μ^r⟩ dr` (`noiseCovW`): the
convolution of the law of `(A η°(U^{0,t_a}φ_a))_a` with the centered Gaussian (as `HRS.Main.surrogateStatLaw`). -/
def surrogateStatLawRd {Ω : Type*} [MeasurableSpace Ω] (C : WholeCoeff d) (A q : ℝ)
    (ts : ι → ℝ) (φ : ι → Euc d → ℝ) (P : Measure Ω) (η : Ω → (Euc d → ℝ) → ℝ) :
    Measure (EuclideanSpace ℝ ι) :=
  law P (fun ζ => (WithLp.toLp 2 fun a => A * η ζ (propagatorW C 0 (ts a) (φ a)) :
      EuclideanSpace ℝ ι)) ∗
    multivariateGaussian 0 (Matrix.of fun a b => noiseCovW C q (ts a) (ts b) (φ a) (φ b))

end Statistics

/-- The real family `(Re φ_a, Im φ_a)` indexed by `ι × Bool` of a complex family (the statistics of complex tests
"viewed in `ℝ^{2p}`", M L10310). -/
def realImPartsRd {ι : Type*} (φ : ι → Euc d → ℂ) : ι × Bool → Euc d → ℝ :=
  fun ab x => if ab.2 then (φ ab.1 x).im else (φ ab.1 x).re

/-- The plane wave `e_ξ(x) = e^{2πi ξ·x}` (`ξ ∈ ℝ^d`; S L9889, L11004-11010: `‖e_k‖_{H^m_uloc} ≤ C(1+|k|)^m`,
with `‖e_k‖_{H^m} = (1+4π²|k|²)^{m/2}` for the torus mode `e^{2πik·x}`). -/
def planeWave (ξ : Euc d) (x : Euc d) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (inner ℝ ξ x : ℝ))

/-- A class of real terminal tests together with its norm: the admissible tests (finite norm; continuous, since the
statistics evaluate tests pointwise) and the norm.  For a complex test the norm is
`‖φ‖ = (‖Re φ‖² + ‖Im φ‖²)^{1/2}` (`normC`). -/
structure TestClassRd (d : ℕ) where
  mem : (Euc d → ℝ) → Prop
  norm : (Euc d → ℝ) → ℝ

/-- A complex test is admissible iff its real and imaginary parts are. -/
def TestClassRd.memC (𝒴 : TestClassRd d) (φ : Euc d → ℂ) : Prop :=
  𝒴.mem (fun x => (φ x).re) ∧ 𝒴.mem (fun x => (φ x).im)

/-- `‖φ‖ = (‖Re φ‖² + ‖Im φ‖²)^{1/2}` of a complex test (for `𝒴 = H^m_uloc` this is the exact norm of the complex
function, since the cross term of the Fourier form vanishes for real `Re, Im`; for `W^{m,p}` it is an equivalent
norm). -/
def TestClassRd.normC (𝒴 : TestClassRd d) (φ : Euc d → ℂ) : ℝ :=
  Real.sqrt (𝒴.norm (fun x => (φ x).re) ^ 2 + 𝒴.norm (fun x => (φ x).im) ^ 2)

/-- `Y_nd = H^m_uloc(ℝ^d)` as a test class (`m = m_*` in S.A.2): continuous tests with
`‖φ‖_{H^m_uloc} < ∞` (**technical**: `Continuous`, because `H^{m_*}_uloc ⊂ C_b²` and the statistics evaluate
tests pointwise). -/
def ulocClass (m : ℕ) (χ : Euc d → ℝ) : TestClassRd d :=
  ⟨fun φ => Continuous φ ∧ ulocNormE m χ φ < ⊤, fun φ => (ulocNormE m χ φ).toReal⟩

/-- `W^{m,p}(ℝ^d)` as a test class (S.A.4, `m = m_𝔠, p = p_𝔠`): the norm is `HRS.Whole.movWNormE`
(`∑_{i ≤ m} ‖ |D^iφ| ‖_{L^p}`) of the classical derivatives.  **Technical**: tests are of class `C^m` (the norm
uses classical derivatives; `C^m ∩ W^{m,p}` is dense in `W^{m,p}`). -/
def wClass (m : ℕ) (p : ℝ) : TestClassRd d :=
  ⟨fun φ => ContDiff ℝ m φ ∧ movWNormE m (ENNReal.ofReal p) φ < ⊤,
    fun φ => (movWNormE m (ENNReal.ofReal p) φ).toReal⟩

/-! ### The Banach spaces `W^{m,p}(ℝ^d)` and the weak norm `wNormE` (moved here, rename-free, from the S.A.16 block of `AppendixAAdjoint.lean` and from after `main_rd_path`, M3-FIX F1: `wWeakClass` below needs them) -/

/-- The index set `{(j, i_1…i_j) : j ≤ m}` of the partial derivatives of order `≤ m` (ordered index tuples). -/
abbrev WIndex (d m : ℕ) : Type := Σ j : Fin (m + 1), (Fin j → Fin d)

/-- The jet `φ ↦ (∂_{i_1}⋯∂_{i_j}φ)_{j ≤ m}` of a function, a function `ℝ^d → (WIndex d m → ℝ)`. -/
def wJet (m : ℕ) (φ : Euc d → ℝ) : Euc d → (WIndex d m → ℝ) :=
  fun x τ => partialDeriv τ.2 φ x

/-- `C_c^∞(ℝ^d)`. -/
def IsCcInfty (φ : Euc d → ℝ) : Prop := ContDiff ℝ ∞ φ ∧ HasCompactSupport φ

/-- `L^p(ℝ^d; ℝ^{WIndex d m})`, `p ∈ [2,∞)`. -/
abbrev WLp (d m : ℕ) (p : ℝ) : Type :=
  Lp (WIndex d m → ℝ) (ENNReal.ofReal p) (volume : Measure (Euc d))

instance (p : ℝ) [hp : Fact (2 ≤ p)] : Fact (1 ≤ ENNReal.ofReal p) :=
  ⟨by
    have h : (1 : ℝ) ≤ p := by linarith [hp.out]
    simpa using ENNReal.ofReal_le_ofReal h⟩

/-- `W^{m,p}(ℝ^d)`, `p ∈ [2,∞)`, as the closure of the jets `{(∂^αφ)_{|α|≤m} : φ ∈ C_c^∞}` in
`L^p(ℝ^d; ℝ^{WIndex d m})` (the sup norm on the finite-dimensional factor; an equivalent norm on `W^{m,p}`,
`∑_{j≤m}‖D^jφ‖_{L^p}` up to constants depending on `d, m`).  For `1 ≤ p < ∞` this closure is `W^{m,p}`
(Meyers-Serrin). -/
def WmpSpace (d m : ℕ) (p : ℝ) [Fact (2 ≤ p)] : Submodule ℝ (WLp d m p) :=
  (Submodule.span ℝ {F : WLp d m p |
    ∃ φ : Euc d → ℝ, IsCcInfty φ ∧ (F : Euc d → (WIndex d m → ℝ)) =ᵐ[volume] wJet m φ}).topologicalClosure

/-- The index `(0, ())` of the zeroth derivative in `WIndex d m`. -/
def wZero (d m : ℕ) : WIndex d m := ⟨⟨0, Nat.succ_pos m⟩, fun i => Fin.elim0 i⟩

/-- `‖u‖_{W^{m,p}(ℝ^d)}` in `ℝ≥0∞` (`⊤` if `u` is not in `W^{m,p}`): the infimum of the norms of the elements `G` of
`WmpSpace d m p` whose zeroth component is `u` a.e. (such `G`, i.e. the weak derivatives, is unique). -/
def wNormE (m : ℕ) (p : ℝ) [Fact (2 ≤ p)] (u : Euc d → ℝ) : ℝ≥0∞ :=
  ⨅ (G : WmpSpace d m p) (_ : ∀ᵐ x ∂(volume : Measure (Euc d)),
    ((G : WLp d m p) : Euc d → (WIndex d m → ℝ)) x (wZero d m) = u x), ENNReal.ofReal ‖G‖

open Classical in
/-- The WEAK `W^{m,p}(ℝ^d)` class (M3-FIX F1, the output class of the S.A.4 / S.A.11 adjoint input): `u` is admissible iff its
weak `W^{m,p}`-norm (`wNormE`, the norm of the `W^{m,p}` element with zeroth component `u` a.e.) is finite, with that norm;
NO classical regularity is asked (unlike `wClass`, whose `mem` demands `C^m` and the classical-derivative norm `movWNormE`).
This is the form in which S.A.16 `adjoint_lp` delivers `U^{r,t}φ` (weak `W^{m,p}` bound; `C²` only from `adjoint_lp_classical`).
For `p < 2` (outside the standing range, `Fact (2 ≤ p)` of `wNormE`) the class is empty with norm `0`. -/
def wWeakClass (m : ℕ) (p : ℝ) : TestClassRd d :=
  if h : 2 ≤ p then
    haveI : Fact (2 ≤ p) := ⟨h⟩
    ⟨fun u => wNormE m p u < ⊤, fun u => (wNormE m p u).toReal⟩
  else ⟨fun _ => False, fun _ => 0⟩
/-- M3 adjoint input from the test class `𝒴` into the output class `𝒵` for ONE coefficient `C` (decision M3, docs/SA12_PLAN.md
section 2; M3-FIX F1: two classes).  Content: S.A.12 main bound + (a) for `𝒴 = 𝒵 = H^{m_*}_uloc` (`ulocClass`), S.A.16 +
`adjoint_lp_classical` for `𝒴 = wClass m p` (classical `C^m ∩ W^{m,p}` tests) and `𝒵 = wWeakClass m p` (S.A.16 gives only the weak
`W^{m,p}` bound for `U^{r,t}φ`, plus `C²` regularity, so the output class is the weak one).  For every `0 ≤ r ≤ t ≤ T` (including
`t = 0`) and every `C²` test `φ ∈ 𝒴`: the classical adjoint solution `f` with terminal datum `φ` exists (`IsClassicalAdjointW`),
`U^{r,t}φ := propagatorW C r t φ` belongs to `𝒵` with `‖U^{r,t}φ‖_𝒵 ≤ K‖φ‖_𝒴`, and `U^{r,t}φ ∈ C_b^j` with
`‖U^{r,t}φ‖_{C_b^j} ≤ K‖φ‖_𝒴`.  `K` absorbs `e^{Λ_m T}`.  Used with `j = 2` for `𝒴 = 𝒵 = ulocClass m_*` (S.A.2, S.A.3) and `j = m_*`
for `(𝒴, 𝒵) = (wClass m p, wWeakClass m p)` (S.A.4, S.A.11).  The membership clause `𝒵.mem (U^{r,t}φ)` is needed because
`ulocClass.norm`, `wWeakClass.norm` are `toReal` of an `ℝ≥0∞` norm (junk `0` at `⊤`).
Tie to the adjoint theorems: `propagatorW` is a `choose`, tied to the solution of S.A.12 / S.A.16 only through uniqueness of
classical solutions, available (coefficient hypotheses `CoeffHypRd`, `MatBound`, `VHypRd`) in the regimes R1, R2a, R2c, R3 (F-CAU,
S.A.33) and in the corner `d-2 < s`, `SymNonpos M` (`HRS/MS/StarTie.lean`, `propagatorW_unique_star`); the hypothesis is not
claimed to follow from S.A.12 / S.A.16 outside these.  The rows with `𝒴 = wClass` additionally need S.A.16 (M2), not S.A.12. -/
def AdjointInputRd (𝒴 𝒵 : TestClassRd d) (j : ℕ) (C : WholeCoeff d) (T K : ℝ) : Prop :=
  ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T → ∀ φ : Euc d → ℝ, ContDiff ℝ 2 φ → 𝒴.mem φ →
    (∃ f, IsClassicalAdjointW C t φ f) ∧
    𝒵.mem (propagatorW C r t φ) ∧ 𝒵.norm (propagatorW C r t φ) ≤ K * 𝒴.norm φ ∧
    MemCb j (propagatorW C r t φ) ∧ cbNorm j (propagatorW C r t φ) ≤ K * 𝒴.norm φ

/-- The conclusions (a)-(d) of `B:thm:main-torus-stat` (M L10301-10316) on `ℝ^d`, for the test class `𝒴` in place of
`H^{m_*}(𝕋^d)` and the rate `𝔯_N = rdRate ε_N q_N σ_N 𝔴_N 𝔈_N e_N`:
* (a) single statistics, `W₁`: `W₁(Law⟨φ,σ_NΞ_N^t⟩, Law 𝔖_N^t[φ]) ≤ C e^{Λ_T t}‖φ‖(1+‖φ‖) 𝔯_N`;
* (b) joint statistics of real tests, `d_{C²}`;
* (c) complex tests at finitely many times `0 ≤ t_1 ≤ ⋯ ≤ t_q = t`, `d_{C²}`;
* (d) under A.7 the joint `W₂` variant with the rate `rdRate ε_N^{(2)} q σ 𝔴 𝔈'_N e_N` (`𝔴_N` still with `𝔈_N`).
Each part is for `t ∈ [0,T]`, `N ≥ C`, and for the finite family on which A.4 is imposed. -/
def RdStatParts (S : WholeMainData d) (R : ∀ N, RealizationRd d N) (C ΛT : ℝ) (𝒴 : TestClassRd d)
    (χ : Euc d → ℝ) (Cin C₀ Λ : ℝ) (𝔈 : ℕ → ℝ) (m₂ : ℝ) (e : ℕ → ℝ) : Prop :=
  -- (a) single statistics, `W₁`
  (∀ (m₀ : ℕ) (ε : ℕ → ℝ) (t : ℝ) (φ : Euc d → ℝ), t ∈ Set.Icc (0 : ℝ) S.T → 𝒴.mem φ →
    InitialFluctuationRd S R χ m₀ Cin ε (transportedTestsRd S (fun _ : Fin 1 => t) (fun _ => φ)) →
    ∀ N : ℕ, C ≤ (N : ℝ) →
      wassersteinE 1
        (fluctStatLawRd (R N).P (S.sigma N) (R N).X (S.ρ N) (fun _ : Fin 1 => t) (fun _ => φ))
        (surrogateStatLawRd (S.coeff N) (S.AN N) (S.qN N) (fun _ : Fin 1 => t) (fun _ => φ)
          (R N).P (R N).η) ≤
      ENNReal.ofReal (HRS.Main.statBound C ΛT t (𝒴.norm φ)
        (rdRate (ε N) (S.qN N) (S.sigma N) (wN d N (𝔈 N) m₂) (𝔈 N) (e N)))) ∧
  -- (b) joint statistics, `d_{C²}`
  (∀ (m₀ : ℕ) (ε : ℕ → ℝ) (t : ℝ) (p : ℕ) (φ : Fin p → Euc d → ℝ), 1 ≤ p →
    t ∈ Set.Icc (0 : ℝ) S.T → (∀ a, 𝒴.mem (φ a)) →
    InitialFluctuationRd S R χ m₀ Cin ε (transportedTestsRd S (fun _ : Fin p => t) φ) →
    ∀ N : ℕ, C ≤ (N : ℝ) →
      smoothDist 2
        (fluctStatLawRd (R N).P (S.sigma N) (R N).X (S.ρ N) (fun _ : Fin p => t) φ)
        (surrogateStatLawRd (S.coeff N) (S.AN N) (S.qN N) (fun _ : Fin p => t) φ
          (R N).P (R N).η) ≤
      HRS.Main.statBound C ΛT t (∑ a, 𝒴.norm (φ a))
        (rdRate (ε N) (S.qN N) (S.sigma N) (wN d N (𝔈 N) m₂) (𝔈 N) (e N))) ∧
  -- (c) complex tests, finitely many times, `d_{C²}`
  (∀ (m₀ : ℕ) (ε : ℕ → ℝ) (n : ℕ) (ts : Fin (n + 1) → ℝ) (φ : Fin (n + 1) → Euc d → ℂ),
    Monotone ts → 0 ≤ ts 0 → ts (Fin.last n) ≤ S.T → (∀ a, 𝒴.memC (φ a)) →
    InitialFluctuationRd S R χ m₀ Cin ε
      (transportedTestsRd S (fun ab : Fin (n + 1) × Bool => ts ab.1) (realImPartsRd φ)) →
    ∀ N : ℕ, C ≤ (N : ℝ) →
      smoothDist 2
        (fluctStatLawRd (R N).P (S.sigma N) (R N).X (S.ρ N)
          (fun ab : Fin (n + 1) × Bool => ts ab.1) (realImPartsRd φ))
        (surrogateStatLawRd (S.coeff N) (S.AN N) (S.qN N)
          (fun ab : Fin (n + 1) × Bool => ts ab.1) (realImPartsRd φ) (R N).P (R N).η) ≤
      HRS.Main.statBound C ΛT (ts (Fin.last n)) (∑ a, 𝒴.normC (φ a))
        (rdRate (ε N) (S.qN N) (S.sigma N) (wN d N (𝔈 N) m₂) (𝔈 N) (e N))) ∧
  -- (d) joint `W₂` variant under A.7, complex tests, finitely many times
  (∀ (m₀ : ℕ) (ε : ℕ → ℝ) (𝔈' ε2 : ℕ → ℝ) (n : ℕ) (ts : Fin (n + 1) → ℝ)
    (φ : Fin (n + 1) → Euc d → ℂ),
    Monotone ts → 0 ≤ ts 0 → ts (Fin.last n) ≤ S.T → (∀ a, 𝒴.memC (φ a)) →
    InitialFluctuationRd S R χ m₀ Cin ε
      (transportedTestsRd S (fun ab : Fin (n + 1) × Bool => ts ab.1) (realImPartsRd φ)) →
    EnergySmallness2Rd S R C₀ Λ χ m₀
      (transportedTestsRd S (fun ab : Fin (n + 1) × Bool => ts ab.1) (realImPartsRd φ)) 𝔈' ε2 →
    ∀ N : ℕ, C ≤ (N : ℝ) →
      wassersteinE 2
        (fluctStatLawRd (R N).P (S.sigma N) (R N).X (S.ρ N)
          (fun ab : Fin (n + 1) × Bool => ts ab.1) (realImPartsRd φ))
        (surrogateStatLawRd (S.coeff N) (S.AN N) (S.qN N)
          (fun ab : Fin (n + 1) × Bool => ts ab.1) (realImPartsRd φ) (R N).P (R N).η) ≤
      ENNReal.ofReal (HRS.Main.statBound C ΛT (ts (Fin.last n)) (∑ a, 𝒴.normC (φ a))
        (rdRate (ε2 N) (S.qN N) (S.sigma N) (wN d N (𝔈 N) m₂) (𝔈' N) (e N))))

/-! ### Theorem S.A.2 -/

/-- Theorem S.A.2 `B:thm:main-rd-stat` (S L9864-9879), nondecaying joint linear statistics on `ℝ^d`.
Hypotheses: `s ≥ max{0, d-2}`; `V` with `m_V = m_*+4` (`VHypRd`); A.1, A.2 (the regime `Rg`, `ν₀` for R3), A.3 at
level `m_*+3` (`r = m_* + 3`), A.4 (inside the parts, for the finite family), A.6 and the second-moment condition
`B:eq:initial-second-moment` (`RdStanding`).  Then parts (a)-(d) of `B:thm:main-torus-stat` hold (`RdStatParts`) with
`H^{m_*}(𝕋^d)` replaced by `Y_nd = H^{m_*}_uloc(ℝ^d)` (`ulocClass`) and the error bound
`𝔯^{ℝ^d}_{N,nd} = ε_N + (σ_N²/(Nβ_N))^{1/2}𝔴_N^{1/2} + σ_N𝔈_N` (`e_N = 0`), `𝔴_N` with `𝔪₂` bounded by `m₂`.
"The constants depend on the displayed test norms and the standing assumptions, but not on the spatial support of
the tests": `C, Λ_T` are chosen before the data and the tests, and depend on `(d, s, Rg, ν₀, |M|, Λ, Λ_V,
|∇V(0)|, ν̄, T, C_in, C₀)` and the cutoff `χ`.
The initial second moment `𝔪₂⁰` is bounded by `m20` (quantified before `C, Λ_T`: the constants may depend on this standing
assumption); `C, Λ_T` do not depend on the propagated number `m₂` (it enters the rate through `𝔴_N`).
Technical hypotheses: tests continuous (`ulocClass`); `ν̄` bounds `β_N⁻¹`; `m₂ ≥ 0` bounds the propagated second
moment (`PropagatedSecondMoment`); for `β_N`, `N ≥ 1` per-`N` assumptions.
M3 (decision of 2026-10-22): the extra hypothesis `AdjointInputRd (ulocClass m_*) (ulocClass m_*) 2 (S.coeff N) T Kad` (the content of S.A.12 `adjoint_rd` + `_classical` for the particle coefficients, constant `Kad`, an explicit argument, i.e. quantified before `C₀min, C, Λ_T`, which may depend on it) replaces the unproved adjoint theorem.  (`propagatorW` is tied to the S.A.12 solution by uniqueness of classical solutions: F-CAU / S.A.33 in R1, R2a, R2c, R3 and `propagatorW_unique_star` in the corner `d-2 < s`, `SymNonpos M`; see `AdjointInputRd`.) -/
theorem main_rd_stat (s : ℝ) (Rg : PDE.Regime) (ν₀ MB Λ ΛV G₀ νbar T Cin m20 : ℝ) (χ : Euc d → ℝ)
    (hχ : IsUlocCutoff χ) (Kad : ℝ) :
    ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ →
    ∃ C ΛT : ℝ, 0 < C ∧ 0 < ΛT ∧
      ∀ (S : WholeMainData d), S.s = s → S.T = T → (∀ N, S.invβ N ≤ νbar) →
      max 0 ((d : ℝ) - 2) ≤ s → S.RegimeHolds Rg ν₀ →
      ∀ (R : ∀ N, RealizationRd d N) (𝔈 : ℕ → ℝ),
        RdStanding S R MB Λ ΛV G₀ m20 (mStar d + 3) (mStar d + 4) C₀ 𝔈 →
        (∀ N : ℕ, 1 ≤ N → AdjointInputRd (ulocClass (mStar d) χ) (ulocClass (mStar d) χ) 2 (S.coeff N) S.T Kad) →
        ∀ m₂ : ℝ, 0 ≤ m₂ → PropagatedSecondMoment S R m₂ →
          RdStatParts S R C ΛT (ulocClass (mStar d) χ) χ Cin C₀ Λ 𝔈 m₂ (fun _ => 0) := by
  sorry

/-! ### Corollary S.A.3 -/

/-- Corollary S.A.3 `B:cor:fourier-statistics` (S L9881-9891), Fourier-mode statistics.  Under the hypotheses of
`main_rd_stat`, for every finite collection `ξ_1,…,ξ_q ∈ ℝ^d` (`q = n+1`) the joint law of
`(σ_NΞ̂_N^t(-ξ_a))_a = (⟨e_{ξ_a}, σ_NΞ_N^t⟩)_a` (`e_ξ = planeWave ξ`, statistics in `ℝ^{2q}` as real and imaginary
parts) is within the bound of `main_rd_stat` (c) (at the single time `t`), with `‖e_{ξ_a}‖_{H^{m_*}_uloc}` replaced by
`⟨ξ_a⟩^{m_*}` (`C, Λ_T` independent of the `ξ_a`): this is the "constants grow at most polynomially in
`max_a⟨ξ_a⟩`" of the TeX, using `‖e_ξ‖_{H^{m_*}_uloc} ≤ C⟨ξ⟩^{m_*}` (S.A.31(ii), not stated here; it is absorbed
into the constant).  `A.4` is imposed for the family of transported real and imaginary parts of the plane waves.
M3: the same adjoint input and the same `Kad` as `main_rd_stat`. -/
theorem fourier_statistics_rd (s : ℝ) (Rg : PDE.Regime) (ν₀ MB Λ ΛV G₀ νbar T Cin m20 : ℝ)
    (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) (Kad : ℝ) :
    ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ →
    ∃ C ΛT : ℝ, 0 < C ∧ 0 < ΛT ∧
      ∀ (S : WholeMainData d), S.s = s → S.T = T → (∀ N, S.invβ N ≤ νbar) →
      max 0 ((d : ℝ) - 2) ≤ s → S.RegimeHolds Rg ν₀ →
      ∀ (R : ∀ N, RealizationRd d N) (𝔈 : ℕ → ℝ),
        RdStanding S R MB Λ ΛV G₀ m20 (mStar d + 3) (mStar d + 4) C₀ 𝔈 →
        (∀ N : ℕ, 1 ≤ N → AdjointInputRd (ulocClass (mStar d) χ) (ulocClass (mStar d) χ) 2 (S.coeff N) S.T Kad) →
        ∀ m₂ : ℝ, 0 ≤ m₂ → PropagatedSecondMoment S R m₂ →
        ∀ (m₀ : ℕ) (ε : ℕ → ℝ) (n : ℕ) (ξ : Fin (n + 1) → Euc d) (t : ℝ), t ∈ Set.Icc (0 : ℝ) T →
          InitialFluctuationRd S R χ m₀ Cin ε
            (transportedTestsRd S (fun ab : Fin (n + 1) × Bool => t)
              (realImPartsRd fun a => planeWave (ξ a))) →
          ∀ N : ℕ, C ≤ (N : ℝ) →
            smoothDist 2
              (fluctStatLawRd (R N).P (S.sigma N) (R N).X (S.ρ N)
                (fun _ : Fin (n + 1) × Bool => t) (realImPartsRd fun a => planeWave (ξ a)))
              (surrogateStatLawRd (S.coeff N) (S.AN N) (S.qN N)
                (fun _ : Fin (n + 1) × Bool => t) (realImPartsRd fun a => planeWave (ξ a))
                (R N).P (R N).η) ≤
            HRS.Main.statBound C ΛT t (∑ a, jbracket (ξ a) ^ mStar d)
              (rdRate (ε N) (S.qN N) (S.sigma N) (wN d N (𝔈 N) m₂) (𝔈 N) 0) := by
  sorry

/-! ### Theorem S.A.4 -/

/-- Theorem S.A.4 `B:thm:main-rd-dec-stat` (S L9893-9905), decaying sub-Coulomb joint linear statistics.
`0 ≤ s < d-2`, `𝔠` an admissible density (Definition S.A.1, `DecayingDensity`; the constants may depend on it, so it is
fixed before `C`), `V` with `m_V = m_𝔠 + 4`, A.1-A.4, A.6 and the second moment at level `m_𝔠 + 3`.  Parts (a)-(d)
of `B:thm:main-torus-stat` hold for terminal tests in `W^{m_𝔠,p_𝔠}(ℝ^d)` (`wClass`) with the error bound
`𝔯^{ℝ^d}_{N,𝔠} = ε_N + (σ_N²/(Nβ_N))^{1/2}𝔴_N^{1/2} + σ_N(𝔈_N + e_N^𝔠)` (`B:eq:master-rate-rd-dec`); in the `W₂`
variant the last term is `σ_N(𝔈'_N + e_N^𝔠)` (`RdStatParts` (d)).
Technical hypotheses: tests of class `C^{m_𝔠}` (see `wClass`); `ν̄`, `m₂` as in `main_rd_stat`.
The constants depend on `m20` as in `main_rd_stat`; the regime hypothesis
(A.2) holds in `R1` since `s < d - 2`.
M3: the extra hypothesis `AdjointInputRd (wClass m_𝔠 p_𝔠) (wWeakClass m_𝔠 p_𝔠) m_* (S.coeff N) T Kad` (classical `C^{m_𝔠}` tests in, the WEAK `W^{m_𝔠,p_𝔠}` class out: the content of S.A.16 `adjoint_lp` + `adjoint_lp_classical`, NOT of S.A.12, which covers only the nondecaying densities; `Kad` an explicit argument as in `main_rd_stat`).  The tie of `propagatorW` to the S.A.16 solution is as in `AdjointInputRd`. -/
theorem main_rd_dec_stat (s : ℝ) (c : DecayingDensity d s) (Rg : PDE.Regime)
    (ν₀ MB Λ ΛV G₀ νbar T Cin m20 : ℝ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) (Kad : ℝ) :
    ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ →
    ∃ C ΛT : ℝ, 0 < C ∧ 0 < ΛT ∧
      ∀ (S : WholeMainData d), S.s = s → S.T = T → (∀ N, S.invβ N ≤ νbar) →
      s < (d : ℝ) - 2 → S.RegimeHolds Rg ν₀ →
      ∀ (R : ∀ N, RealizationRd d N) (𝔈 : ℕ → ℝ),
        RdStanding S R MB Λ ΛV G₀ m20 (c.sobolevIndex + 3) (c.sobolevIndex + 4) C₀ 𝔈 →
        (∀ N : ℕ, 1 ≤ N → AdjointInputRd (wClass c.sobolevIndex c.integrability) (wWeakClass c.sobolevIndex c.integrability) (mStar d) (S.coeff N) S.T Kad) →
        ∀ m₂ : ℝ, 0 ≤ m₂ → PropagatedSecondMoment S R m₂ →
          RdStatParts S R C ΛT (wClass c.sobolevIndex c.integrability) χ Cin C₀ Λ 𝔈 m₂
            c.errorRate := by
  sorry


/-! ### Remark S.A.5 -/

private lemma q35_tendsto_natpow {e : ℝ} (he : e < 0) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ e) atTop (𝓝 0) := by
  have h := (tendsto_rpow_neg_atTop (neg_pos.2 he)).comp tendsto_natCast_atTop_atTop
  simpa [Function.comp_def] using h

private lemma q35_tendsto_log_mul :
    Tendsto (fun N : ℕ => (1 + Real.log N) * (N : ℝ) ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) := by
  have h1 := q35_tendsto_natpow (e := -(1 / 2 : ℝ)) (by norm_num)
  have h2 : Tendsto (fun N : ℕ => Real.log N / (N : ℝ) ^ (1 / 2 : ℝ)) atTop (𝓝 0) :=
    ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero).comp
      tendsto_natCast_atTop_atTop
  have h3 := h1.add h2
  rw [zero_add] at h3
  refine h3.congr fun N => ?_
  rw [Real.rpow_neg (Nat.cast_nonneg N)]
  ring


/-- Remark S.A.5 `B:rem:density-tradeoff` (S L9907-9913), the checkable claim: for the lower-regularity density
(Definition S.A.1 (B), error `e_N^𝔠 = (1 + 1_{s=0} log N)N^{-2/((s+1)(s+2))}`), the condition
`σ_N e_N^𝔠 → 0` at the i.i.d. normalization `σ_N = √N` holds iff `s < (√17 - 3)/2`.  The remaining sentences of the
remark (the two densities are complementary; the sharp density exists exactly when `s > (d-4)/2`
(`DecayingDensity.sharp_exists_iff`), permits `σ_N N^{s/d-1} → 0` and uses the stronger norm `r = a/2`,
`p = 2d/(a-2)`; the lower density is available for `s > (d-4)/3` and uses `r = (d-s)/2`, `p = 2d/(d-s-2)`) restate the
definition S.A.1 and the rates of S.A.4 and are not separate claims. -/
theorem sqrtN_errorRate_tendsto_iff {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2)
    (hlow : ((d : ℝ) - 4) / 3 < s) :
    Tendsto (fun N : ℕ => Real.sqrt N * (DecayingDensity.lower hlow : DecayingDensity d s).errorRate N)
        atTop (𝓝 0) ↔ s < (Real.sqrt 17 - 3) / 2 := by
  have key : ∀ x : ℝ, 0 ≤ x → ((x + 1) * (x + 2) < 4 ↔ x < (Real.sqrt 17 - 3) / 2) := by
    intro x hx
    have h1 : x < (Real.sqrt 17 - 3) / 2 ↔ 2 * x + 3 < Real.sqrt 17 := by
      constructor <;> intro h <;> linarith
    have h2 : (2 * x + 3) ^ 2 = 4 * ((x + 1) * (x + 2)) + 1 := by ring
    rw [h1, Real.lt_sqrt (by linarith : (0 : ℝ) ≤ 2 * x + 3), h2]
    constructor <;> intro h <;> linarith
  have hgen : ∀ (c : ℝ) (N : ℕ), 1 ≤ N →
      Real.sqrt (N : ℝ) * (c * (N : ℝ) ^ (-(2 / ((s + 1) * (s + 2))))) =
        c * (N : ℝ) ^ (1 / 2 - 2 / ((s + 1) * (s + 2))) := by
    intro c N hN
    have hN0 : (0 : ℝ) < N := Nat.cast_pos.2 (by omega)
    have e : (N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (-(2 / ((s + 1) * (s + 2)))) =
        (N : ℝ) ^ (1 / 2 - 2 / ((s + 1) * (s + 2))) := by
      rw [← Real.rpow_add hN0]
      congr 1
    rw [Real.sqrt_eq_rpow, ← e]
    ring
  have hE : ∀ N : ℕ, (DecayingDensity.lower hlow : DecayingDensity d s).errorRate N =
      (1 + (if s = 0 then Real.log N else 0)) * (N : ℝ) ^ (-(2 / ((s + 1) * (s + 2)))) :=
    fun N => rfl
  simp only [hE]
  constructor
  · intro h
    by_contra hns
    push Not at hns
    have hk : 4 ≤ (s + 1) * (s + 2) := by
      by_contra hlt
      push Not at hlt
      exact absurd ((key s hs0).1 hlt) (not_lt.2 hns)
    have hspos : 0 < s := by nlinarith
    have hpos : s ≠ 0 := hspos.ne'
    have hg : ∀ᶠ N : ℕ in atTop,
        Real.sqrt (N : ℝ) * ((1 + (if s = 0 then Real.log N else 0)) *
          (N : ℝ) ^ (-(2 / ((s + 1) * (s + 2))))) =
          (N : ℝ) ^ (1 / 2 - 2 / ((s + 1) * (s + 2))) := by
      filter_upwards [eventually_ge_atTop 1] with N hN
      rw [if_neg hpos, add_zero, hgen 1 N hN, one_mul]
    have h' : Tendsto (fun N : ℕ => (N : ℝ) ^ (1 / 2 - 2 / ((s + 1) * (s + 2)))) atTop
        (𝓝 0) := h.congr' hg
    have hexp : 0 ≤ 1 / 2 - 2 / ((s + 1) * (s + 2)) := by
      have hP : 0 < (s + 1) * (s + 2) := mul_pos (by linarith) (by linarith)
      have : 2 / ((s + 1) * (s + 2)) ≤ 1 / 2 := by
        rw [div_le_iff₀ hP]
        linarith
      linarith
    have hge : ∀ᶠ N : ℕ in atTop, (1 : ℝ) ≤ (N : ℝ) ^ (1 / 2 - 2 / ((s + 1) * (s + 2))) := by
      filter_upwards [eventually_ge_atTop 1] with N hN
      exact Real.one_le_rpow (by exact_mod_cast hN) hexp
    have := ge_of_tendsto h' hge
    norm_num at this
  · intro hlt
    by_cases hs : s = 0
    · have hα : 2 / ((s + 1) * (s + 2)) = 1 := by
        rw [hs]
        norm_num
      have hg : ∀ᶠ N : ℕ in atTop,
          Real.sqrt (N : ℝ) * ((1 + (if s = 0 then Real.log N else 0)) *
            (N : ℝ) ^ (-(2 / ((s + 1) * (s + 2))))) =
            (1 + Real.log N) * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
        filter_upwards [eventually_ge_atTop 1] with N hN
        have hN0 : (0 : ℝ) < N := Nat.cast_pos.2 (by omega)
        rw [if_pos hs, hα]
        have e : Real.sqrt (N : ℝ) * (N : ℝ) ^ (-(1 : ℝ)) = (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_add hN0]
          norm_num
        calc Real.sqrt (N : ℝ) * ((1 + Real.log N) * (N : ℝ) ^ (-(1 : ℝ)))
            = (1 + Real.log N) * (Real.sqrt (N : ℝ) * (N : ℝ) ^ (-(1 : ℝ))) := by ring
          _ = (1 + Real.log N) * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by rw [e]
      exact q35_tendsto_log_mul.congr' (hg.mono fun N h => h.symm)
    · have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
      have hk : (s + 1) * (s + 2) < 4 := (key s hs0).2 hlt
      have hneg : 1 / 2 - 2 / ((s + 1) * (s + 2)) < 0 := by
        have hP : 0 < (s + 1) * (s + 2) := mul_pos (by linarith) (by linarith)
        have : 1 / 2 < 2 / ((s + 1) * (s + 2)) := by
          rw [lt_div_iff₀ hP]
          linarith
        linarith
      have hg : ∀ᶠ N : ℕ in atTop,
          Real.sqrt (N : ℝ) * ((1 + (if s = 0 then Real.log N else 0)) *
            (N : ℝ) ^ (-(2 / ((s + 1) * (s + 2))))) =
            (N : ℝ) ^ (1 / 2 - 2 / ((s + 1) * (s + 2))) := by
        filter_upwards [eventually_ge_atTop 1] with N hN
        rw [if_neg hs, add_zero, hgen 1 N hN, one_mul]
      exact (q35_tendsto_natpow hneg).congr' (hg.mono fun N h => h.symm)

/-! ### The field setting on `ℝ^d` -/

/-- A selected whole-space field density `(𝒳, Γ, e_N)` of `B:thm:main-rd-field` (S L9915-9949) (the condition under
which the adjoint estimate is available is part of it, see `HoldsAt`):
(a) `nd Rg`: `s ≥ max{0,d-2}` and the uniformly local adjoint regime `Rg ∈ {R1,R2a,R2c,R3}` of `B:thm:adjoint-rd`:
`𝒳 = H^{m_nd}_uloc`, `Γ = Γ_nd`, `e_N = 0`;
(b) `decSub c`: `0 ≤ s < d-2` and an admissible density `𝔠`: `𝒳 = W^{m_𝔠,p_𝔠}`, `Γ = Γ_𝔠`, `e_N = e_N^𝔠`;
(c) `decSuperIso m p` / `decSuperHilb m`: `d-2 < s < d` in the decaying `W^{m,p}` regimes `B:thm:adjoint-lp`
(`ii`: `M = -λI`, `λ > 0`, `p ≥ 2`; `iii`: `M = -λI + 𝒜`, `λ ≥ 0`, `𝒜* = -𝒜`, `p = 2`), with `m` chosen so that
`W^{m,p} ↪ C_b^{m_*}` (i.e. `m > m_* + d/p`): `𝒳 = W^{m,p}`, `Γ = m + 2 + ⌊d(1/2 - 1/p)⌋ + 1`, `e_N = 0`. -/
inductive FieldDensityRd (d : ℕ) (s : ℝ) : Type
  | nd (Rg : PDE.Regime)
  | decSub (c : DecayingDensity d s)
  | decSuperIso (m : ℕ) (p : ℝ)
  | decSuperHilb (m : ℕ)

namespace FieldDensityRd

variable {s : ℝ}

/-- The field index `Γ` of the selected density. -/
def Gamma : FieldDensityRd d s → ℕ
  | nd _ => gammaNd d
  | decSub c => c.gammaIndex
  | decSuperIso m p => m + 2 + ⌊(d : ℝ) * (1 / 2 - 1 / p)⌋₊ + 1
  | decSuperHilb m => m + 2 + ⌊(d : ℝ) * (1 / 2 - 1 / 2)⌋₊ + 1

/-- The additional error `e_N` of the selected density. -/
def eN : FieldDensityRd d s → ℕ → ℝ
  | nd _ => fun _ => 0
  | decSub c => c.errorRate
  | decSuperIso _ _ => fun _ => 0
  | decSuperHilb _ => fun _ => 0

/-- The conditions under which the selected density applies, for one dynamics `(s, M, β⁻¹)` (`ν₀` for R3). -/
def HoldsAt : FieldDensityRd d s → ℝ → Matrix (Fin d) (Fin d) ℝ → ℝ → ℝ → Prop
  | nd Rg, s', M, invβ, ν₀ => max 0 ((d : ℝ) - 2) ≤ s' ∧ RdRegimeHolds Rg d s' M invβ ν₀
  | decSub _, s', _, _, _ => s' < (d : ℝ) - 2
  | decSuperIso m p, s', M, _, _ =>
      (d : ℝ) - 2 < s' ∧ 2 ≤ p ∧ (mStar d : ℝ) + d / p < m ∧ ∃ lam : ℝ, 0 < lam ∧ M = -(lam • 1)
  | decSuperHilb m, s', M, _, _ =>
      (d : ℝ) - 2 < s' ∧ (mStar d : ℝ) + d / 2 < m ∧
        ∃ lam : ℝ, 0 ≤ lam ∧ ∃ A : Matrix (Fin d) (Fin d) ℝ, A.transpose = -A ∧ M = -(lam • 1) + A

/-- The selected density applies to every `N ≥ 1` of the sequence. -/
def Holds (fd : FieldDensityRd d s) (S : WholeMainData d) (ν₀ : ℝ) : Prop :=
  ∀ N : ℕ, 1 ≤ N → fd.HoldsAt S.s S.M (S.invβ N) ν₀

end FieldDensityRd

/-- `η_{N,lin}^t` and the particle field: a random element `Ξ` of `H^{-Γ}(ℝ^d)` represents the particle field
`σ_NΞ_N^t = σ_N(μ_N^t - μ_{β_N}^t)` iff `⟨φ,Ξ⟩ = σ_N(μ_N^t(φ) - μ_{β_N}^t(φ))` a.s. for every smooth `φ ∈ H^Γ`
(these tests determine an element of `H^{-Γ}`; existence is part of the conclusions). -/
def IsFluctFieldRepr (S : WholeMainData d) (R : ∀ N, RealizationRd d N) (N Γ : ℕ) (t : ℝ)
    (Ξ : (R N).Ω → HNeg d (Γ : ℝ)) : Prop :=
  ∀ φ : Euc d → ℝ, IsSobolevTest (Γ : ℝ) φ → ∀ᵐ ζ ∂(R N).P,
    HNeg.pairing φ (Ξ ζ) = S.sigma N *
      (pair (empirical ((R N).X (Real.toNNReal t) ζ)) φ - pair (withDensityReal (S.ρ N t)) φ)

/-- The whole-space initial-field hypothesis `B:ass:init-field` (F-rd) (S L11439-11456), without the distance bound:
for `H = H^{-Γ}(ℝ^d)`, `Iemp N t` and `I N t` are `H`-valued random variables representing the functionals
`⟨φ, 𝓘_{N,emp}^t⟩ = A_N⟨U_N^{0,t}φ, κ_NΞ_N^0⟩ = A_Nκ_N(μ_N^0(U_N^{0,t}φ) - μ°(U_N^{0,t}φ))` and
`⟨φ, 𝓘_N^t⟩ = A_N⟨U_N^{0,t}φ, η°⟩` on the smooth tests `φ ∈ H^Γ` (`B:eq:transported-initial-rd`), with
`ε_N^f ↓ 0` (nonnegative, antitone, tending to `0`) and `sup_{N,t} E[‖𝓘_{N,emp}^t‖² + ‖𝓘_N^t‖²] ≤ C_in²`
(`lintegral` form).  The distance bound is `InitialFieldDist` (`d_{C²}`) or, in S.A.7, a `W₁`/`W₂` bound.
(The index `Γ` and the adjoint input are those of the selected density; the representation of an `H`-valued
random variable by its pairings with smooth tests follows `HRS/Whole/AppendixBField.lean`.) -/
structure TransportedInitialFieldRd (S : WholeMainData d) (R : ∀ N, RealizationRd d N) (Γ : ℕ)
    (Cin : ℝ) (εf : ℕ → ℝ) (Iemp I : ∀ N, ℝ → (R N).Ω → HNeg d (Γ : ℝ)) : Prop where
  meas : ∀ N : ℕ, 1 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) S.T, Measurable (Iemp N t) ∧ Measurable (I N t)
  repr_emp : ∀ N : ℕ, 1 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) S.T, ∀ φ : Euc d → ℝ,
    IsSobolevTest (Γ : ℝ) φ → ∀ᵐ ζ ∂(R N).P,
      HNeg.pairing φ (Iemp N t ζ) = S.AN N * (S.κ N *
        (pair (empirical ((R N).X₀ ζ)) (propagatorW (S.coeff N) 0 t φ) -
          pair S.μ0 (propagatorW (S.coeff N) 0 t φ)))
  repr : ∀ N : ℕ, 1 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) S.T, ∀ φ : Euc d → ℝ,
    IsSobolevTest (Γ : ℝ) φ → ∀ᵐ ζ ∂(R N).P,
      HNeg.pairing φ (I N t ζ) = S.AN N * (R N).η ζ (propagatorW (S.coeff N) 0 t φ)
  εf_nonneg : ∀ N : ℕ, 1 ≤ N → 0 ≤ εf N
  εf_anti : Antitone εf
  εf_tendsto : Tendsto εf atTop (𝓝 0)
  moment : ∀ N : ℕ, 1 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) S.T,
    ∫⁻ ζ, ‖Iemp N t ζ‖ₑ ^ 2 ∂(R N).P + ∫⁻ ζ, ‖I N t ζ‖ₑ ^ 2 ∂(R N).P ≤ ENNReal.ofReal (Cin ^ 2)

/-- The distance bound of (F-rd): `sup_{t≤T} d_{C²}(Law 𝓘_{N,emp}^t, Law 𝓘_N^t) ≤ ε_N^f`. -/
def InitialFieldDist (S : WholeMainData d) (R : ∀ N, RealizationRd d N) (Γ : ℕ) (εf : ℕ → ℝ)
    (Iemp I : ∀ N, ℝ → (R N).Ω → HNeg d (Γ : ℝ)) : Prop :=
  ∀ N : ℕ, 1 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) S.T,
    smoothDist 2 (law (R N).P (Iemp N t)) (law (R N).P (I N t)) ≤ εf N

/-- `G_N^t` of `B:eq:surrogate-field-rd` (S L9695-9696): a centered Gaussian law `νG` on `H^{-Γ}(ℝ^d)` with covariance
`B:eq:surrogate-cov` on `H^Γ` (`noiseCovW`), `q = σ_N²/(Nβ_N)`, constructed from the intrinsic kernel of S.A.20
(unique, S.B.7(ii)); statements are made for every such `νG`. -/
def IsLinearFieldNoiseRd (C : WholeCoeff d) (q t : ℝ) (Γ : ℕ) (νG : Measure (HNeg d (Γ : ℝ))) : Prop :=
  IsProbabilityMeasure νG ∧ IsCenteredGaussian νG ∧ ∀ φ ψ : Euc d → ℝ,
    IsSobolevTest (Γ : ℝ) φ → IsSobolevTest (Γ : ℝ) ψ →
      ∫ x, HNeg.pairing φ x * HNeg.pairing ψ x ∂νG = noiseCovW C q t t φ ψ

/-- The law of `η_{N,lin}^t = 𝓘_N^t + G_N^t` (`B:eq:surrogate-field-rd`, S L9693-9696), `𝓘_N^t` the transported
initial field (`I`, already containing `A_N`) and `G_N^t ∼ νG` independent of it: the convolution of the laws. -/
def linearFieldLawRd {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {Γ : ℕ}
    (I : Ω → HNeg d (Γ : ℝ)) (νG : Measure (HNeg d (Γ : ℝ))) : Measure (HNeg d (Γ : ℝ)) :=
  law P I ∗ νG

/-- The rate of `B:eq:field-rate-rd` (S L9941-9944): `ε^f + σ(𝔈 + e) + (σ²/(Nβ)) 𝔴` with `q = σ²/(Nβ)`. -/
def fieldRateRd (εf q σ w E e : ℝ) : ℝ := εf + σ * (E + e) + q * w

/-! ### The adjoint inputs of the field and path rows (decision M3) -/

end HRS.Whole.AppendixA

/-! Rename-free MOVE (decision M3, question Q2) of three assumption predicates from `AppendixALemmas.lean` and
`AppendixALemmas2.lean`: they keep their full names `HRS.Whole.AppendixALemmas.{AdjointInputOneD, AdjointDerivInput,
SelectedCommutatorInput}`, their statements and their docstrings, and are now defined before S.A.6 so that the statements
of S.A.6-S.A.11 can use them. -/
namespace HRS.Whole.AppendixALemmas

open HRS.Whole.AppendixA

variable {d : ℕ}

/-- The selected adjoint estimate with Sobolev embedding, as used in the first sentence of the proof
of `B:lem:adjoint-field-kernel` (S L10574-10575), for one coefficient `C`: for every `0 ≤ r ≤ t ≤ T` and every
smooth `φ ∈ H^Γ(ℝ^d)` the classical adjoint solution with terminal datum `φ` exists, `U^{r,t}φ ∈ C^j` and
`|∂^β U^{r,t}φ(x)| ≤ K ‖φ‖_{H^Γ}` for all `|β| ≤ j` and `x ∈ ℝ^d`, and `φ ↦ U^{r,t}φ` is linear on the test
class (`propagatorW` is a `choose`; this linearity is the uniqueness of the classical adjoint solution, as in
`AdjointInputOne` of `AppendixBField.lean`, which this strengthens by the order `j` and all `r`).  For the selected
field densities (nondecaying: `H^Γ ↪ H^{m_nd}_uloc ↪ C_b^{m_*}`; decaying: `H^Γ ↪ W^{m+2,p} ↪ C_b^{m_*}`) the
estimate holds with `j = m_*`; the density-specific adjoint theorems (S.A.12, S.A.16) are not re-stated. -/
def AdjointInputOneD (Γ : ℝ) (j : ℕ) (C : WholeCoeff d) (T K : ℝ) : Prop :=
  ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T → ∀ φ : Euc d → ℝ, IsSobolevTest Γ φ →
    (∃ f, IsClassicalAdjointW C t φ f) ∧ ContDiff ℝ j (propagatorW C r t φ) ∧
      (∀ φ₂ : Euc d → ℝ, IsSobolevTest Γ φ₂ → ∀ c : ℝ,
        propagatorW C r t (φ + c • φ₂) = propagatorW C r t φ + c • propagatorW C r t φ₂) ∧
      ∀ l ≤ j, ∀ i : Fin l → Fin d, ∀ x : Euc d,
        |partialDeriv i (propagatorW C r t φ) x| ≤ K * sobolevNorm Γ φ

/-- `AdjointInputOneD` for the family `(Cf N)_{N ≥ 1}`, with `K` independent of `N`. -/
def AdjointDerivInput (Γ : ℝ) (j : ℕ) (Cf : ℕ → WholeCoeff d) (T K : ℝ) : Prop :=
  ∀ N : ℕ, 1 ≤ N → AdjointInputOneD Γ j (Cf N) T K

/-- The selected commutator estimate along the adjoint orbit, for the whole-space field density of index `Γ` with
error `e_N` (S L10861-10870, proof L10873-10880: "the selected adjoint estimate controls the commutator norm
uniformly; the pathwise estimate used in the fixed-time field theorem"): for every `N ≥ 2`, pairwise distinct `X_N`,
`0 ≤ r ≤ t ≤ T`, smooth `φ ∈ H^Γ`,
`|Comm_N(M^*∇U_N^{r,t}φ; X_N, μ_{β_N}^r)| ≤ K ‖φ‖_{H^Γ}(F_N(X_N,μ^r) + o_N(Λ) + e_N)`
(`o_N(Λ) = HRS.oNΛ`).  It stands for the combination of the commutator estimates `B:prop:commutator`
(`HRS.Whole.commN`) and the selected adjoint estimate of the density `(𝒳, Γ, e_N)` (`fd.eN`); the
density-specific theorems (S.A.2-S.A.17, S.B.5) are not re-stated. -/
def SelectedCommutatorInput (S : WholeMainData d) (Γ : ℝ) (T K C₀ Λ : ℝ) (e : ℕ → ℝ) : Prop :=
  ∀ N : ℕ, 2 ≤ N → ∀ X : EucConfig d N, Function.Injective X → ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T →
    ∀ φ : Euc d → ℝ, IsSobolevTest Γ φ →
      |commN d S.s (fun x => Torus.matVec S.M.transpose (gradient (propagatorW (S.coeff N) r t φ) x)) X
          (withDensityReal (S.ρ N r))| ≤
        K * sobolevNorm Γ φ *
          (rieszModulatedEnergy d S.s X (withDensityReal (S.ρ N r)) + oNΛ d S.s C₀ Λ N + e N)

end HRS.Whole.AppendixALemmas

namespace HRS.Whole.AppendixA

variable {d : ℕ}

open HRS.Whole.AppendixALemmas (AdjointInputOneD AdjointDerivInput SelectedCommutatorInput)

/-- The selected-density clause of the field adjoint input: for `fd = decSub c` the fractional transport bound of the adjoint
orbit, in the exact shape consumed by S.B.5(ii),(iii) (`HasFracTransportBound c.regularity c.integrability` of
`v = Mᵀ∇U^{r,t}φ`, unfolded here because `HasFracTransportBound` (`AppendixBEnergy.lean`) is not in the import closure of this file; the
definition is `∃ L F, 0 ≤ F ∧ LipschitzWith L v ∧ (∃ w, (∀ i, IsFracDerivRep α (v · i) (w · i)) ∧ ‖|w|‖_{L^p} ≤ F) ∧ L + F ≤ K'`),
with `K' = K‖φ‖_{H^Γ}`, `Γ = Γ_𝔠`, for every smooth `φ ∈ H^Γ`, `N ≥ 1`, `0 ≤ r ≤ t ≤ T`.  This is the content of S.A.1 claim 2
(`commutatorNorm_le`: `‖Mᵀ∇f‖_𝔠 ≤ C‖f‖_{W^{m_𝔠,p_𝔠}}`) applied to `f = U^{r,t}φ` together with the S.A.16 bound
`‖U^{r,t}φ‖_{W^{m_𝔠,p_𝔠}} ≤ K‖φ‖_{H^Γ}` (the S.A.1 claim is stated for `C^∞` `f`; it extends to `W^{m_𝔠,p_𝔠} ∩ C²` by mollification: the Lipschitz constants and `L^p` norms of `|∇|^r(Mᵀ∇f_ε)` stay bounded, `∇f_ε → ∇f` locally uniformly, and `IsFracDerivRep` passes to the weak limit) (M3-FIX F2; before the fix the clause asked classical `C^{m_𝔠}` and `movWNormE`, which the
weak S.A.16 output does not give).  `True` for the other densities (`nd`: S.B.5(i) needs only the `C_b^{m_*}` bound of
`AdjointDerivInput`; `decSuperIso/Hilb`: likewise). -/
def FieldDensityRd.wInput {s : ℝ} (fd : FieldDensityRd d s) (S : WholeMainData d) (K : ℝ) : Prop :=
  match fd with
  | .decSub c => ∀ N : ℕ, 1 ≤ N → ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ S.T → ∀ φ : Euc d → ℝ,
      IsSobolevTest (c.gammaIndex : ℝ) φ →
      ∃ (L : ℝ≥0) (F : ℝ), 0 ≤ F ∧
        LipschitzWith L (fun x => Torus.matVec S.M.transpose (gradient (propagatorW (S.coeff N) r t φ) x)) ∧
        (∃ w : Euc d → Euc d, (∀ i, IsFracDerivRep c.regularity
            (fun x => Torus.matVec S.M.transpose (gradient (propagatorW (S.coeff N) r t φ) x) i) (fun x => w x i)) ∧
          eLpNorm (fun x => ‖w x‖) (ENNReal.ofReal c.integrability) volume ≤ ENNReal.ofReal F) ∧
        (L : ℝ) + F ≤ K * sobolevNorm (c.gammaIndex : ℝ) φ
  | .nd _ => True
  | .decSuperIso _ _ => True
  | .decSuperHilb _ => True

/-- Field-level adjoint input of the selected density `fd` for the particle coefficients `S.coeff N`, `N ≥ 1` (decision M3;
S.A.6, S.A.7, S.A.9, S.A.10, S.A.26): `AdjointDerivInput` at the index `Γ = fd.Gamma` through order `m_*` (the hypothesis of
S.A.20 `adjoint_field_kernel`: classical solutions, linearity on `IsSobolevTest Γ`, `|∂^βU^{r,t}φ| ≤ K‖φ‖_{H^Γ}`, `|β| ≤ m_*`), its
joint measurability clause (repair P9, the second hypothesis of S.A.20), and the density-specific clause `wInput`.
Honest scope (reviews R1, R2 of the first M3 draft): `deriv` and `wbound` are consequences of the adjoint theory (`nd`: S.A.12 at level
`m_nd`; `decSub`, `decSuperIso`, `decSuperHilb`: S.A.16 `adjoint_lp`, NOT S.A.12, which covers only the nondecaying density) plus
uniqueness of classical solutions to tie `propagatorW` to the constructed solution (F-CAU / S.A.33 in R1, R2a, R2c, R3; `propagatorW_unique_star`
in the corner `d-2 < s`, `SymNonpos M`; outside these nothing is claimed).  `meas` (joint measurability of the derivatives of the
`choose`-defined `propagatorW` in `(r,t,x)`, repair P9) is NOT derivable from S.A.12 / S.A.16: it is an EXTRA claim kept as a hypothesis
(as S.A.20 `adjoint_field_kernel` already takes it as a hypothesis). -/
structure FieldAdjointInputRd {s : ℝ} (fd : FieldDensityRd d s) (S : WholeMainData d) (K : ℝ) : Prop where
  deriv : AdjointDerivInput (fd.Gamma : ℝ) (mStar d) S.coeff S.T K
  meas : ∀ N : ℕ, 1 ≤ N → ∀ (j : Fin d) (φ : Euc d → ℝ), IsSobolevTest (fd.Gamma : ℝ) φ →
    Measurable (fun p : {p : ℝ × ℝ × Euc d // 0 ≤ p.1 ∧ p.1 ≤ p.2.1 ∧ p.2.1 ≤ S.T} =>
      partialDeriv (fun _ : Fin 1 => j) (propagatorW (S.coeff N) p.1.1 p.1.2.1 φ) p.1.2.2)
  wbound : fd.wInput S K

/-! ### Theorem S.A.6 -/

/-- Theorem S.A.6 `B:thm:main-rd-field` (S L9915-9949), the fluctuation field on `ℝ^d`.  Hypotheses:
`B:eq:initial-second-moment`, A.1, A.3, A.4 (with the empty finite family, since no finite family of tests occurs in
the conclusion), A.5 (F-rd, with its distance bound `InitialFieldDist`), A.6, and one selected density `fd`
(`FieldDensityRd.HoldsAt`: (a) uloc regime / (b) decaying sub-Coulomb / (c) decaying super-Coulomb).
"The mean-field regularity assumptions through the two-derivative level implicit in `Γ`" is read, as in
`HRS.Main.main_torus_field` (`r = γ+3`), as `r = Γ + 3` in A.3 and `m_V = Γ + 3` in `B:eq:V-assumption`.
Conclusion, for `t ∈ [0,T]`, `N ≥ C` and every Gaussian law `νG` of `G_N^t`: the particle field is a random element of
`H^{-Γ}` (`IsFluctFieldRepr`; existence is claimed) and for every representative
`d_{C²}(Law σ_NΞ_N^t, Law η_{N,lin}^t) ≤ C e^{Λ_T t}[ε_N^f + σ_N(𝔈_N + e_N) + (σ_N²/(Nβ_N))𝔴_N]`; moreover
`sup_N E‖σ_NΞ_N^t‖_{H^{-Γ}} < ∞`.  "The proof is intrinsic ... no plane wave" is prose.
AMBIGUITY: (1) the level `r`/`m_V` (above); (2) none further (`C, Λ_T` depend on `m20`, not on `m₂`, as in `main_rd_stat`).
Technical hypotheses: `m₂ ≥ 0` bounds the propagated second moment; measurability of the representatives.
Repair S.A.6 (2026-10-24, approved, review pending): the hypothesis `σ_N e_N → 0` (`Filter.Tendsto (fun N => S.sigma N * fd.eN N) atTop (𝓝 0)`) is added: for `fd = decSub (lower _)` the first-moment conclusion needs `σ_N(𝔈_N + e_N)` bounded (TeX remainder bound `E‖R‖ ≤ Cσ_N T(𝔈_N + e_N)`; S.A.25 `path_remainder_rd` takes it explicitly), which the other hypotheses give only for `σ_N𝔈_N` (the TeX remark `B:rem:density-tradeoff` already requires `σ_N e_N → 0` for the lower density).  `rd_field_wasserstein_one/_two` do not need it (`e_N` appears in their bounds).
M3: the extra hypothesis `FieldAdjointInputRd fd S Kad` (the selected adjoint estimate of the density: `AdjointDerivInput` at `Γ` through `m_*`, the measurability clause P9 of S.A.20, and for `decSub` the fractional transport bound of `Mᵀ∇U^{r,t}φ`), `Kad` an explicit argument as in `main_rd_stat`.  For `fd = nd` the content is S.A.12; for the decaying densities it is S.A.16 (`adjoint_lp`), so S.A.12 alone does not discharge it there; the measurability clause is an extra claim (see `FieldAdjointInputRd`). -/
theorem main_rd_field (s : ℝ) (fd : FieldDensityRd d s) (ν₀ MB Λ ΛV G₀ νbar T Cin m20 : ℝ)
    (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) (Kad : ℝ) :
    ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ →
    ∃ C ΛT : ℝ, 0 < C ∧ 0 < ΛT ∧
      ∀ (S : WholeMainData d), S.s = s → S.T = T → (∀ N, S.invβ N ≤ νbar) → fd.Holds S ν₀ →
      ∀ (R : ∀ N, RealizationRd d N) (𝔈 : ℕ → ℝ),
        RdStanding S R MB Λ ΛV G₀ m20 (fd.Gamma + 3) (fd.Gamma + 3) C₀ 𝔈 →
        FieldAdjointInputRd fd S Kad →
        Filter.Tendsto (fun N : ℕ => S.sigma N * fd.eN N) Filter.atTop (nhds 0) →
        ∀ m₂ : ℝ, 0 ≤ m₂ → PropagatedSecondMoment S R m₂ →
        ∀ (m₀ : ℕ) (ε : ℕ → ℝ), InitialFluctuationRd S R χ m₀ Cin ε (fun _ => ∅) →
        ∀ (εf : ℕ → ℝ) (Iemp I : ∀ N, ℝ → (R N).Ω → HNeg d (fd.Gamma : ℝ)),
          TransportedInitialFieldRd S R fd.Gamma Cin εf Iemp I →
          InitialFieldDist S R fd.Gamma εf Iemp I →
        ∀ t ∈ Set.Icc (0 : ℝ) T,
          (∀ N : ℕ, C ≤ (N : ℝ) →
            ∀ νG : Measure (HNeg d (fd.Gamma : ℝ)),
              IsLinearFieldNoiseRd (S.coeff N) (S.qN N) t fd.Gamma νG →
              (∃ Ξ : (R N).Ω → HNeg d (fd.Gamma : ℝ), Measurable Ξ ∧
                IsFluctFieldRepr S R N fd.Gamma t Ξ) ∧
              ∀ Ξ : (R N).Ω → HNeg d (fd.Gamma : ℝ), Measurable Ξ →
                IsFluctFieldRepr S R N fd.Gamma t Ξ →
                smoothDist 2 (law (R N).P Ξ) (linearFieldLawRd (R N).P (I N t) νG) ≤
                  C * Real.exp (ΛT * t) *
                    fieldRateRd (εf N) (S.qN N) (S.sigma N) (wN d N (𝔈 N) m₂) (𝔈 N) (fd.eN N)) ∧
          ∃ B : ℝ, ∀ N : ℕ, 1 ≤ N → ∀ Ξ : (R N).Ω → HNeg d (fd.Gamma : ℝ), Measurable Ξ →
            IsFluctFieldRepr S R N fd.Gamma t Ξ → ∫⁻ ζ, ‖Ξ ζ‖ₑ ∂(R N).P ≤ ENNReal.ofReal B := by
  sorry

/-! ### Corollary S.A.7 -/

/-- Corollary S.A.7 `B:cor:rd-field-wasserstein` (S L9951-9981), the `W₁` variant.  Under the hypotheses and the
selected density of `main_rd_field`, if the initial-field estimate (F-rd) is strengthened to
`sup_{t≤T} W₁(Law 𝓘_{N,emp}^t, Law 𝓘_N^t) ≤ ε_{N,1}^f` (`εf1`), then
`W₁(Law σ_NΞ_N^t, Law η_{N,lin}^t) ≤ C e^{Λ_T t}[ε_{N,1}^f + ((σ_N²/(Nβ_N))𝔴_N)^{1/2} + σ_N(𝔈_N + e_N)]`.
(`ε_N^f` of (F-rd) is kept for the representation/moment part of (F-rd), `ε_{N,1}^f` is any nonnegative sequence: the TeX only
asks the strengthened estimate, not monotonicity of `ε_{N,1}^f`.)
The last sentence ("in particular the i.i.d. whole-space initial coupling of `B:lem:iid-init-field-rd` yields a fully
quantitative `W₁` field theorem") is the instance with `εf1 = C A_N N^{-1/(4d+10)}(log N)^{1/(2d+5)}`, S.B.2 (stated
in `HRS/Whole/AppendixBField.lean`).
M3: the extra hypothesis `FieldAdjointInputRd fd S Kad`, as in `main_rd_field`. -/
theorem rd_field_wasserstein_one (s : ℝ) (fd : FieldDensityRd d s)
    (ν₀ MB Λ ΛV G₀ νbar T Cin m20 : ℝ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) (Kad : ℝ) :
    ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ →
    ∃ C ΛT : ℝ, 0 < C ∧ 0 < ΛT ∧
      ∀ (S : WholeMainData d), S.s = s → S.T = T → (∀ N, S.invβ N ≤ νbar) → fd.Holds S ν₀ →
      ∀ (R : ∀ N, RealizationRd d N) (𝔈 : ℕ → ℝ),
        RdStanding S R MB Λ ΛV G₀ m20 (fd.Gamma + 3) (fd.Gamma + 3) C₀ 𝔈 →
        FieldAdjointInputRd fd S Kad →
        ∀ m₂ : ℝ, 0 ≤ m₂ → PropagatedSecondMoment S R m₂ →
        ∀ (m₀ : ℕ) (ε : ℕ → ℝ), InitialFluctuationRd S R χ m₀ Cin ε (fun _ => ∅) →
        ∀ (εf : ℕ → ℝ) (Iemp I : ∀ N, ℝ → (R N).Ω → HNeg d (fd.Gamma : ℝ)),
          TransportedInitialFieldRd S R fd.Gamma Cin εf Iemp I →
        ∀ εf1 : ℕ → ℝ, (∀ N : ℕ, 1 ≤ N → 0 ≤ εf1 N) →
          (∀ N : ℕ, 1 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) S.T,
            wassersteinE 1 (law (R N).P (Iemp N t)) (law (R N).P (I N t)) ≤ ENNReal.ofReal (εf1 N)) →
        ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ N : ℕ, C ≤ (N : ℝ) →
          ∀ νG : Measure (HNeg d (fd.Gamma : ℝ)),
            IsLinearFieldNoiseRd (S.coeff N) (S.qN N) t fd.Gamma νG →
            ∀ Ξ : (R N).Ω → HNeg d (fd.Gamma : ℝ), Measurable Ξ →
              IsFluctFieldRepr S R N fd.Gamma t Ξ →
              wassersteinE 1 (law (R N).P Ξ) (linearFieldLawRd (R N).P (I N t) νG) ≤
                ENNReal.ofReal (C * Real.exp (ΛT * t) *
                  (εf1 N + Real.sqrt (S.qN N * wN d N (𝔈 N) m₂) + S.sigma N * (𝔈 N + fd.eN N))) := by
  sorry

/-- Corollary S.A.7 `B:cor:rd-field-wasserstein`, the `W₂` variant: if the initial-field estimate is strengthened to
`sup_{t≤T} W₂(Law 𝓘_{N,emp}^t, Law 𝓘_N^t) ≤ ε_{N,2}^f` and A.7 (`B:ass:MF2`, `EnergySmallness2Rd`) holds, then
`W₂(Law σ_NΞ_N^t, Law η_{N,lin}^t) ≤ C e^{Λ_T t}[ε_{N,2}^f + ((σ_N²/(Nβ_N))𝔴_N)^{1/2} + σ_N(𝔈'_N + e_N)]`
(`𝔴_N` still defined with `𝔈_N`).  A.7 is imposed with the empty finite family (its `(I1)` in `L²` is then vacuous).
M3: the extra hypothesis `FieldAdjointInputRd fd S Kad`, as in `main_rd_field`. -/
theorem rd_field_wasserstein_two (s : ℝ) (fd : FieldDensityRd d s)
    (ν₀ MB Λ ΛV G₀ νbar T Cin m20 : ℝ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) (Kad : ℝ) :
    ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ →
    ∃ C ΛT : ℝ, 0 < C ∧ 0 < ΛT ∧
      ∀ (S : WholeMainData d), S.s = s → S.T = T → (∀ N, S.invβ N ≤ νbar) → fd.Holds S ν₀ →
      ∀ (R : ∀ N, RealizationRd d N) (𝔈 : ℕ → ℝ),
        RdStanding S R MB Λ ΛV G₀ m20 (fd.Gamma + 3) (fd.Gamma + 3) C₀ 𝔈 →
        FieldAdjointInputRd fd S Kad →
        ∀ m₂ : ℝ, 0 ≤ m₂ → PropagatedSecondMoment S R m₂ →
        ∀ (m₀ : ℕ) (ε : ℕ → ℝ), InitialFluctuationRd S R χ m₀ Cin ε (fun _ => ∅) →
        ∀ (𝔈' ε2 : ℕ → ℝ), EnergySmallness2Rd S R C₀ Λ χ m₀ (fun _ => ∅) 𝔈' ε2 →
        ∀ (εf : ℕ → ℝ) (Iemp I : ∀ N, ℝ → (R N).Ω → HNeg d (fd.Gamma : ℝ)),
          TransportedInitialFieldRd S R fd.Gamma Cin εf Iemp I →
        ∀ εf2 : ℕ → ℝ, (∀ N : ℕ, 1 ≤ N → 0 ≤ εf2 N) →
          (∀ N : ℕ, 1 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) S.T,
            wassersteinE 2 (law (R N).P (Iemp N t)) (law (R N).P (I N t)) ≤ ENNReal.ofReal (εf2 N)) →
        ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ N : ℕ, C ≤ (N : ℝ) →
          ∀ νG : Measure (HNeg d (fd.Gamma : ℝ)),
            IsLinearFieldNoiseRd (S.coeff N) (S.qN N) t fd.Gamma νG →
            ∀ Ξ : (R N).Ω → HNeg d (fd.Gamma : ℝ), Measurable Ξ →
              IsFluctFieldRepr S R N fd.Gamma t Ξ →
              wassersteinE 2 (law (R N).P Ξ) (linearFieldLawRd (R N).P (I N t) νG) ≤
                ENNReal.ofReal (C * Real.exp (ΛT * t) *
                  (εf2 N + Real.sqrt (S.qN N * wN d N (𝔈 N) m₂) + S.sigma N * (𝔈' N + fd.eN N))) := by
  sorry


/-! ### The adjoint hypotheses, the limit coefficients and `Δ_N^{(m)}` -/

/-- The hypotheses of `B:thm:adjoint-rd` / `B:eq:coeff-hypothesis-rd` (S L10077-10084) for one `(D, μ)` at level `m`,
besides the regime: `D.s = s`, `0 ≤ s < d`; `|M_{ij}| ≤ MB`; `V` with `m_V = m+3` and `Λ_V, |∇V(0)|` bounds; `μ` is
`(m+3,Λ)`-regular on `[0,T]` (`CoeffHypRd`); `T > 0`; `ν = β⁻¹ ∈ [0, ν̄]`. (Whole-space analogue of
`HRS.PDE.AdjointData`; the regime is a separate hypothesis since the `W^{m,p}` regimes of `B:thm:adjoint-lp` are
not the regimes of A.2.) -/
structure AdjointRdData (s : ℝ) (m : ℕ) (MB Λ ΛV G₀ νbar : ℝ) (D : WholeDyn d) (T : ℝ)
    (μ : ℝ → Euc d → ℝ) : Prop where
  hs : D.s = s ∧ 0 ≤ s ∧ s < d
  hM : PDE.MatBound MB D.M
  hV : VHypRd (m + 3) ΛV G₀ D.V
  hμ : CoeffHypRd s m Λ T μ
  hT : 0 < T
  hν : 0 ≤ D.invβ ∧ D.invβ ≤ νbar

/-- The limiting coefficient quadruple `(β_∞, μ_{β_∞}, A, 2/β_*)` (M L10285-10290) on `ℝ^d`
(`invβ = β_∞⁻¹`, `invβstar = β_*⁻¹`). -/
structure LimitCoeffsRd (d : ℕ) where
  invβ : ℝ
  hinvβ : 0 ≤ invβ
  ρ : ℝ → Euc d → ℝ
  A : ℝ
  hA : 0 ≤ A
  invβstar : ℝ
  hinvβstar : 0 ≤ invβstar

/-- The limiting dynamics data. -/
def LimitCoeffsRd.dyn (L : LimitCoeffsRd d) (S : WholeMainData d) : WholeDyn d :=
  ⟨S.s, S.M, S.V, L.invβ⟩

/-- The coefficients of the limiting generator. -/
def LimitCoeffsRd.coeff (L : LimitCoeffsRd d) (S : WholeMainData d) : WholeCoeff d :=
  (L.dyn S).coeff L.ρ

open Classical in
/-- The coefficient norm `‖δμ‖_{𝒞^{m+2}} + ‖δμ‖_{𝒞^{m+2}_w}` of the stability estimates `B:eq:propagator-stability`,
`B:eq:adjoint-lp-stability` and of `B:eq:deltaN` on `ℝ^d` (S L10103, L10295): the `C_b^{m+2}` norm, the weighted
`C^{m+2}` norm `max_{j ≤ m+2}‖⟨x⟩^{d+3}∇^{⊗j}δμ‖_∞` of `S:eq:mf-regularity-whole`, and, when `d-1 ≤ s`, the additional
fractional-derivative bound `‖|∇|^{s-d}∇δμ‖_∞`; valued in `ℝ≥0∞` (`⊤` if some norm is infinite). -/
def coeffNormE (d : ℕ) (s : ℝ) (m : ℕ) (δ : Euc d → ℝ) : ℝ≥0∞ :=
  (if MemCb (m + 2) δ then ENNReal.ofReal (cbNorm (m + 2) δ) else ⊤) +
    weightedSupE (m + 2) ((d : ℝ) + 3) δ +
    (if (d : ℝ) - 1 ≤ s then ⨆ x, ENNReal.ofReal ‖fracForceRd d s δ x‖ else 0)

/-- The full coefficient discrepancy `Δ_N^{(m)}` of `B:eq:deltaN` (M L10412-10418) on `ℝ^d`:
`|β_N⁻¹ - β_∞⁻¹| + |2σ_N²/(Nβ_N) - 2/β_*| + |A_N - A| + sup_{r ≤ T}‖μ_{β_N}^r - μ_{β_∞}^r‖_{𝒞^{m+2}}`
with the coefficient norm `coeffNormE` (in `ℝ≥0∞`, so that unboundedness is `⊤`, not a junk `0`). -/
def coeffDiscrepancyRd (S : WholeMainData d) (L : LimitCoeffsRd d) (m N : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (|S.invβ N - L.invβ| + |2 * S.qN N - 2 * L.invβstar| + |S.AN N - L.A|) +
    ⨆ r : Set.Icc (0 : ℝ) S.T, coeffNormE d S.s m (S.ρ N r - L.ρ r)

/-- M3 stability input for the sequence `S.coeff N → L.coeff S` (decision M3; `ulocNormE` half of S.A.12(d) for the nondecaying density and S.A.16 stability for the decaying
densities, for the common regime and the same `(M, V)`, S L10103, L10295): for `N ≥ 1`, `0 ≤ r ≤ t ≤ T` and smooth `φ ∈ H^{Γq}`, the difference of the adjoint
propagators is in `C_b^j` and `‖(U_N^{r,t} - U_∞^{r,t})φ‖_{C_b^j} ≤ K‖φ‖_{H^{Γq}} Δ_N^{(m)}`, with `Δ_N^{(m)} = coeffDiscrepancyRd S L m N`
(valued in `ℝ≥0∞`, so `Δ_N = ⊤` makes the bound void; `K` absorbs `T e^{Λ_{m+2}T}` and the embedding into `C_b^j`).  M3-FIX F3: the classical adjoint solutions of BOTH coefficients exist (so
the difference of the two `choose`-defined `propagatorW` is not junk minus junk).  Uniqueness: `propagatorW` of both coefficients is tied to the constructed solutions by F-CAU / `propagatorW_unique_star` under `fd.HoldsAt` for `S.coeff N` and `L.coeff S`; nothing is claimed outside these regimes.  Used with
`(Γq, j, m) = (Γ+2, m₀+1, Γ)` (S.A.9, S.A.10, S.A.27) and `(Γ+2, m_*, Γ)` (S.A.26), `Γ = fd.Gamma`. -/
def AdjointStabilityInputRd (S : WholeMainData d) (L : LimitCoeffsRd d) (Γq j m : ℕ) (K : ℝ) : Prop :=
  ∀ N : ℕ, 1 ≤ N → ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ S.T → ∀ φ : Euc d → ℝ, IsSobolevTest (Γq : ℝ) φ →
    (∃ f, IsClassicalAdjointW (S.coeff N) t φ f) ∧ (∃ f, IsClassicalAdjointW (L.coeff S) t φ f) ∧
    MemCb j (fun x => propagatorW (S.coeff N) r t φ x - propagatorW (L.coeff S) r t φ x) ∧
    ENNReal.ofReal (cbNorm j (fun x => propagatorW (S.coeff N) r t φ x - propagatorW (L.coeff S) r t φ x)) ≤
      ENNReal.ofReal (K * sobolevNorm (Γq : ℝ) φ) * coeffDiscrepancyRd S L m N

/-- "Assume common adjoint regimes and constants and `Δ_N^{(m)} → 0`" (`B:cor:true-limit`, M L10420-10421) on `ℝ^d`:
the limit trajectory solves the whole-space mean-field equation with viscosity `β_∞⁻¹` and datum `μ°`, the adjoint
hypotheses (`AdjointRdData`, common `s, MB, Λ, Λ_V, |∇V(0)|, ν̄, T`, same `M, V`) hold at the level `lvl` for the limit
and for every `N ≥ 1`, and `Δ_N^{(m)} → 0`.  The common *regime* of the adjoint theory is a separate hypothesis of the
theorems (`FieldDensityRd.HoldsAt` for the limit). -/
structure CoeffConvergenceRd (S : WholeMainData d) (L : LimitCoeffsRd d) (MB Λ ΛV G₀ νbar : ℝ)
    (lvl m : ℕ) : Prop where
  limit_solution : IsWholeMeanFieldSolution (L.dyn S) S.T L.ρ
  limit_datum : withDensityReal (L.ρ 0) = S.μ0
  limit_adjoint : AdjointRdData S.s lvl MB Λ ΛV G₀ νbar (L.dyn S) S.T L.ρ
  seq_adjoint : ∀ N : ℕ, 1 ≤ N → AdjointRdData S.s lvl MB Λ ΛV G₀ νbar (S.dyn N) S.T (S.ρ N)
  tendsto : Tendsto (fun N => coeffDiscrepancyRd S L m N) atTop (𝓝 0)

/-! ### The path space `C([0,T]; H^{-Γ}(ℝ^d))` -/

/-- `C([0,T]; H^{-Γ}(ℝ^d))` with the sup norm (Mathlib's `ContinuousMap` norm on the compact `[0,T]`), as
`HRS.PathSpace` on the torus. -/
def HNegPath (d : ℕ) (Γ T : ℝ) : Type := C(Set.Icc (0 : ℝ) T, HNeg d Γ)

namespace HNegPath

variable {Γ T : ℝ}

instance : NormedAddCommGroup (HNegPath d Γ T) :=
  inferInstanceAs (NormedAddCommGroup C(Set.Icc (0 : ℝ) T, HNeg d Γ))

instance : NormedSpace ℝ (HNegPath d Γ T) :=
  inferInstanceAs (NormedSpace ℝ C(Set.Icc (0 : ℝ) T, HNeg d Γ))

instance : MeasurableSpace (HNegPath d Γ T) := borel _

instance : BorelSpace (HNegPath d Γ T) := ⟨rfl⟩

/-- Evaluation of a path at a time `t ∈ [0,T]`. -/
def at' (w : HNegPath d Γ T) (t : Set.Icc (0 : ℝ) T) : HNeg d Γ :=
  (show C(Set.Icc (0 : ℝ) T, HNeg d Γ) from w) t

end HNegPath

open Classical in
/-- A random path in `C([0,T]; H^{-Γ})` from a process `Y`, the zero path if `t ↦ Y^t(ζ)` is not continuous. -/
def toHNegPath {Ω : Type*} (Γ T : ℝ) (Y : ℝ → Ω → HNeg d Γ) (ζ : Ω) : HNegPath d Γ T :=
  if h : Continuous fun t : Set.Icc (0 : ℝ) T => Y t ζ then
    (⟨fun t => Y t ζ, h⟩ : C(Set.Icc (0 : ℝ) T, HNeg d Γ))
  else 0

/-- A random path `Ξ` in `C([0,T]; H^{-q}(ℝ^d))` represents the particle field path `t ↦ σ_NΞ_N^t`:
for every `t ∈ [0,T]` and smooth `φ ∈ H^q`, `⟨φ, Ξ^t⟩ = σ_N(μ_N^t(φ) - μ_{β_N}^t(φ))` a.s. -/
def IsFluctPathRepr (S : WholeMainData d) (R : ∀ N, RealizationRd d N) (N q : ℕ)
    (Ξ : (R N).Ω → HNegPath d (q : ℝ) S.T) : Prop :=
  ∀ t : Set.Icc (0 : ℝ) S.T, ∀ φ : Euc d → ℝ, IsSobolevTest (q : ℝ) φ → ∀ᵐ ζ ∂(R N).P,
    HNeg.pairing φ ((Ξ ζ).at' t) = S.sigma N *
      (pair (empirical ((R N).X (Real.toNNReal t.1) ζ)) φ - pair (withDensityReal (S.ρ N t.1)) φ)

/-! ### The duality identity on `ℝ^d` and Assumption S.A.8 -/

/-- `B_ψ(ρ_N,ρ_N)` for `ρ_N = μ_N - μ`, expanded bilinearly: `½∬_{x≠y}(∇ψ(x)-∇ψ(y))·M∇g(x-y) d(ρ_N)^{⊗2}`
(`HRS.flucInteraction` on `ℝ^d`). -/
def flucInteractionRd {N : ℕ} (D : WholeDyn d) (ψ : Euc d → ℝ) (X : EucConfig d N) (ρ : Euc d → ℝ) : ℝ :=
  interactionPairingW D ψ (empirical X) (empirical X)
  - interactionPairingW D ψ (empirical X) (withDensityReal ρ)
  - interactionPairingW D ψ (withDensityReal ρ) (empirical X)
  + interactionPairingW D ψ (withDensityReal ρ) (withDensityReal ρ)

/-- The finite-`N` adjoint-duality identity `B:eq:duality-identity` (M L1660-1670) for a time-dependent test
`f = (f^τ)_{τ ≤ t}` on `ℝ^d`, written for the particle flow `X` with Brownian filtration data `(ℱ, W')`:
a.s., for every `τ ∈ [0,t]`,
`⟨f^τ, ρ_N^τ⟩ = ⟨f^0, ρ_N^0⟩ + M_N^τ[f] + ∫_0^τ ½∬_{x≠y}(∇f^r(x) - ∇f^r(y))·M∇g(x-y) d(ρ_N^r)^{⊗2} dr`,
`ρ_N = μ_N - μ`, `M_N^τ[f] = (√(2/β_N)/N)∑_i∫_0^τ∇f^r(x_i^r)·dW_i^r` (`HRS.itoIntegral`, with `β_N⁻¹ = D.invβ`).

Statement repair MH-REPAIRS-2 (docs/ISSUES.md, 2026-10-19): `f` is constrained only on `[0,t]` (`IsClassicalAdjointW`), so the
Itô integrand is truncated to `[0,t]` (as `empiricalNoiseIntegrand` on the torus); without the truncation `itoIntegral` is the junk
value `0` whenever the values of `f` past `t` admit no continuous Itô integral, and the identity is false.  The conjunct
`IntegrableOn` of the interaction term is added as in the torus `duality_identity_all`. -/
def DualityIdentityRd {Ω : Type*} [mΩ : MeasurableSpace Ω] {N : ℕ} (P : Measure Ω)
    (ℱ : Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (D : WholeDyn d)
    (ρ : ℝ → Euc d → ℝ) (X : ℝ≥0 → Ω → EucConfig d N) (t : ℝ) (f : ℝ → Euc d → ℝ) : Prop :=
  ∀ᵐ ζ ∂P, ∀ τ ∈ Set.Icc (0 : ℝ) t,
    IntegrableOn (fun r => flucInteractionRd D (f r) (X (Real.toNNReal r) ζ) (ρ r)) (Set.Icc (0 : ℝ) τ) ∧
    pair (empirical (X (Real.toNNReal τ) ζ)) (f τ) - pair (withDensityReal (ρ τ)) (f τ) =
      (pair (empirical (X 0 ζ)) (f 0) - pair (withDensityReal (ρ 0)) (f 0)) +
      (Real.sqrt (2 * D.invβ) / N) *
        itoIntegral P ℱ W' (fun r ζ' ia => if r ∈ Set.Icc (0 : ℝ) t then
          gradComp ia.2 (f r) (X (Real.toNNReal r) ζ' ia.1) else 0) τ ζ +
      ∫ r in Set.Icc (0 : ℝ) τ, flucInteractionRd D (f r) (X (Real.toNNReal r) ζ) (ρ r)

/-- `U` is the weighted extension of the adjoint propagator of `C` (S.A.8, S L9987-10002): it agrees with `propagatorW`
whenever a classical adjoint solution exists, maps the `C^k` functions `h` with `‖h‖_{C_1^k} < ∞`
(`‖h‖_{C_1^k} = max_{|α|≤k} sup_x ⟨x⟩^{-1}|∂^αh(x)|`, `weightedSupE k (-1)`, `B:eq:weighted-Ck-path-definition`)
to `C^k` functions, `‖U^{r,u}h‖_{C_1^k} ≤ K e^{K(u-r)}‖h‖_{C_1^k}` for `0 ≤ r ≤ u ≤ T` (`B:eq:path-C1-propagation`), and
"the terminal-time evolution identity is valid in this weighted space" (S L10763-10768, used at L10782):
* the evolution property `U^{r,t} = U^{r,s}U^{s,t}` (`r ≤ s ≤ t`, for `C^k` functions `h` of finite weighted norm; `U^{s,t}h` is then again `C^k` of finite
  weighted norm by the bound), and
* the terminal-time identity `U^{s,t}φ - φ = ∫_s^t U^{s,τ}𝓛_τφ dτ` (`𝓛_τ = generatorW C τ`, pointwise in `x`, with an integrable
  integrand) for `0 ≤ s ≤ t ≤ T` and smooth `φ ∈ H^q` (`q = q_ℝ = Γ+2`) such that `𝓛_τφ` is `C^k` of finite weighted norm
  for `τ ∈ [s,t]` (the estimate `B:eq:path-generator-C1`, S L10772-10775, shows this is the case).

Statement repair MP-RD-REPAIRS (ISSUES.md): the inputs of `bound` and `evolution` and the generator in `terminal_identity` were `C^∞`;
the image `𝓛_τφ` is only `C^k` under `MeanFieldRegularityRd` (`C^{Γ+5}`), and S L10782 applies the bound to it. -/
structure IsWeightedExtension (C : WholeCoeff d) (k q : ℕ) (T K : ℝ)
    (U : ℝ → ℝ → (Euc d → ℝ) → (Euc d → ℝ)) : Prop where
  consistent : ∀ r u : ℝ, 0 ≤ r → r ≤ u → u ≤ T → ∀ h : Euc d → ℝ,
    (∃ f, IsClassicalAdjointW C u h f) → U r u h = propagatorW C r u h
  bound : ∀ r u : ℝ, 0 ≤ r → r ≤ u → u ≤ T → ∀ h : Euc d → ℝ, ContDiff ℝ k h →
    weightedSupE k (-1) h < ⊤ → ContDiff ℝ k (U r u h) ∧
      weightedSupE k (-1) (U r u h) ≤
        ENNReal.ofReal (K * Real.exp (K * (u - r))) * weightedSupE k (-1) h
  evolution : ∀ r s t : ℝ, 0 ≤ r → r ≤ s → s ≤ t → t ≤ T → ∀ h : Euc d → ℝ, ContDiff ℝ k h →
    weightedSupE k (-1) h < ⊤ → U r t h = U r s (U s t h)
  terminal_identity : ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T → ∀ φ : Euc d → ℝ, ContDiff ℝ ∞ φ →
    HRS.PDE.ToolboxRd.MemSobolev (q : ℝ) φ →
    (∀ τ ∈ Set.Icc s t, ContDiff ℝ k (generatorW C τ φ) ∧ weightedSupE k (-1) (generatorW C τ φ) < ⊤) →
    ∀ x : Euc d, IntegrableOn (fun τ => U s τ (generatorW C τ φ) x) (Set.Icc s t) ∧
      U s t φ x - φ x = ∫ τ in Set.Icc s t, U s τ (generatorW C τ φ) x

/-- Assumption S.A.8 `B:ass:rd-path-weighted` (S L9987-10002), weighted adjoint estimate for whole-space paths, for
the coefficients `S.coeff N` (`N ≥ 1`) and `Clim` (the limiting propagator), `k = m_0 + 1`, `q = q_ℝ` and a constant `K`
independent of `N`: the adjoint propagators, including the limiting one, extend consistently to the smooth functions with
finite `C_1^k` norm and satisfy `B:eq:path-C1-propagation`, the evolution property and the terminal-time evolution
identity (`IsWeightedExtension`). -/
structure WeightedPathInput (S : WholeMainData d) (Clim : WholeCoeff d) (k q : ℕ) (K : ℝ) : Prop where
  limit : ∃ U, IsWeightedExtension Clim k q S.T K U
  particles : ∀ N : ℕ, 1 ≤ N → ∃ U, IsWeightedExtension (S.coeff N) k q S.T K U

/-! ### Theorem S.A.9 and Corollary S.A.10 -/

/-- The fixed-time initial condition `B:eq:rd-path-initial-fixed-time` (S L10009-10013): for every `t ∈ [0,T]`, the
linear approximation transported initial fields converge, `𝓘_N^t ⟹ A(U_∞^{0,t})^*η°` in `H^{-(Γ+2)}(ℝ^d)`.
`𝓘_N^t` is any `H^{-(Γ+2)}`-valued representative of `φ ↦ A_Nη°(U_N^{0,t}φ)` and the limit any representative of
`φ ↦ Aη°(U_∞^{0,t}φ)` on a probability space carrying `η°` of the (common, fixed) law `νη` (smooth tests of
`H^{Γ+2}`).
Repair (2026-10-24, approved): `AEMeasurable η₀ P'` is added after `law P' η₀ = νη` (a non-a.e.-measurable `η₀` has a junk Dirac law). -/
def TransportedConvergesFixedTime (S : WholeMainData d) (R : ∀ N, RealizationRd d N)
    (L : LimitCoeffsRd d) (q : ℕ) : Prop :=
  ∀ t ∈ Set.Icc (0 : ℝ) S.T, ∀ νη : Measure ((Euc d → ℝ) → ℝ),
    (∀ N : ℕ, 1 ≤ N → law (R N).P (R N).η = νη) →
    ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
      (η₀ : Ω' → (Euc d → ℝ) → ℝ), law P' η₀ = νη → AEMeasurable η₀ P' →
    ∀ J : Ω' → HNeg d (q : ℝ), Measurable J →
      (∀ φ : Euc d → ℝ, IsSobolevTest (q : ℝ) φ → ∀ᵐ ζ ∂P',
        HNeg.pairing φ (J ζ) = L.A * η₀ ζ (propagatorW (L.coeff S) 0 t φ)) →
    ∀ I' : ∀ N, (R N).Ω → HNeg d (q : ℝ),
      (∀ N : ℕ, 1 ≤ N → Measurable (I' N) ∧ ∀ φ : Euc d → ℝ, IsSobolevTest (q : ℝ) φ →
        ∀ᵐ ζ ∂(R N).P, HNeg.pairing φ (I' N ζ) =
          S.AN N * (R N).η ζ (propagatorW (S.coeff N) 0 t φ)) →
      HRS.Main.ConvergesInLaw (fun N => law (R N).P (I' N)) (law P' J)

/-- The conclusion of `B:thm:main-rd-path` (S L10016-10019): `Ξ_N^t := σ_NΞ_N^t` has continuous paths in
`H^{-(Γ+2)}(ℝ^d)` (existence of a measurable path-valued representative `IsFluctPathRepr`), and for every
representatives `Ξ_N` and every continuous solution `Y` of the limit linear SPDE with the limiting coefficients
(`IsAdjointDualityLimitW`, S.B.7: initial functional `Aη°` with `η°` of the law `νη`, `q = β_*⁻¹`), the laws of `Ξ_N^·`
converge weakly to the law of `η^·` on `C([0,T]; H^{-(Γ+2)}(ℝ^d))`.
Technical hypotheses: `Ξ_N` measurable; the path map of the limit is a.e. measurable (a consequence of continuity of
the paths and measurability of the evaluations, needed so that the law is not a junk `0`).
Repair S.A.9 (2026-10-24, approved; same junk-Dirac repair as S.A.26 and S.B.7): `AEMeasurable η₀ P'` is added after
`law P' η₀ = νη`: `Measure.map` of a non-a.e.-measurable map is an arbitrary fixed Dirac mass (not `0`), so the law hypothesis does not
force `η₀` to be a.e.-measurable, and the identification of the limit law then has no proof. -/
def RdPathConclusion (S : WholeMainData d) (R : ∀ N, RealizationRd d N) (L : LimitCoeffsRd d)
    (q : ℕ) : Prop :=
  (∀ N : ℕ, 1 ≤ N → ∃ Ξ : (R N).Ω → HNegPath d (q : ℝ) S.T, Measurable Ξ ∧ IsFluctPathRepr S R N q Ξ) ∧
  ∀ νη : Measure ((Euc d → ℝ) → ℝ), (∀ N : ℕ, 1 ≤ N → law (R N).P (R N).η = νη) →
    ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
      (η₀ : Ω' → (Euc d → ℝ) → ℝ) (Y : ℝ → Ω' → HNeg d (q : ℝ)),
      law P' η₀ = νη → AEMeasurable η₀ P' →
      (∀ᵐ ζ ∂P', Continuous fun t : Set.Icc (0 : ℝ) S.T => Y t ζ) →
      AEMeasurable (toHNegPath (q : ℝ) S.T Y) P' →
      IsAdjointDualityLimitW P' (L.coeff S) (q : ℝ) L.A L.invβstar S.T η₀ Y →
      ∀ Ξ : ∀ N, (R N).Ω → HNegPath d (q : ℝ) S.T,
        (∀ N : ℕ, 1 ≤ N → Measurable (Ξ N) ∧ IsFluctPathRepr S R N q (Ξ N)) →
        HRS.Main.ConvergesInLaw (fun N => law (R N).P (Ξ N)) (law P' (toHNegPath (q : ℝ) S.T Y))

/-- The transported empirical initial vector `(⟨φ_a, 𝓘_{N,emp}^{t_a}⟩)_a = (A_N κ_N (μ_N^0(U_N^{0,t_a}φ_a) - μ°(U_N^{0,t_a}φ_a)))_a
= (σ_N⟨U_N^{0,t_a}φ_a, Ξ_N^0⟩)_a` converges in law, as `N → ∞`, to the vector `(A η°(U_∞^{0,t_a}φ_a))_a` of the limit, for every
random functional `η°` of the common law `νη` of the realizations (`B:eq:rd-path-initial-fixed-time` at several times at once).
Statement repair MP-RD-REPAIRS-4 (C)(a) (docs/ISSUES.md, 2026-10-19): the TeX proof of `B:thm:main-rd-path` applies
`B:lem:path-fidi` to arbitrary finite families of times, hence needs the family-dependent `B:ass:init` for every finite family; in Lean
`main_rd_path` assumed `B:ass:init` only for the empty family.  `TransportedConvergesFixedTime` controls single times only.
Repair (2026-10-24, approved): `AEMeasurable η₀ P'` is added after `law P' η₀ = νη` (a non-a.e.-measurable `η₀` has a junk Dirac law). -/
def EmpiricalInitialVectorConverges (S : WholeMainData d) (R : ∀ N, RealizationRd d N) (L : LimitCoeffsRd d)
    {p : ℕ} (ts : Fin p → ℝ) (φ : Fin p → Euc d → ℝ) : Prop :=
  ∀ νη : Measure ((Euc d → ℝ) → ℝ), (∀ N : ℕ, 1 ≤ N → law (R N).P (R N).η = νη) →
    ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
      (η₀ : Ω' → (Euc d → ℝ) → ℝ), law P' η₀ = νη → AEMeasurable η₀ P' →
      HRS.Main.ConvergesInLaw
        (fun N => law (R N).P (fun ζ => (WithLp.toLp 2 fun a => S.AN N * (S.κ N *
          (HRS.Whole.pair (HRS.Whole.empirical ((R N).X₀ ζ)) (propagatorW (S.coeff N) 0 (ts a) (φ a)) -
            HRS.Whole.pair S.μ0 (propagatorW (S.coeff N) 0 (ts a) (φ a)))) : EuclideanSpace ℝ (Fin p))))
        (law P' (fun ζ => (WithLp.toLp 2 fun a => L.A * η₀ ζ (propagatorW (L.coeff S) 0 (ts a) (φ a)) :
          EuclideanSpace ℝ (Fin p))))

/-- Theorem S.A.9 `B:thm:main-rd-path` (S L10004-10022), the qualitative path-space fluctuation field on `ℝ^d`.
Hypotheses: `B:ass:rd-path-weighted` (`WeightedPathInput`, `k = m_0+1`, `m_0` of A.4); the hypotheses of
`main_rd_field` for one selected density `(𝒳, Γ, e_N)` (`fd`), with `q_ℝ = Γ+2`, A.3 with `r = q_ℝ+3 = Γ+5` and
`B:eq:V-assumption` with `m_V = q_ℝ+3 = Γ+5`; the smallness `B:eq:rd-path-smallness`
`ε_N^f + σ_N(𝔈_N + e_N) + (σ_N²/(Nβ_N))𝔴_N → 0`; the coefficient convergence `Δ_N^{(Γ)} → 0` of `B:eq:deltaN`
(`CoeffConvergenceRd`, adjoint level `Γ+2`, `m = Γ`, with the selected regime also for the limit); and for every fixed
`t` the transported initial fields converge (`TransportedConvergesFixedTime`).  Conclusion `RdPathConclusion`.
"No dynamical second moment of the modulated energy is used" (no A.7).  The sentences "the fixed-time initial
condition follows from `B:cor:true-limit`; it is verified for i.i.d. data in `B:cor:iid-init-path-rd`" are remarks.
AMBIGUITY: (1) the weighted coefficient distance in `Δ_N^{(Γ)}` (see `coeffNormE`); (2) the level `m_V` for the
selected densities (as in `main_rd_field`); (3) `K` of `WeightedPathInput` is a free constant (the TeX: "a constant
independent of `N`").

Statement repair MP-RD-REPAIRS-4 (C)(a) (docs/ISSUES.md, 2026-10-19): the multi-time initial hypothesis
`EmpiricalInitialVectorConverges` for every finite family of times in `[0,T]` and Schwartz tests (the TeX proof applies
`B:lem:path-fidi` to arbitrary finite families, S L10897-10900, so `B:ass:init` is needed for every family, not only the empty one).
M3: the extra hypotheses (after `WeightedPathInput`; `Kad, Kadj, Kst` are explicit arguments, free constants of the hypotheses; the conclusion has no constant but `C₀min`, which may depend on them) are the field input `FieldAdjointInputRd fd S Kad`, the path-level adjoint input `AdjointDerivInput (Γ+2) (m₀+1) S.coeff` (the `adjoint` field of `PathAdjointInput`; its `weighted` field is the particle half of `WeightedPathInput`), the same for the limit (`AdjointInputOneD`) and the stability input `AdjointStabilityInputRd` (`C_b^{m₀+1}`, data `H^{Γ+2}`, `Δ_N^{(Γ)}`).  For the decaying densities (`decSub`, `decSuperIso`, `decSuperHilb`) these adjoint inputs are S.A.16 content, not S.A.12 (S.A.12 `adjoint_rd` covers the nondecaying density only). -/
theorem main_rd_path (s : ℝ) (fd : FieldDensityRd d s) (ν₀ MB Λ ΛV G₀ νbar T Cin m20 : ℝ)
    (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) (Kad Kadj Kst : ℝ) :
    ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ →
    ∀ (S : WholeMainData d), S.s = s → S.T = T → (∀ N, S.invβ N ≤ νbar) → fd.Holds S ν₀ →
    ∀ (R : ∀ N, RealizationRd d N) (𝔈 : ℕ → ℝ),
      RdStanding S R MB Λ ΛV G₀ m20 (fd.Gamma + 5) (fd.Gamma + 5) C₀ 𝔈 →
      ∀ m₂ : ℝ, 0 ≤ m₂ → PropagatedSecondMoment S R m₂ →
      ∀ (m₀ : ℕ) (ε : ℕ → ℝ), InitialFluctuationRd S R χ m₀ Cin ε (fun _ => ∅) →
      ∀ (εf : ℕ → ℝ) (Iemp I : ∀ N, ℝ → (R N).Ω → HNeg d (fd.Gamma : ℝ)),
        TransportedInitialFieldRd S R fd.Gamma Cin εf Iemp I →
        InitialFieldDist S R fd.Gamma εf Iemp I →
      ∀ L : LimitCoeffsRd d, fd.HoldsAt S.s S.M L.invβ ν₀ →
        CoeffConvergenceRd S L MB Λ ΛV G₀ νbar (fd.Gamma + 2) fd.Gamma →
      ∀ K : ℝ, WeightedPathInput S (L.coeff S) (m₀ + 1) (fd.Gamma + 2) K →
      FieldAdjointInputRd fd S Kad →
        AdjointDerivInput ((fd.Gamma + 2 : ℕ) : ℝ) (m₀ + 1) S.coeff S.T Kadj →
        AdjointInputOneD ((fd.Gamma + 2 : ℕ) : ℝ) (m₀ + 1) (L.coeff S) S.T Kadj →
        AdjointStabilityInputRd S L (fd.Gamma + 2) (m₀ + 1) fd.Gamma Kst →
      Tendsto (fun N => εf N + S.sigma N * (𝔈 N + fd.eN N) + S.qN N * wN d N (𝔈 N) m₂) atTop (𝓝 0) →
      TransportedConvergesFixedTime S R L (fd.Gamma + 2) →
      (∀ (p : ℕ) (ts : Fin p → ℝ) (φ : Fin p → Euc d → ℝ), (∀ a, ts a ∈ Set.Icc (0 : ℝ) T) →
        (∀ a, ∃ ψ : SchwartzMap (Euc d) ℝ, ⇑ψ = φ a) →
          EmpiricalInitialVectorConverges S R L ts φ) →
        RdPathConclusion S R L (fd.Gamma + 2) := by
  sorry

/-- The i.i.d. setting of `B:ex:iid` and `B:lem:iid-init-field-rd` (M L10468-10475, S L11169-11172): `X_N^0` has law
`(μ°)^{⊗N}`, `κ_N = √N`, `η°` is the centered Gaussian bridge of `μ°` (`IsGaussianBridgeW`), and
`m_2° = ∫|x|²dμ° < ∞`.
Repair (2026-10-24, approved): the field `kappa` holds for `N ≥ 1` only (`WholeMainData.hκ : 0 < κ N` contradicts `κ 0 = √0 = 0`).
Repair ED10 (2026-10-25, approved): field `eta_meas` (a non-a.e.-measurable `η` has a junk Dirac law). -/
structure IidSettingRd (S : WholeMainData d) (R : ∀ N, RealizationRd d N) : Prop where
  law_init : ∀ N : ℕ, 1 ≤ N → law (R N).P (R N).X₀ = Measure.pi (fun _ => S.μ0)
  kappa : ∀ N : ℕ, 1 ≤ N → S.κ N = Real.sqrt N
  bridge : ∀ N : ℕ, 1 ≤ N → IsGaussianBridgeW (R N).P S.μ0 (R N).η
  eta_meas : ∀ N : ℕ, 1 ≤ N → AEMeasurable (R N).η (R N).P
  second_moment : Integrable (fun x : Euc d => ‖x‖ ^ 2) S.μ0

/-- Corollary S.A.10 `B:cor:iid-path-rd` (S L10024-10026): in the i.i.d. setting, assume the hypotheses and the coefficient
convergence of `main_rd_path`; then the path convergence `B:eq:rd-path-convergence` holds for every selected whole-space
field density.  The fixed-time condition `B:eq:rd-path-initial-fixed-time` is *not* assumed: for i.i.d. data it is supplied
by `B:cor:iid-init-path-rd` (S.A.27, S L10903-10912, drafted elsewhere).
AMBIGUITY: "the hypotheses of `B:thm:main-rd-path`" read as all of them except the fixed-time condition, which the TeX says is
verified for i.i.d. data (S L10019-10021).
M3: the same extra hypotheses as `main_rd_path` (the fixed-time condition is still supplied by S.A.27). -/
theorem iid_path_rd (s : ℝ) (fd : FieldDensityRd d s) (ν₀ MB Λ ΛV G₀ νbar T Cin m20 : ℝ)
    (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) (Kad Kadj Kst : ℝ) :
    ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ →
    ∀ (S : WholeMainData d), S.s = s → S.T = T → (∀ N, S.invβ N ≤ νbar) → fd.Holds S ν₀ →
    ∀ (R : ∀ N, RealizationRd d N) (𝔈 : ℕ → ℝ), IidSettingRd S R →
      RdStanding S R MB Λ ΛV G₀ m20 (fd.Gamma + 5) (fd.Gamma + 5) C₀ 𝔈 →
      ∀ m₂ : ℝ, 0 ≤ m₂ → PropagatedSecondMoment S R m₂ →
      ∀ (m₀ : ℕ) (ε : ℕ → ℝ), InitialFluctuationRd S R χ m₀ Cin ε (fun _ => ∅) →
      ∀ (εf : ℕ → ℝ) (Iemp I : ∀ N, ℝ → (R N).Ω → HNeg d (fd.Gamma : ℝ)),
        TransportedInitialFieldRd S R fd.Gamma Cin εf Iemp I →
        InitialFieldDist S R fd.Gamma εf Iemp I →
      ∀ L : LimitCoeffsRd d, fd.HoldsAt S.s S.M L.invβ ν₀ →
        CoeffConvergenceRd S L MB Λ ΛV G₀ νbar (fd.Gamma + 2) fd.Gamma →
      ∀ K : ℝ, WeightedPathInput S (L.coeff S) (m₀ + 1) (fd.Gamma + 2) K →
      FieldAdjointInputRd fd S Kad →
        AdjointDerivInput ((fd.Gamma + 2 : ℕ) : ℝ) (m₀ + 1) S.coeff S.T Kadj →
        AdjointInputOneD ((fd.Gamma + 2 : ℕ) : ℝ) (m₀ + 1) (L.coeff S) S.T Kadj →
        AdjointStabilityInputRd S L (fd.Gamma + 2) (m₀ + 1) fd.Gamma Kst →
      Tendsto (fun N => εf N + S.sigma N * (𝔈 N + fd.eN N) + S.qN N * wN d N (𝔈 N) m₂) atTop (𝓝 0) →
        RdPathConclusion S R L (fd.Gamma + 2) := by
  sorry


/-! ### The Banach space `W^{-m,p'}(ℝ^d)` (the spaces `W^{m,p}(ℝ^d)` are defined before `AdjointInputRd`, M3) -/

/-- `W^{-m,p'}(ℝ^d) = (W^{m,p}(ℝ^d))^*`, `1/p + 1/p' = 1`, `p ∈ [2,∞)`, with the dual norm and its Borel
`σ`-algebra. -/
def WNeg (d m : ℕ) (p : ℝ) [Fact (2 ≤ p)] : Type := StrongDual ℝ (WmpSpace d m p)

namespace WNeg

variable {m : ℕ} {p : ℝ} [Fact (2 ≤ p)]

instance : NormedAddCommGroup (WNeg d m p) :=
  inferInstanceAs (NormedAddCommGroup (StrongDual ℝ (WmpSpace d m p)))

instance : NormedSpace ℝ (WNeg d m p) :=
  inferInstanceAs (NormedSpace ℝ (StrongDual ℝ (WmpSpace d m p)))

instance : MeasurableSpace (WNeg d m p) := borel _

instance : BorelSpace (WNeg d m p) := ⟨rfl⟩

/-- The value `⟨ξ, F⟩` of `ξ ∈ W^{-m,p'}` on `F ∈ W^{m,p}`. -/
def eval (ξ : WNeg d m p) (F : WmpSpace d m p) : ℝ := (show StrongDual ℝ (WmpSpace d m p) from ξ) F

end WNeg

/-- A random element `Ξ` of `W^{-m,p'}` represents the functional `φ ↦ a(φ)` on `C_c^∞` if `⟨Ξ, F⟩ = a(φ)` a.s. for every
`φ ∈ C_c^∞` and every `F ∈ W^{m,p}` whose class is the jet of `φ`. -/
def WNegRepr {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {m : ℕ} {p : ℝ} [Fact (2 ≤ p)]
    (Ξ : Ω → WNeg d m p) (a : (Euc d → ℝ) → Ω → ℝ) : Prop :=
  ∀ φ : Euc d → ℝ, IsCcInfty φ → ∀ F : WmpSpace d m p,
    ((F : WLp d m p) : Euc d → (WIndex d m → ℝ)) =ᵐ[volume] wJet m φ →
      ∀ᵐ ζ ∂P, (Ξ ζ).eval F = a φ ζ

/-! ### Corollary S.A.11 -/

/-- The parameters `(m, p)` of the test space `𝒳 = W^{m,p}` of a decaying selected density
(`decSub c`: `m_𝔠, p_𝔠`; `decSuperIso m p`; `decSuperHilb m`: `p = 2`); `none` for the uniformly local density. -/
def FieldDensityRd.wParams {s : ℝ} : FieldDensityRd d s → Option (ℕ × ℝ)
  | .nd _ => none
  | .decSub c => some (c.sobolevIndex, c.integrability)
  | .decSuperIso m p => some (m, p)
  | .decSuperHilb m => some (m, 2)

/-- The zero-temperature field coupling of `B:cor:zero-temp-decaying-field` (S L10030-10033): `W^{-m,p'}`-valued random
variables `Ξ0 N` (representing `κ_NΞ_N^0`: `φ ↦ κ_N(μ_N^0(φ) - μ°(φ))`) and `ηW N` (representing `η°`) with
`E‖κ_NΞ_N^0 - η°‖_{W^{-m,p'}} ≤ ε_{N,𝒳}^f` (`lintegral` form, `ε ≥ 0`). -/
structure ZeroTempCoupling (S : WholeMainData d) (R : ∀ N, RealizationRd d N) {m : ℕ} {p : ℝ}
    [Fact (2 ≤ p)] (εfX : ℕ → ℝ) (Ξ0 ηW : ∀ N, (R N).Ω → WNeg d m p) : Prop where
  meas : ∀ N : ℕ, 1 ≤ N → Measurable (Ξ0 N) ∧ Measurable (ηW N)
  repr_emp : ∀ N : ℕ, 1 ≤ N → WNegRepr (R N).P (Ξ0 N) fun φ ζ =>
    S.κ N * (pair (empirical ((R N).X₀ ζ)) φ - pair S.μ0 φ)
  repr_eta : ∀ N : ℕ, 1 ≤ N → WNegRepr (R N).P (ηW N) fun φ ζ => (R N).η ζ φ
  nonneg : ∀ N : ℕ, 1 ≤ N → 0 ≤ εfX N
  bound : ∀ N : ℕ, 1 ≤ N →
    ∫⁻ ζ, ‖Ξ0 N ζ - ηW N ζ‖ₑ ∂(R N).P ≤ ENNReal.ofReal (εfX N)

/-- A random element `Ξ` of `W^{-m,p'}` represents the particle field `σ_NΞ_N^t` (`WNegRepr` of
`φ ↦ σ_N(μ_N^t(φ) - μ_{β_N}^t(φ))`). -/
def IsFluctWRepr (S : WholeMainData d) (R : ∀ N, RealizationRd d N) (N m : ℕ) (p : ℝ) [Fact (2 ≤ p)]
    (t : ℝ) (Ξ : (R N).Ω → WNeg d m p) : Prop :=
  WNegRepr (R N).P Ξ fun φ ζ => S.sigma N *
    (pair (empirical ((R N).X (Real.toNNReal t) ζ)) φ - pair (withDensityReal (S.ρ N t)) φ)

/-- `Z` represents the transported linear approximation `Z_N^t = A_N(U_N^{0,t})^*η°` of the `W^{-m,p'}`-valued `η°` (`ηW`):
`⟨Z, F⟩ = A_N⟨η°, G⟩` a.s. for `φ ∈ C_c^∞` and `F, G ∈ W^{m,p}` the jets of `φ` and of `U_N^{0,t}φ`.
REPAIR (approved 2026-10-23, review R1 of the M3 draft): `G` is any element of `W^{m,p}` whose ZEROTH component is
`U_N^{0,t}φ` a.e. (`G (wZero d m) = propagatorW (S.coeff N) 0 t φ` a.e., the form of `wNormE`), i.e. `G` is the WEAK jet of
`U_N^{0,t}φ`; before the repair `G` had to equal the classical jet `wJet m (U_N^{0,t}φ)` a.e., which asks `C^m` regularity of the orbit that S.A.16
does not give (it gives the weak `W^{m,p}` bound and `C²`).  Such `G` is unique when it exists (the higher components are the weak derivatives of
the zeroth one), and exists iff `U_N^{0,t}φ ∈ W^{m,p}` (`wNormE < ⊤`), so the clause is neither vacuous nor ambiguous; where `U_N^{0,t}φ ∈ C^m`
the weak jet is the classical one. -/
def IsTransportedWRepr (S : WholeMainData d) (R : ∀ N, RealizationRd d N) (N m : ℕ) (p : ℝ)
    [Fact (2 ≤ p)] (t : ℝ) (ηW Z : (R N).Ω → WNeg d m p) : Prop :=
  ∀ φ : Euc d → ℝ, IsCcInfty φ → ∀ F G : WmpSpace d m p,
    ((F : WLp d m p) : Euc d → (WIndex d m → ℝ)) =ᵐ[volume] wJet m φ →
    (∀ᵐ x ∂(volume : Measure (Euc d)), ((G : WLp d m p) : Euc d → (WIndex d m → ℝ)) x (wZero d m) =
      propagatorW (S.coeff N) 0 t φ x) →
      ∀ᵐ ζ ∂(R N).P, (Z ζ).eval F = S.AN N * (ηW ζ).eval G

/-- Corollary S.A.11 `B:cor:zero-temp-decaying-field` (S L10028-10046), exact zero temperature in the Banach dual.
For a decaying selected density `𝒳 = W^{m,p}` (`fd.wParams = some (m,p)`), assume `β_N = ∞` for every `N`
(`invβ N = 0`; then `q_N = 0`, so the Gaussian block `G_N^t` vanishes) and a coupling `ZeroTempCoupling`.  Then the particle field `σ_NΞ_N^t` and `Z_N^t = A_N(U_N^{0,t})^*η°` are `W^{-m,p'}`-valued random variables (existence of
measurable representatives is asserted, as in the TeX: otherwise the laws are not defined) and, with
`Z_N^t = A_N(U_N^{0,t})^*η°` (the `W^{-m,p'}`-valued random variable representing
`φ ↦ A_Nη°(U_N^{0,t}φ)`: for `φ ∈ C_c^∞`, `F, G ∈ W^{m,p}` the weak jets of `φ`, `U_N^{0,t}φ`: the zeroth component of `G` is `U_N^{0,t}φ` a.e.),
`W₁(Law σ_NΞ_N^t, Law Z_N^t) ≤ C e^{Λ_T t}[ε_{N,𝒳}^f + σ_N(𝔈_N + e_N)]` as laws on `W^{-m,p'}(ℝ^d)`, for `t ∈ [0,T]`,
`N ≥ C`.  Hypotheses besides these: those of `main_rd_field` except (F-rd) (A.1, A.3 with `r = Γ+3`,
`m_V = Γ+3`, A.4 with the empty family, A.6, second moment, the selected density).
Technical hypotheses: measurability of the representatives `Ξ, Z`; the representation of `Z` is imposed only for
those `φ ∈ C_c^∞` for which `U_N^{0,t}φ` is the weak jet of an element `G` of `W^{m,p}` (true by S.A.16).
AMBIGUITY: `‖·‖_{W^{m,p}}` is the sup-norm-on-jets equivalent norm (`WmpSpace`), so the dual norm differs from the
TeX's by a constant factor absorbed into `C`.
M3: the extra hypothesis `AdjointInputRd (wClass m p) (wWeakClass m p) m_* (S.coeff N) T Kad` (S.A.16 `adjoint_lp` + `adjoint_lp_classical` content for the decaying density `W^{m,p}`, NOT S.A.12 content; classical tests in, weak `W^{m,p}` class out; `Kad` an explicit argument as in `main_rd_stat`).  The tie of `propagatorW` to the S.A.16 solution is as in `AdjointInputRd`. -/
theorem zero_temp_decaying_field (s : ℝ) (fd : FieldDensityRd d s) (m : ℕ) (p : ℝ) [Fact (2 ≤ p)]
    (hfd : fd.wParams = some (m, p)) (ν₀ MB Λ ΛV G₀ νbar T Cin m20 : ℝ) (χ : Euc d → ℝ)
    (hχ : IsUlocCutoff χ) (Kad : ℝ) :
    ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ →
    ∃ C ΛT : ℝ, 0 < C ∧ 0 < ΛT ∧
      ∀ (S : WholeMainData d), S.s = s → S.T = T → (∀ N, S.invβ N ≤ νbar) → fd.Holds S ν₀ →
      (∀ N, S.invβ N = 0) →
      ∀ (R : ∀ N, RealizationRd d N) (𝔈 : ℕ → ℝ),
        RdStanding S R MB Λ ΛV G₀ m20 (fd.Gamma + 3) (fd.Gamma + 3) C₀ 𝔈 →
        (∀ N : ℕ, 1 ≤ N → AdjointInputRd (wClass m p) (wWeakClass m p) (mStar d) (S.coeff N) S.T Kad) →
        ∀ m₂ : ℝ, 0 ≤ m₂ → PropagatedSecondMoment S R m₂ →
        ∀ (m₀ : ℕ) (ε : ℕ → ℝ), InitialFluctuationRd S R χ m₀ Cin ε (fun _ => ∅) →
        ∀ (εfX : ℕ → ℝ) (Ξ0 ηW : ∀ N, (R N).Ω → WNeg d m p), ZeroTempCoupling S R εfX Ξ0 ηW →
        ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ N : ℕ, C ≤ (N : ℝ) →
          (∃ Ξ : (R N).Ω → WNeg d m p, Measurable Ξ ∧ IsFluctWRepr S R N m p t Ξ) ∧
          (∃ Z : (R N).Ω → WNeg d m p, Measurable Z ∧ IsTransportedWRepr S R N m p t (ηW N) Z) ∧
          ∀ Ξ Z : (R N).Ω → WNeg d m p, Measurable Ξ → Measurable Z →
            IsFluctWRepr S R N m p t Ξ → IsTransportedWRepr S R N m p t (ηW N) Z →
            wassersteinE 1 (law (R N).P Ξ) (law (R N).P Z) ≤
              ENNReal.ofReal (C * Real.exp (ΛT * t) * (εfX N + S.sigma N * (𝔈 N + fd.eN N))) := by
  sorry

end HRS.Whole.AppendixA
