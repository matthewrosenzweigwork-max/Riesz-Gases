import HRS.Whole.Critical

/-!
# Weighted adjoint decay, chart localisation, and the noise couplings of the critical
stationary path estimate (spec packet SPEC-W3): Sections S8.3-S8.8

Source: HRS whole-space supplement (S), Section S8 (`S:sec:critical`).

* S8.3 `S:Q:lem:weighted-adjoint` (S lines 6439-6450): polynomially weighted adjoint decay and the
  pair inverse in the quadratic whole-space model.
* S8.4 `S:R:lem:charts` (S lines 6529-6541): charts adapted to the quadratic weight.
* S8.5 `S:R:lem:feature-decay` (S lines 6562-6574): spatial decay of the adjoint noise features.
* S8.6 `S:R:prop:finite-noise` (S lines 6598-6608): the finite-horizon noise coupling.
* S8.7 `S:R:lem:spectral` (S lines 6653-6670): a spectral space for the noise.
* S8.8 `S:R:lem:return-map` (S lines 6745-6756): return from the auxiliary space.

## Scope and representation decisions (common)

* **Model.** "The quadratic whole-space model" / "either stationary model" is, in every statement of
  this file, the critical (`s = d/2`) quadratic model of S8.1: `d ≥ 2`, `V = a|x|²/2`,
  `μ = μ_β` any `IsThermalEquilibrium d (d/2) a β ρβ`, `ν = β⁻¹`, particles stationary
  (`IsCanonicalRealization`).  The *torus* alternatives ("in either stationary model", S lines 6599,
  6653; "the same ... holds on the torus", S line 6563) are **not stated**: the periodic noise/orbit
  machinery (periodic `𝒦`-space, features, `A`, `L` on `𝕋^d`) has no Lean counterpart yet.
* `U_t = e^{t𝒜}` of S8.3 is the unique extension `U` of the semigroup of the projected generator
  `𝒜 = P_μ ℒ` (`IsWeightedSemigroup`, characterised on `C_c^∞` by the classical backward solution of
  `-∂_r u = 𝒜 u`, `projGeneratorW`).  Spatial gradients and zero-mass pairings do not see the
  additive constants that separate it from the classical adjoint solution of `ℒ`
  (`propagatorW`, `S:R:eq:backward-expression` S lines 6555-6559, 6552).
* The noise features `Γ_{r,a}(x) ∈ 𝒦_H = H¹([0,H];ℓ²) ⊕ ℓ²` are the existing `gradFeature`
  (Orbits.lean, S5.2); "adapted coupling" statements use the output pattern of
  `HRS.hilbert_polar_coupling` (Corollary A.23): `IsAdaptedGaussianCoupling` (a measure preserving
  enlargement `Ω' → Ω` with enlarged filtration, a cylindrical Brownian motion `B` independent of
  `ℱ₀`, both the empirical martingale `∫ S dB` and a deterministic-covariance Gaussian martingale
  `∫ Sb dB`).  The reconstruction `𝒯M` is `reconstructPath` (S5.2).
* `ℓ²`-valued objects are `OscDual d m` (coordinates indexed by `MultiIndex d`) for the Hermite
  features, and `SeqL2` (`ℓ²(ℕ)`) for the auxiliary space `ℋ_τ` (the coordinates
  `e^{-τω_ℓ/2} z(e_ℓ)`; the `ℋ_τ` norm is then the `ℓ²` norm).
* The linear-variance input `R:eq:linear-input` (M line 4187) is `LinearInputBounds`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole

variable {d : ℕ}

instance instSepSeqL2 : TopologicalSpace.SeparableSpace SeqL2 :=
  HRS.StaticLimitAux.separable_lp (ι := ℕ)

instance instSCSeqL2 : SecondCountableTopology SeqL2 :=
  UniformSpace.secondCountable_of_separable _

/-! ### Linear input and adapted couplings (shared definitions) -/

/-- The linear-variance input `R:eq:linear-input` (M line 4187, `S:R:prop:finite-noise` S line 6599)
for a configuration `Y` under `P` and the reference `μ`, with constant `C`: `dm_N/dμ ≤ C`,
`‖dm_N/dμ - 1‖_{L²(μ)} ≤ Cδ_N` (`HasMarginalDensityBounds`, `m_N` the law of the first
particle) and `Var[μ_N(f)] ≤ C N⁻¹ ‖f‖²_{L²(μ)}` (`ℝ≥0∞`-valued variance). -/
def LinearInputBounds (d : ℕ) (s : ℝ) (N : ℕ) (μ : Measure (Euc d)) (C : ℝ) {Ω : Type}
    [MeasurableSpace Ω] (P : Measure Ω) (Y : Ω → EucConfig d N) : Prop :=
  HasMarginalDensityBounds (firstMarginal (law P Y)) μ C (C * deltaN d s N) ∧
  ∀ f : Euc d → ℝ, MemLp f 2 μ →
    evariance (fun ζ => linStat f (Y ζ)) P ≤ ENNReal.ofReal (C / N * ∫ x, f x ^ 2 ∂μ)

/-- The data of an adapted coupling of an empirical `H`-valued martingale with a Gaussian martingale
of deterministic covariance, on a horizon `T` (the output pattern of `HRS.hilbert_polar_coupling`,
Corollary A.23, S lines 10631-10650): a measure preserving enlargement `π : Ω' → Ω` carrying a
filtration `ℱ'` that contains the pulled-back `ℱ`; an `H`-cylindrical Brownian motion `B` for `ℱ'`
independent of the (pulled-back) initial σ-field `ℱ₀`; the empirical martingale `M = ∫ Φ dW` is the
Itô integral `∫ S dB` of the square roots `S_r` of its covariance forms `Σ_r = ΦΦ*`; and the Gaussian
martingale `G = ∫ Sb dB` has deterministic covariance density `Cdet` (`Sb_r` the square roots). -/
structure IsAdaptedGaussianCoupling {Ω : Type} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    (ℱ : Filtration ℝ mΩ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    {κ : Type} (Φ : ℝ → Ω → κ → H) (M : ℝ → Ω → H) (T : ℝ)
    (Cdet : ℝ → H →L[ℝ] H →L[ℝ] ℝ) {Ω' : Type} {mΩ' : MeasurableSpace Ω'} (P' : Measure Ω')
    (π : Ω' → Ω) (ℱ' : Filtration ℝ mΩ') {ι : Type} [Countable ι] (e : HilbertBasis ι ℝ H)
    (B : ℝ≥0 → Ω' → ι → ℝ) (S : ℝ → Ω → H →L[ℝ] H) (Sb : ℝ → H →L[ℝ] H) (G : ℝ → Ω' → H) :
    Prop where
  prob : IsProbabilityMeasure P'
  preserving : MeasurePreserving π P' P
  filtration : ∀ τ, (ℱ τ).comap π ≤ ℱ' τ
  brownian : IsCylindricalBrownian P' ℱ' B
  indep : Indep ((ℱ 0).comap π) (cylindricalPathSigma B) P'
  sqrtS : ∀ r ∈ Set.Icc 0 T, ∀ z, IsSqrtOfForm (S r z) (hsCovForm (Φ r z))
  empirical : IsHilbertItoIntegral P' ℱ' B (fun r w j => if r ≤ T then S r (π w) (e j) else 0)
    (fun τ w => M (min τ T) (π w))
  sqrtSb : ∀ r ∈ Set.Icc 0 T, IsSqrtOfForm (Sb r) (Cdet r)
  gaussian : IsHilbertItoIntegral P' ℱ' B (fun r _ j => if r ≤ T then Sb r (e j) else 0) G

/-! ### S8.3 `S:Q:lem:weighted-adjoint` (S lines 6439-6450) -/

section WeightedAdjoint

/-- The space `C_M`: continuous `f` with `⟨x⟩^{-M} f(x) → 0` at infinity (S line 6439). -/
def MemCM (M : ℝ) (f : Euc d → ℝ) : Prop :=
  Continuous f ∧ Tendsto (fun x => f x / jbracket x ^ M) (cocompact (Euc d)) (𝓝 0)

/-- The space `C_M^j`: `C^j` functions all of whose partial derivatives of order `≤ j` satisfy
`⟨x⟩^{-M} ∂^α f(x) → 0` at infinity.  Its norm is `weightedSupE j (-M)`. -/
def MemCMj (M : ℝ) (j : ℕ) (f : Euc d → ℝ) : Prop :=
  ContDiff ℝ j f ∧ ∀ i ≤ j, ∀ idx : Fin i → Fin d,
    Tendsto (fun x => partialDeriv idx f x / jbracket x ^ M) (cocompact (Euc d)) (𝓝 0)

/-- The projected generator `𝒜 f = P_μ ℒ f = ℒ f - μ(ℒ f)` (`S:R:eq:backward-expression`; M line 4713:
`𝒜 f = P[Bf + Jf]`). -/
def projGeneratorW (C : WholeCoeff d) (μ : Measure (Euc d)) (r : ℝ) (g : Euc d → ℝ)
    (x : Euc d) : ℝ :=
  generatorW C r g x - ∫ y, generatorW C r g y ∂μ

/-- A classical backward solution `-∂_r f = G_r f`, `f(t) = φ`, for a general generator `G` (the same
conditions as the repaired `IsClassicalAdjointW`, whose generator is `generatorW C`; in particular `∂_r f` is only of linear growth, `|G_r f_r(x)| ≤ B(1+|x|)`). -/
structure IsAdjointSolutionG (G : ℝ → (Euc d → ℝ) → Euc d → ℝ) (t : ℝ) (φ : Euc d → ℝ)
    (f : ℝ → Euc d → ℝ) : Prop where
  c2 : ∀ r ∈ Set.Icc 0 t, ContDiff ℝ 2 (f r)
  bdd : ∀ j ≤ 2, ∃ B : ℝ, ∀ r ∈ Set.Icc 0 t, ∀ x, ‖iteratedFDeriv ℝ j (f r) x‖ ≤ B
  cont_c2 : ∀ j ≤ 2, Continuous fun p : Set.Icc (0 : ℝ) t × Euc d =>
    iteratedFDeriv ℝ j (f p.1) p.2
  terminal : f t = φ
  time_deriv : ∀ x : Euc d, ∀ r ∈ Set.Ioo 0 t, HasDerivAt (fun r' => f r' x) (-(G r (f r) x)) r
  cont_time_deriv : Continuous fun p : Set.Icc (0 : ℝ) t × Euc d => G p.1 (f p.1) p.2
  bdd_time_deriv : ∃ B : ℝ, ∀ r ∈ Set.Icc 0 t, ∀ x, |G r (f r) x| ≤ B * (1 + ‖x‖)

/-- `U` is the extension to `C_M` of the semigroup `U_t = e^{t𝒜}` of the projected generator of the
(time independent) coefficients `C` with invariant measure `μ` (S line 6440 "The semigroup extends to
`C_M`"): for `t ≥ 0`, `U_t` is a linear operator on `C_M` into `C_M`, bounded uniformly on bounded
time intervals, `U_0 = id`, `U_{t+s} = U_tU_s`, and on `C_c^∞` it is the classical backward solution
of `-∂_r u = 𝒜 u` with terminal datum `φ`, evaluated at `0` (this fixes it uniquely, `C_c` being
dense in `C_M`). -/
structure IsWeightedSemigroup (C : WholeCoeff d) (μ : Measure (Euc d)) (M : ℝ)
    (U : ℝ → (Euc d → ℝ) → Euc d → ℝ) : Prop where
  maps : ∀ t, 0 ≤ t → ∀ f, MemCM M f → MemCM M (U t f)
  add : ∀ t, 0 ≤ t → ∀ f g, MemCM M f → MemCM M g → U t (f + g) = U t f + U t g
  smul : ∀ t, 0 ≤ t → ∀ (c : ℝ) f, MemCM M f → U t (c • f) = c • U t f
  bdd : ∀ T, 0 ≤ T → ∃ K : ℝ, ∀ t ∈ Set.Icc 0 T, ∀ f, MemCM M f →
    weightedSupE 0 (-M) (U t f) ≤ ENNReal.ofReal K * weightedSupE 0 (-M) f
  zero : ∀ f, MemCM M f → U 0 f = f
  semigroup : ∀ t s, 0 ≤ t → 0 ≤ s → ∀ f, MemCM M f → U (t + s) f = U t (U s f)
  classical : ∀ t, 0 ≤ t → ∀ φ : Euc d → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
    ∃ f, IsAdjointSolutionG (projGeneratorW C μ) t φ f ∧ U t φ = f 0

/-- The weighted space of kernels `R(x,y)`: `C^j` in both variables with
`⟨x⟩^{-M}⟨y⟩^{-M} ‖D^iR(x,y)‖ → 0` at infinity of `ℝ^d × ℝ^d`, `i ≤ j` (weight `⟨x⟩^M⟨y⟩^M`,
derivatives in both variables). -/
def MemCMpair (M : ℝ) (j : ℕ) (R : Euc d → Euc d → ℝ) : Prop :=
  ContDiff ℝ j (Function.uncurry R) ∧ ∀ i ≤ j,
    Tendsto (fun z : Euc d × Euc d =>
      jbracket z.1 ^ (-M) * jbracket z.2 ^ (-M) * ‖iteratedFDeriv ℝ i (Function.uncurry R) z‖)
      (cocompact (Euc d × Euc d)) (𝓝 0)

/-- The norm `sup_{i≤j} sup_{x,y} ⟨x⟩^{-M}⟨y⟩^{-M}‖D^iR(x,y)‖` of `MemCMpair`, in `ℝ≥0∞`. -/
def pairNormE (M : ℝ) (j : ℕ) (R : Euc d → Euc d → ℝ) : ℝ≥0∞ :=
  ⨆ i : Fin (j + 1), ⨆ z : Euc d × Euc d,
    ENNReal.ofReal (jbracket z.1 ^ (-M) * jbracket z.2 ^ (-M) *
      ‖iteratedFDeriv ℝ i (Function.uncurry R) z‖)

/-- Doubly centered kernels: `∫R(x,y)dμ(x) = 0` for every `y` and `∫R(x,y)dμ(y) = 0` for every `x`
(`P_xP_yR = R`). -/
def IsDoublyCentered (μ : Measure (Euc d)) (R : Euc d → Euc d → ℝ) : Prop :=
  (∀ y, ∫ x, R x y ∂μ = 0) ∧ ∀ x, ∫ y, R x y ∂μ = 0

/-- The tensor semigroup `(U_t^xU_t^yR)(x,y) = (U_t[x' ↦ (U_tR(x',·))(y)])(x)`. -/
def tensorU (U : ℝ → (Euc d → ℝ) → Euc d → ℝ) (t : ℝ) (R : Euc d → Euc d → ℝ) (x y : Euc d) : ℝ :=
  U t (fun x' => U t (R x') y) x

/-- The pair inverse `Ψ_R(x,y) = ∫_0^∞ (U_t^xU_t^yR)(x,y) dt` (`S:Q:eq:smooth-pair-inverse`). -/
def pairInverseW (U : ℝ → (Euc d → ℝ) → Euc d → ℝ) (R : Euc d → Euc d → ℝ) (x y : Euc d) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ), tensorU U t R x y

/-- Lemma S8.3 (S:Q:lem:weighted-adjoint, TeX S L6439-6450) (S lines 6439-6450, `S:Q:eq:weighted-decay`,
`S:Q:eq:smooth-pair-inverse`), in the quadratic whole-space model (`d ≥ 2`, `s = d/2`, `V = a|x|²/2`,
`μ = μ_β`, `𝒜 = P_μℒ`, `ℒ = generatorW (critCoeff …)`), for every `M > 0`:
(1) the semigroup `U_t` extends to `C_M` (`IsWeightedSemigroup`); and for such an extension
(2) `‖U_tP‖_{C_M→C_M} ≤ Ce^{-ct}` and `‖U_tP‖_{C_M→C_M^j} ≤ C_je^{-ct}` for `t ≥ 1` (`C, c, C_j`
depend on `M`, and `j` for `C_j`), `P = P_μ` the centering; (3) `U_t` preserves `C_M^j` with bounded
norm on bounded time intervals; (4) the tensor semigroup on doubly centered kernels has the analogous
bounds with weight `⟨x⟩^M⟨y⟩^M` and derivatives in both variables (stated with a common rate `c` and
the same shape: `‖·‖_{M,0} ≤ Ce^{-ct}‖·‖_{M,0}`, `‖·‖_{M,j} ≤ C_je^{-ct}‖·‖_{M,0}`); (5) for a smooth
doubly centered kernel `R` of polynomial growth (`|D^kR(x,y)| ≤ C_k⟨x⟩^K⟨y⟩^K`, `K < M`) the pair
inverse converges for every `x, y`, is `C^j` with derivatives through order `j` bounded by `C⟨x⟩^M⟨y⟩^M`, and
satisfies `-(𝒜_x+𝒜_y)Ψ_R = R`.
AMBIGUITY: the source writes "(t ≥ 1)" after the display containing both inequalities of
`S:Q:eq:weighted-decay`; it is applied to both.  "Analogous bounds" for the tensor semigroup (4) is
read with the same exponential rate form; "every fixed number of weighted derivatives possessed by
`R`" (5) is read for each `j ≥ 2` with `R ∈ C^j`, weighted bounds through order `j`, and `Ψ_R ∈ C^j` (S8.2's proof, S L6334-6336, applies it to a remainder with only 8 derivatives; `j ≥ 2` is needed for `𝒜_x`, `𝒜_y`).  The statement is for the critical exponent `s = d/2` of
S8.1 (the model of this section; the proof uses only `s + 1 < d` for `d > 2` and the principal-value
reading at `d = 2`).  `ν = β⁻¹`. -/
theorem weighted_adjoint_decay (hd : 2 ≤ d) (a β : ℝ) (ha : 0 < a) (hβ : 0 < β)
    (ρβ : Euc d → ℝ) (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) (M : ℝ) (hM : 0 < M) :
    (∃ U, IsWeightedSemigroup (critCoeff d a β ρβ) (withDensityReal ρβ) M U) ∧
    ∀ U, IsWeightedSemigroup (critCoeff d a β ρβ) (withDensityReal ρβ) M U →
      (∃ Cd c : ℝ, 0 < c ∧ ∀ t : ℝ, 1 ≤ t → ∀ f, MemCM M f →
        weightedSupE 0 (-M) (U t (projMean (withDensityReal ρβ) f)) ≤
          ENNReal.ofReal (Cd * Real.exp (-c * t)) * weightedSupE 0 (-M) f) ∧
      (∀ j : ℕ, ∃ Cj c : ℝ, 0 < c ∧ ∀ t : ℝ, 1 ≤ t → ∀ f, MemCM M f →
        MemCMj M j (U t (projMean (withDensityReal ρβ) f)) ∧
        weightedSupE j (-M) (U t (projMean (withDensityReal ρβ) f)) ≤
          ENNReal.ofReal (Cj * Real.exp (-c * t)) * weightedSupE 0 (-M) f) ∧
      (∀ (j : ℕ) (T : ℝ), 0 ≤ T → ∃ K : ℝ, ∀ t ∈ Set.Icc 0 T, ∀ f, MemCMj M j f →
        MemCMj M j (U t f) ∧
        weightedSupE j (-M) (U t f) ≤ ENNReal.ofReal K * weightedSupE j (-M) f) ∧
      (∃ Cd c : ℝ, 0 < c ∧ ∀ t : ℝ, 1 ≤ t → ∀ R : Euc d → Euc d → ℝ, MemCMpair M 0 R →
        IsDoublyCentered (withDensityReal ρβ) R →
        pairNormE M 0 (tensorU U t R) ≤ ENNReal.ofReal (Cd * Real.exp (-c * t)) * pairNormE M 0 R) ∧
      (∀ j : ℕ, ∃ Cj c : ℝ, 0 < c ∧ ∀ t : ℝ, 1 ≤ t → ∀ R : Euc d → Euc d → ℝ, MemCMpair M 0 R →
        IsDoublyCentered (withDensityReal ρβ) R →
        MemCMpair M j (tensorU U t R) ∧
        pairNormE M j (tensorU U t R) ≤ ENNReal.ofReal (Cj * Real.exp (-c * t)) * pairNormE M 0 R) ∧
      ∀ j : ℕ, 2 ≤ j → ∀ R : Euc d → Euc d → ℝ, ContDiff ℝ j (Function.uncurry R) →
        IsDoublyCentered (withDensityReal ρβ) R →
        (∃ K : ℝ, K < M ∧ ∀ k : ℕ, k ≤ j → ∃ CR : ℝ, ∀ x y : Euc d,
          ‖iteratedFDeriv ℝ k (Function.uncurry R) (x, y)‖ ≤ CR * jbracket x ^ K * jbracket y ^ K) →
        (∀ x y, IntegrableOn (fun t => tensorU U t R x y) (Set.Ioi 0)) ∧
        ContDiff ℝ j (Function.uncurry (pairInverseW U R)) ∧
        (∀ k : ℕ, k ≤ j → ∃ CΨ : ℝ, ∀ x y : Euc d,
          ‖iteratedFDeriv ℝ k (Function.uncurry (pairInverseW U R)) (x, y)‖ ≤
            CΨ * jbracket x ^ M * jbracket y ^ M) ∧
        ∀ x y : Euc d,
          -(projGeneratorW (critCoeff d a β ρβ) (withDensityReal ρβ) 0
              (fun x' => pairInverseW U R x' y) x +
            projGeneratorW (critCoeff d a β ρβ) (withDensityReal ρβ) 0
              (pairInverseW U R x) y) = R x y := by
  sorry

end WeightedAdjoint

/-! ### S8.4 `S:R:lem:charts` (S lines 6529-6541) -/

section Charts

/-- The fixed chart cube `[-1/2,1/2]^d`. -/
def chartCube (d : ℕ) : Set (Euc d) := {u | ∀ i, |u i| ≤ 1 / 2}

/-- Lemma S8.4 (S:R:lem:charts, TeX S L6529-6541) (S lines 6529-6541, `S:R:eq:chart-properties`,
`S:R:eq:chart-count`): for a density with the Gaussian comparison
`c e^{-q|x|²/2} ≤ ρ(x) ≤ C e^{-q|x|²/2}`, `q > 0` (`S:R:eq:Gaussian-comparison`, S lines 6524-6527;
for the thermal density of S8.1 it is S3.4), there are countably many affine charts
`F_j(u) = x_j + A_ju` on the cube `Q = [-1/2,1/2]^d` and smooth `χ_j` with
`tsupport χ_j ⊂ F_j(int Q)` such that `∑_jχ_j² = 1`, `‖A_j‖ ≤ C_A`,
`c_A⟨x_j⟩⁻¹ ≤ |det A_j| ≤ C_A'⟨x_j⟩⁻¹`, `sup_u|∂^ℓ(χ_j∘F_j)| ≤ C_ℓ` (constants independent of `j`),
the images `F_j(Q)` have uniformly finite overlap, `c₁α_j ≤ ρ(F_j u)|det A_j| ≤ C₁α_j` on the whole
chart (`u ∈ Q`) with `α_j = ρ(x_j)|det A_j|`, and `∑_j⟨x_j⟩^{-2p} < ∞` for `2p > d+1`.
AMBIGUITY: "on a fixed cube" is not specified in the source (the unit cube with the origin at its
centre is used; a different fixed cube changes `A_j` by a fixed linear map).  The overlap is for
the images of `Q` itself ("uniformly finite", S line 6532; the proof also asserts it for enlarged
cubes).  The charts are allowed to depend on `ρ` only through the density comparison; constants are
chosen after `ρ`. -/
theorem adapted_charts (hd : 2 ≤ d) (q c C : ℝ) (hq : 0 < q) (hc : 0 < c)
    (ρ : Euc d → ℝ) (hρ : ∀ x, c * Real.exp (-q * ‖x‖ ^ 2 / 2) ≤ ρ x ∧
      ρ x ≤ C * Real.exp (-q * ‖x‖ ^ 2 / 2)) :
    ∃ (ι : Type) (_ : Countable ι) (xc : ι → Euc d) (A : ι → Euc d →L[ℝ] Euc d)
      (χ : ι → Euc d → ℝ),
      (∀ j, ContDiff ℝ ∞ (χ j) ∧
        tsupport (χ j) ⊆ (fun u => xc j + A j u) '' interior (chartCube d)) ∧
      (∀ x, Summable (fun j => χ j x ^ 2) ∧ ∑' j, χ j x ^ 2 = 1) ∧
      (∃ CA : ℝ, ∀ j, ‖A j‖ ≤ CA) ∧
      (∃ cdet Cdet : ℝ, 0 < cdet ∧ ∀ j,
        cdet * jbracket (xc j) ^ (-1 : ℝ) ≤ |LinearMap.det (A j : Euc d →ₗ[ℝ] Euc d)| ∧
        |LinearMap.det (A j : Euc d →ₗ[ℝ] Euc d)| ≤ Cdet * jbracket (xc j) ^ (-1 : ℝ)) ∧
      (∀ l : ℕ, ∃ Cl : ℝ, ∀ j (u : Euc d),
        ‖iteratedFDeriv ℝ l (fun u' => χ j (xc j + A j u')) u‖ ≤ Cl) ∧
      (∃ K : ℕ, ∀ x : Euc d,
        {j | x ∈ (fun u => xc j + A j u) '' chartCube d}.encard ≤ K) ∧
      (∃ c₁ C₁ : ℝ, 0 < c₁ ∧ ∀ j, ∀ u ∈ chartCube d,
        c₁ * (ρ (xc j) * |LinearMap.det (A j : Euc d →ₗ[ℝ] Euc d)|) ≤
          ρ (xc j + A j u) * |LinearMap.det (A j : Euc d →ₗ[ℝ] Euc d)| ∧
        ρ (xc j + A j u) * |LinearMap.det (A j : Euc d →ₗ[ℝ] Euc d)| ≤
          C₁ * (ρ (xc j) * |LinearMap.det (A j : Euc d →ₗ[ℝ] Euc d)|)) ∧
      ∀ p : ℝ, (d : ℝ) + 1 < 2 * p → Summable (fun j => jbracket (xc j) ^ (-(2 * p))) := by
  sorry

end Charts

/-! ### S8.5 `S:R:lem:feature-decay` (S lines 6562-6574) -/

section FeatureDecay

/-- The conditions under which the orbit feature `Γ_{r,·}(x)` of `orbitFeature` is genuinely an
element of `𝒦_T = H¹([0,T];ℓ²) ⊕ ℓ²` (no junk `0` from `ellVec` / `toLp`): the coordinates of
`D φ_α(x)` are in `ℓ²`, those of `D U(r,t) ℒ φ_α(x)` are in `ℓ²` for `r < t ≤ T`, and `t ↦ (…)_α` is
in `L²([0,T];ℓ²)`. -/
def IsKFeature (C : WholeCoeff d) (m T : ℝ) (Dop : (Euc d → ℝ) → Euc d → ℝ) (r : ℝ) (x : Euc d) :
    Prop :=
  Memℓp (fun α : MultiIndex d => Dop (oscTestFun m α) x) 2 ∧
  (∀ t ∈ Set.Ioc r T, Memℓp (fun α : MultiIndex d =>
    Dop (propagatorW C r t (generatorW C t (oscTestFun m α))) x) 2) ∧
  MemLp (fun t : ℝ => if r < t then ellVec (d := d) m (fun α => Dop
    (propagatorW C r t (generatorW C t (oscTestFun m α))) x) else 0) 2
    (volume.restrict (Set.Icc (0 : ℝ) T))

/-- Lemma S8.5 (S:R:lem:feature-decay, TeX S L6562-6574) (S lines 6562-6574, `S:R:eq:orbit-feature-new`,
`S:R:eq:weighted-feature`): in the quadratic whole-space model (`s = d/2`, `d ≥ 2`, `μ = μ_β`),
`m ≥ 24d + 240` (the Hermite features `φ_j = λ_j^{-m/2}h_j`), a finite horizon `H > 0`:
for `r ∈ [0,H]` and every gradient component `a`, the feature
`Γ_{r,a}(x) = ((t ↦ ∂_aU_{(t-r)_+}φ_j(x))_j, (∂_aφ_j(x))_j) ∈ 𝒦_H` (`gradFeature`) satisfies, for
`p = s + 2 = d/2 + 2` and every integer `0 ≤ ℓ ≤ d + 2`,
`sup_{r,x} ⟨x⟩^p ‖D_x^ℓ Γ_{r,a}(x)‖_{𝒦_H} ≤ C_H`.  `C_H` depends on `H` and the model parameters
(chosen before `ρβ`).  The classical adjoint evolutions of `φ_α` and `ℒφ_α` are asserted to exist
(so `propagatorW` is not junk), the feature is asserted to be a genuine element of `𝒦_H`
(`IsKFeature`) and `C^{d+2}` in `x`.  The torus assertion of the source (S line 6563, "the same
finite-horizon bounded feature assertion holds on the torus, without the spatial weight") is not
stated (no periodic `𝒦`-space). -/
theorem feature_decay (hd : 2 ≤ d) (a β : ℝ) (ha : 0 < a) (hβ : 0 < β) (m : ℝ)
    (hm : (wholeSpaceIndex d : ℝ) ≤ m) (Hz : ℝ) (hHz : 0 < Hz) :
    ∃ C : ℝ, ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ →
      (∀ α : MultiIndex d, ∀ t ∈ Set.Icc 0 Hz,
        (∃ f, IsClassicalAdjointW (critCoeff d a β ρβ) t (oscTestFun m α) f) ∧
        ∃ f, IsClassicalAdjointW (critCoeff d a β ρβ) t
          (generatorW (critCoeff d a β ρβ) t (oscTestFun m α)) f) ∧
      ∀ (i : Fin d), ∀ r ∈ Set.Icc 0 Hz,
        (∀ x, IsKFeature (critCoeff d a β ρβ) m Hz (gradComp i) r x) ∧
        ContDiff ℝ ((d + 2 : ℕ) : WithTop ℕ∞)
          (fun x => gradFeature (critCoeff d a β ρβ) m Hz i r x) ∧
        ∀ x : Euc d, ∀ l : ℕ, l ≤ d + 2 →
          jbracket x ^ ((d : ℝ) / 2 + 2) *
            ‖iteratedFDeriv ℝ l (fun y => gradFeature (critCoeff d a β ρβ) m Hz i r y) x‖ ≤ C := by
  sorry

end FeatureDecay

/-! ### S8.6 `S:R:prop:finite-noise` (S lines 6598-6608) -/

section FiniteNoise

/-- Proposition S8.6 (S:R:prop:finite-noise, TeX S L6598-6608) (S lines 6598-6608, `S:R:eq:finite-noise`): in the
stationary quadratic whole-space model (`s = d/2`, canonical stationary particles
`IsCanonicalRealization`, reference `μ = μ_β`), on a finite horizon `H > 0`, suppose the actual
time marginals satisfy the linear input `R:eq:linear-input` (`LinearInputBounds`, constant `C_in`).
Let `Φ_r(i,a) = √(2/(Nβ)) Γ_{r,a}(x_i^r)` (`gradFeature`, the `𝒦_H`-valued integrand of the empirical
noise, `W` an `(ℱ_t)`-Brownian motion, `X` progressive) and `M = ∫ Φ dW` its Itô integral.  There is
an adapted coupling (`IsAdaptedGaussianCoupling`: enlargement, cylindrical Brownian motion `B`
independent of `ℱ₀`, a Gaussian martingale `G = ∫ Sb dB` of deterministic covariance density
`2β⁻¹∑_a∫ Γ_{r,a}⊗Γ_{r,a} dμ` (`featureForm`; the "deterministic-intensity Gaussian noise", intensity
`μ`)) with
`(E sup_{t≤H} ‖𝒯M^t - 𝒯G^t‖²_{ℓ²})^{1/2} ≤ C_H(N^{-1/2} + δ_N)`, `𝒯` the reconstruction
`reconstructPath` (`S:R:eq:owning-maximal`, S5.2): `𝒯M^t` is the adjoint stochastic convolution of
the empirical noise and `𝒯G^t` that of the Gaussian noise.  `C_H` depends on `H`, the model and
`C_in` (quantified before the realization).  The integrand is asserted Hilbert-Schmidt
(`IsHSIntegrand`) and the bounded bilinear forms `Cdet_r` are asserted to exist (so the Itô integral
and the square roots are not vacuous).
Technical hypotheses: `N ≥ 2`; `X` progressive for `ℱ`; `W` cylindrical Brownian for `ℱ`.
Repair ED11 (2026-10-25, approved): the feature time is `max r 0` (for `r < 0` the adjoint propagator is an unconstrained choice; values for `r ≥ 0` are unchanged).
Not stated: the torus alternative (S line 6599 "in either stationary model", proof S line 6610). -/
theorem finite_noise (hd : 2 ≤ d) (a β : ℝ) (ha : 0 < a) (hβ : 0 < β) (m : ℝ)
    (hm : (wholeSpaceIndex d : ℝ) ≤ m) (Hz : ℝ) (hHz : 0 < Hz) (Cin : ℝ) :
    ∃ C : ℝ, ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ → ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N),
        IsCanonicalRealization d ((d : ℝ) / 2) a β N P X₀ W X →
      ∀ ℱ : Filtration ℝ mΩ,
        IsCylindricalBrownian P ℱ (fun t z (ia : Fin N × Fin d) => W t z ia.1 ia.2) →
        (∀ i : Fin N, IsProgressive ℱ (fun r z => X (Real.toNNReal r) z i)) →
        (∀ t ∈ Set.Icc (0 : ℝ) Hz, LinearInputBounds d ((d : ℝ) / 2) N (withDensityReal ρβ) Cin P
          (X (Real.toNNReal t))) →
        let Φ : ℝ → Ω → (Fin N × Fin d) → KSpace d m Hz := fun r z ia =>
          Real.sqrt (2 / (N * β)) •
            gradFeature (critCoeff d a β ρβ) m Hz ia.2 (max r 0) (X (Real.toNNReal r) z ia.1)
        IsHSIntegrand P ℱ Hz Φ ∧
        ∀ M : ℝ → Ω → KSpace d m Hz,
          IsHilbertItoIntegral P ℱ (fun t z (ia : Fin N × Fin d) => W t z ia.1 ia.2) Φ M →
          ∃ (Cdet : ℝ → KSpace d m Hz →L[ℝ] KSpace d m Hz →L[ℝ] ℝ),
            (∀ r ∈ Set.Icc 0 Hz, ∀ u v, Cdet r u v =
              featureForm m Hz β⁻¹ (fun i => gradFeature (critCoeff d a β ρβ) m Hz i r)
                (withDensityReal ρβ) u v) ∧
            ∃ (Ω' : Type) (mΩ' : MeasurableSpace Ω') (P' : Measure Ω') (π : Ω' → Ω)
              (ℱ' : Filtration ℝ mΩ') (ι : Type) (_ : Countable ι)
              (e : HilbertBasis ι ℝ (KSpace d m Hz)) (B : ℝ≥0 → Ω' → ι → ℝ)
              (S : ℝ → Ω → KSpace d m Hz →L[ℝ] KSpace d m Hz)
              (Sb : ℝ → KSpace d m Hz →L[ℝ] KSpace d m Hz) (G : ℝ → Ω' → KSpace d m Hz),
              IsAdaptedGaussianCoupling P ℱ Φ M Hz Cdet P' π ℱ' e B S Sb G ∧
              (∫⁻ w', (⨆ t : Set.Icc (0 : ℝ) Hz, ENNReal.ofReal
                  ‖reconstructPath m Hz (fun τ w => M τ (π w)) w' t -
                    reconstructPath m Hz G w' t‖) ^ 2 ∂P') ^ (1 / 2 : ℝ) ≤
                ENNReal.ofReal (C * ((N : ℝ) ^ (-(1 / 2 : ℝ)) + deltaN d ((d : ℝ) / 2) N)) := by
  sorry

end FiniteNoise

/-! ### S8.7 `S:R:lem:spectral` (S lines 6653-6670) -/

section Spectral

/-- `L e = -ρ⁻¹ div(ρ∇e) = -(Δe + ∇log ρ·∇e)` (S line 6668, `L = -ρ⁻¹Div(ρ∇)`; M line 4716),
for a positive smooth density `ρ`. -/
def weightedLaplacian (ρ : Euc d → ℝ) (e : Euc d → ℝ) (x : Euc d) : ℝ :=
  -(Laplacian.laplacian e x + inner ℝ (gradient (fun y => Real.log (ρ y)) x) (gradient e x))

/-- The spectral data `(e_ℓ, ω_ℓ)` of `S:R:eq:spectral-data` (S lines 6655-6660), for the critical
quadratic model with thermal density `ρβ`, `μ = ρβ dx`, `ν = β⁻¹`, `A = νI + K_μ` (on `L²_0(μ)`,
`A⁻¹ = β R_{β,μ}`; M line 4716 "`𝒜 = -AL` on centered `L²(μ)`"), `L = weightedLaplacian`:
`e_ℓ` smooth real centered eigenfunctions, `ω_ℓ > 0` increasing, `ALe_ℓ = ω_ℓe_ℓ`,
`⟨e_ℓ, A⁻¹e_j⟩ = δ_{ℓj}`, `∫∇e_ℓ·∇e_j dμ = ω_ℓδ_{ℓj}`, `ω_ℓ ≥ cℓ^{1/d}` (indices from `0`, so
`(ℓ+1)^{1/d}`).  Added well-definedness fields: the responses `A⁻¹e_j` exist, the gradient products
are `μ`-integrable, and (the proof's "orthonormal eigenbasis", S line 6676) the `e_ℓ` are complete in
`L²_0(μ)`: a centered `f ∈ L²(μ)` with `⟨f, A⁻¹e_ℓ⟩ = 0` for all `ℓ` vanishes. -/
structure IsSpectralData (d : ℕ) (β : ℝ) (ρβ : Euc d → ℝ) (e : ℕ → Euc d → ℝ) (om : ℕ → ℝ) :
    Prop where
  smooth : ∀ l, ContDiff ℝ ∞ (e l)
  centered : ∀ l, MemL2Zero (withDensityReal ρβ) (e l)
  pos : ∀ l, 0 < om l
  mono : Monotone om
  eigen : ∀ l, ∀ᵐ x ∂(withDensityReal ρβ),
    β⁻¹ * weightedLaplacian ρβ (e l) x +
      Kop (rieszKernel d ((d : ℝ) / 2)) (withDensityReal ρβ) (weightedLaplacian ρβ (e l)) x =
    om l * e l x
  response : ∀ l, ∃ h, IsResponse (rieszKernel d ((d : ℝ) / 2)) (withDensityReal ρβ) β (e l) h
  orth : ∀ l j, β * l2Inner (withDensityReal ρβ) (e l)
    (responseInverse (rieszKernel d ((d : ℝ) / 2)) (withDensityReal ρβ) β (e j)) =
      if l = j then 1 else 0
  grad_int : ∀ l j, Integrable (fun x => inner ℝ (gradient (e l) x) (gradient (e j) x))
    (withDensityReal ρβ)
  grad_orth : ∀ l j, ∫ x, inner ℝ (gradient (e l) x) (gradient (e j) x) ∂(withDensityReal ρβ) =
    if l = j then om l else 0
  growth : ∃ c : ℝ, 0 < c ∧ ∀ l : ℕ, c * ((l : ℝ) + 1) ^ (1 / (d : ℝ)) ≤ om l
  complete : ∀ f : Euc d → ℝ, MemL2Zero (withDensityReal ρβ) f →
    (∀ l, l2Inner (withDensityReal ρβ) f
      (responseInverse (rieszKernel d ((d : ℝ) / 2)) (withDensityReal ρβ) β (e l)) = 0) →
    f =ᵐ[withDensityReal ρβ] 0

/-- The diagonal semigroup `e^{-sω_ℓ}` on `ℓ²` (the convolution kernel `e^{-tω_ℓ}` of S line 6670). -/
def semiDiag (om : ℕ → ℝ) (s : ℝ) (z : SeqL2) : SeqL2 :=
  SeqL2.ofSeq fun l => Real.exp (-s * om l) * SeqL2.coord z l

/-- Lemma S8.7 (S:R:lem:spectral, TeX S L6653-6670) (S lines 6653-6670, `S:R:eq:spectral-data`,
`S:R:eq:spectral-L4`, `S:R:eq:aux-space`), whole-space critical quadratic model:
there are smooth real centered eigenfunctions `e_ℓ` and positive `ω_ℓ` with the properties of
`IsSpectralData`; for some fixed `t₀ > 0`, `‖∇e_ℓ‖_{L⁴(μ)} ≤ Ce^{t₀ω_ℓ}`; and for every
`τ > 4t₀` (so "choose `τ > 4t₀`") in the auxiliary Hilbert space `ℋ_τ`
(`‖z‖²_{ℋ_τ} = ∑_ℓ e^{-τω_ℓ}|z(e_ℓ)|²`, here the `ℓ²` norm of the coordinates `e^{-τω_ℓ/2}z(e_ℓ)`),
the empirical current `M = ∫ Φ dW`, `Φ_r(i,a) = √(2/(Nβ))(e^{-τω_ℓ/2}∂_ae_ℓ(x_i^r))_ℓ`, is coupled
(`IsAdaptedGaussianCoupling`, on every horizon `T`) to the Gaussian current `G = ∫ Sb dB` with the
deterministic diagonal covariance `b_ℓ = 2νω_ℓe^{-τω_ℓ}` (`S:R:eq:spectral-current`) such that the
expected difference trace `E‖S_r - Sb_r‖²_{HS}` is at most `C(N^{-1} + δ_N²)` for every `r ∈ [0,T]`
(uniformly in time: `C` independent of `T`), and the convolution `D(t) = ∫_0^t e^{-(t-r)ω}(S_r - Sb_r)dB_r`
of the difference with the diagonal semigroup has `E‖D(t)‖²_{ℋ_τ} ≤ C(N^{-1} + δ_N²)` at every
time `t ∈ [0,T]`, independently of the elapsed time.
The stationarity/linear-input facts used by the source (`R:eq:linear-input`) hold in this model by
S3 and are not hypotheses.  `C` depends on the model, `τ`; it is chosen before `N` and the
realization.  The coordinate sequences `(e^{-τω_ℓ/2}∂_ae_ℓ(x))_ℓ` are asserted in `ℓ²` for `μ`-a.e. `x`. The empirical integrand is asserted Hilbert-Schmidt (`IsHSIntegrand`) on every horizon
(so the Itô integral exists) and the bounded bilinear forms `Cdet_r` of the Gaussian current are
asserted to exist.
Technical hypotheses: `N ≥ 2`; `X` progressive and `W` Brownian for `ℱ`.  Not stated: the torus
alternative. -/
theorem spectral_space (hd : 2 ≤ d) (a β : ℝ) (ha : 0 < a) (hβ : 0 < β) (ρβ : Euc d → ℝ)
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) :
    ∃ (e : ℕ → Euc d → ℝ) (om : ℕ → ℝ), IsSpectralData d β ρβ e om ∧
    ∃ t₀ : ℝ, 0 < t₀ ∧
      (∃ C4 : ℝ, ∀ l, eLpNorm (fun x => ‖gradient (e l) x‖) 4 (withDensityReal ρβ) ≤
        ENNReal.ofReal (C4 * Real.exp (t₀ * om l))) ∧
      ∀ τ : ℝ, 4 * t₀ < τ → ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N),
        IsCanonicalRealization d ((d : ℝ) / 2) a β N P X₀ W X →
      ∀ ℱ : Filtration ℝ mΩ,
        IsCylindricalBrownian P ℱ (fun t z (ia : Fin N × Fin d) => W t z ia.1 ia.2) →
        (∀ i : Fin N, IsProgressive ℱ (fun r z => X (Real.toNNReal r) z i)) →
        let Φ : ℝ → Ω → (Fin N × Fin d) → SeqL2 := fun r z ia =>
          Real.sqrt (2 / (N * β)) • SeqL2.ofSeq (fun l =>
            Real.exp (-(τ * om l) / 2) * gradient (e l) (X (Real.toNNReal r) z ia.1) ia.2)
        (∀ᵐ x ∂(withDensityReal ρβ), ∀ i : Fin d, Memℓp (fun l => Real.exp (-(τ * om l) / 2) *
          gradient (e l) x i) 2) ∧
        (∀ T : ℝ, IsHSIntegrand P ℱ T Φ) ∧
        ∀ T : ℝ, 0 ≤ T → ∀ M : ℝ → Ω → SeqL2,
          IsHilbertItoIntegral P ℱ (fun t z (ia : Fin N × Fin d) => W t z ia.1 ia.2) Φ M →
          ∃ (Cdet : ℝ → SeqL2 →L[ℝ] SeqL2 →L[ℝ] ℝ),
            (∀ r ∈ Set.Icc 0 T, ∀ u v, Cdet r u v =
              ∑' l, 2 * β⁻¹ * om l * Real.exp (-τ * om l) * SeqL2.coord u l * SeqL2.coord v l) ∧
            ∃ (Ω' : Type) (mΩ' : MeasurableSpace Ω') (P' : Measure Ω') (π : Ω' → Ω)
              (ℱ' : Filtration ℝ mΩ') (ι : Type) (_ : Countable ι) (eb : HilbertBasis ι ℝ SeqL2)
              (B : ℝ≥0 → Ω' → ι → ℝ) (S : ℝ → Ω → SeqL2 →L[ℝ] SeqL2)
              (Sb : ℝ → SeqL2 →L[ℝ] SeqL2) (G : ℝ → Ω' → SeqL2),
              IsAdaptedGaussianCoupling P ℱ Φ M T Cdet P' π ℱ' eb B S Sb G ∧
              (∀ r ∈ Set.Icc 0 T, ∫⁻ w, ∑' j, ‖(S r (π w) - Sb r) (eb j)‖ₑ ^ 2 ∂P' ≤
                ENNReal.ofReal (C * ((N : ℝ)⁻¹ + deltaN d ((d : ℝ) / 2) N ^ 2))) ∧
              ∀ t ∈ Set.Icc 0 T, ∀ D : ℝ → Ω' → SeqL2,
                IsHilbertItoIntegral P' ℱ' B (fun r w j =>
                  if r ≤ t then semiDiag om (t - r) ((S r (π w) - Sb r) (eb j)) else 0) D →
                ∫⁻ w, ‖D t w‖ₑ ^ 2 ∂P' ≤
                  ENNReal.ofReal (C * ((N : ℝ)⁻¹ + deltaN d ((d : ℝ) / 2) N ^ 2)) := by
  sorry

end Spectral

/-! ### S8.8 `S:R:lem:return-map` (S lines 6745-6756) -/

section ReturnMap

/-- The return map `z ↦ (t ↦ (z(U_{b+t}φ_j))_j)` of `S:R:eq:return-map` (S lines 6745-6748), on the
auxiliary space `ℋ_τ` (coordinates `z'_ℓ = e^{-τω_ℓ/2}z(e_ℓ)`), made explicit by the spectral
expansion of the proof (S lines 6759-6761): `P_μφ_j = ∑_ℓ a_{jℓ}e_ℓ` with
`a_{jℓ} = ⟨P_μφ_j, A⁻¹e_ℓ⟩ = β⟨P_μφ_j, R_{β,μ}e_ℓ⟩`, and `U_te_ℓ = e^{-tω_ℓ}e_ℓ`
(`S:R:eq:spectral-semigroup`), so that
`z(U_{b+t}φ_j) = ∑_ℓ a_{jℓ} e^{-(b+t-τ/2)ω_ℓ} z'_ℓ`.  The `ℓ²` element is `ellVec` (indices `j ↔`
multi-indices `α`, `φ_α = oscTestFun m α`). -/
def returnMapW (d : ℕ) (β : ℝ) (ρβ : Euc d → ℝ) (e : ℕ → Euc d → ℝ) (om : ℕ → ℝ) (m τ b : ℝ)
    (z : SeqL2) (t : ℝ) : OscDual d m :=
  ellVec m fun α => ∑' l,
    (β * l2Inner (withDensityReal ρβ) (projMean (withDensityReal ρβ) (oscTestFun m α))
      (responseInverse (rieszKernel d ((d : ℝ) / 2)) (withDensityReal ρβ) β (e l))) *
    Real.exp (-(b + t - τ / 2) * om l) * SeqL2.coord z l

/-- Lemma S8.8 (S:R:lem:return-map, TeX S L6745-6756) (S lines 6745-6756), first assertion: with spectral data as in
S8.7 (`IsSpectralData`, `‖∇e_ℓ‖_{L⁴} ≤ Ce^{t₀ω_ℓ}`), `τ > 4t₀` and a fixed `b > τ/2 + 1`, the return
map is bounded from `ℋ_τ` into `𝒳_{m,T} = C([0,T]; B_m)`: for every `z ∈ ℋ_τ` the coordinate
series converge and define elements of `ℓ² = B_m`, the path is continuous on `[0,T]`, and
`sup_{t≤T} ‖returnMap z (t)‖_{B_m} ≤ C‖z‖_{ℋ_τ}`; `C` depends on the data, `m ≥ 24d+240`, `T`. -/
theorem return_map_bounded (hd : 2 ≤ d) (a β : ℝ) (ha : 0 < a) (hβ : 0 < β) (ρβ : Euc d → ℝ)
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) (e : ℕ → Euc d → ℝ) (om : ℕ → ℝ)
    (hdata : IsSpectralData d β ρβ e om) (t₀ : ℝ) (ht₀ : 0 < t₀) (C4 : ℝ)
    (hL4 : ∀ l, eLpNorm (fun x => ‖gradient (e l) x‖) 4 (withDensityReal ρβ) ≤
      ENNReal.ofReal (C4 * Real.exp (t₀ * om l)))
    (τ : ℝ) (hτ : 4 * t₀ < τ) (b : ℝ) (hb : τ / 2 + 1 < b) (m : ℝ)
    (hm : (wholeSpaceIndex d : ℝ) ≤ m) (T : ℝ) (hT : 0 < T) :
    ∃ C : ℝ, ∀ z : SeqL2,
      (∀ t ∈ Set.Icc 0 T, (∀ α : MultiIndex d, Summable fun l =>
          (β * l2Inner (withDensityReal ρβ) (projMean (withDensityReal ρβ) (oscTestFun m α))
            (responseInverse (rieszKernel d ((d : ℝ) / 2)) (withDensityReal ρβ) β (e l))) *
          Real.exp (-(b + t - τ / 2) * om l) * SeqL2.coord z l) ∧
        Memℓp (fun α : MultiIndex d => ∑' l,
          (β * l2Inner (withDensityReal ρβ) (projMean (withDensityReal ρβ) (oscTestFun m α))
            (responseInverse (rieszKernel d ((d : ℝ) / 2)) (withDensityReal ρβ) β (e l))) *
          Real.exp (-(b + t - τ / 2) * om l) * SeqL2.coord z l) 2) ∧
      ContinuousOn (fun t => returnMapW d β ρβ e om m τ b z t) (Set.Icc 0 T) ∧
      ∀ t ∈ Set.Icc 0 T, ‖returnMapW d β ρβ e om m τ b z t‖ ≤ C * ‖z‖ := by
  sorry

/-- A centered Gaussian random functional on bounded smooth test functions with covariance form `C₀`
(the stationary Gaussian initial field `Z⁰`, evaluated on adjoint orbits `U_{a+t}φ_j ∉ Σ^m`, see
`IsLinearFluctuationSolutionW`): each `η(f)` is measurable and for every finite family
`φ_1,…,φ_p ∈ C_b²` the vector `(η(φ_a))_a` is a centered Gaussian with covariance
`(C₀(φ_a,φ_b))_{ab}`. -/
def IsGaussianFunctionalW {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
    (η : Ω' → (Euc d → ℝ) → ℝ) (C₀ : (Euc d → ℝ) → (Euc d → ℝ) → ℝ) : Prop :=
  (∀ f, Measurable fun ζ => η ζ f) ∧
  ∀ (p : ℕ) (φ : Fin p → Euc d → ℝ), (∀ i, MemCb 2 (φ i)) →
    law P' (fun ζ => (WithLp.toLp 2 fun i => η ζ (φ i) : EuclideanSpace ℝ (Fin p))) =
      ProbabilityTheory.multivariateGaussian 0 (Matrix.of fun i j => C₀ (φ i) (φ j))

/-- Lemma S8.8 (S:R:lem:return-map, TeX S L6745-6756) (S lines 6745-6756), second assertion
`S:R:eq:initial-decay`: in the critical quadratic model, `m ≥ 24d+240`, `T > 0`: for stationary
initial fields with the variance bound `R:eq:linear-input` (`Var[μ_N⁰(f)] ≤ C_in N⁻¹‖f‖²_{L²(μ)}`, the
initial law being the canonical `P_{N,β}`, centering at its first marginal `m_N`), and for the
stationary Gaussian initial field (`IsGaussianFunctionalW`, covariance `⟨P_μφ, R_{β,μ}P_μψ⟩`),
`(E sup_{t≤T}∑_j|ζ_N⁰(U_{a+t}φ_j)|²)^{1/2} ≤ C_Te^{-ca}` and
`(E sup_{t≤T}∑_j|Z⁰(U_{a+t}φ_j)|²)^{1/2} ≤ C_Te^{-ca}` for `a ≥ 1`
(the Gaussian clause takes the supremum over RATIONAL times `t ∈ [0,T]`, with no continuity hypothesis (repair P6, 2026-10-20): finite-dimensional laws alone do not control the supremum over uncountably many `t` (`η` could be altered on a null set depending on `t`), the countable supremum of measurable functions is the process bound and equals the supremum over `[0,T]` for any version continuous along the adjoint orbits `t ↦ Z⁰(U_{a+t}φ_j)`. The source states the sum of the two; separate bounds with the same constant are equivalent up to
the factor `2`).  `ζ_N⁰ = √N(μ_N⁰ - m_N)`; `U_{a+t}φ_j` is the classical adjoint orbit (`propagatorW`
of the unprojected generator; it differs from the projected-semigroup orbit by a constant, which
`ζ_N⁰` and `Z⁰` (zero mass) do not see); existence of the adjoint orbits is asserted.  `C_T, c`
depend on the model, `T` and `C_in`, chosen before `a`, `N` and the fields. -/
theorem return_map_initial_decay (hd : 2 ≤ d) (a β : ℝ) (ha : 0 < a) (hβ : 0 < β) (m : ℝ)
    (hm : (wholeSpaceIndex d : ℝ) ≤ m) (T : ℝ) (hT : 0 < T) (Cin : ℝ) :
    ∃ CT c : ℝ, 0 < c ∧ ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ →
      (∀ α : MultiIndex d, ∀ t : ℝ, 0 ≤ t →
        ∃ f, IsClassicalAdjointW (critCoeff d a β ρβ) t (oscTestFun m α) f) ∧
      ∀ a₁ : ℝ, 1 ≤ a₁ →
        (∀ N : ℕ, 2 ≤ N → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
          [IsProbabilityMeasure P] (X₀ : Ω → EucConfig d N),
          law P X₀ = canonicalGibbs (rieszKernel d ((d : ℝ) / 2)) (confinement a) N β →
          (∀ f : Euc d → ℝ, MemLp f 2 (withDensityReal ρβ) →
            evariance (fun ζ => linStat f (X₀ ζ)) P ≤
              ENNReal.ofReal (Cin / N * ∫ x, f x ^ 2 ∂(withDensityReal ρβ))) →
          (∫⁻ ζ, (⨆ t : Set.Icc (0 : ℝ) T, l2NormE (fun α : MultiIndex d =>
              Real.sqrt N * (pair (empirical (X₀ ζ))
                  (propagatorW (critCoeff d a β ρβ) 0 (a₁ + t) (oscTestFun m α)) -
                ∫ x, propagatorW (critCoeff d a β ρβ) 0 (a₁ + t) (oscTestFun m α) x
                  ∂(firstMarginal (law P X₀))))) ^ 2 ∂P) ^ (1 / 2 : ℝ) ≤
            ENNReal.ofReal (CT * Real.exp (-c * a₁))) ∧
        ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
          (η : Ω' → (Euc d → ℝ) → ℝ),
          IsGaussianFunctionalW P' η
            (susceptibilityCov (rieszKernel d ((d : ℝ) / 2)) (withDensityReal ρβ) β) →
          (∫⁻ ζ', (⨆ t : {t : ℝ // t ∈ Set.Icc (0 : ℝ) T ∧ ∃ q : ℚ, (q : ℝ) = t},
              l2NormE (fun α : MultiIndex d =>
              η ζ' (propagatorW (critCoeff d a β ρβ) 0 (a₁ + t.1) (oscTestFun m α)))) ^ 2 ∂P') ^
              (1 / 2 : ℝ) ≤
            ENNReal.ofReal (CT * Real.exp (-c * a₁)) := by
  sorry

end ReturnMap

end HRS.Whole
