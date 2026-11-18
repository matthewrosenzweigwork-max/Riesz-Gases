import HRS.Main.Headline
import HRS.Main.Q42Aux1

/-!
# Section 2 of the main manuscript: the first non-Gaussian correction on observation windows
(headline results and prose claims, part 3)

Specification file SPEC-2 (statements with `sorry` proofs; definitions contain no `sorry`).
Source: `HRS_periodic_main_20261008T010000Z.tex` ("M"), Section 2, lines 1242-1420.

Rows covered: `M:prose:L1242-1272`, `M:H:thm:edgeworth` (2.13), `M:prose:L1290-1331`,
`M:H:cor:stationary-correction` (2.14), `M:prose:L1362-1395`, `M:prose:L1396-1420`.

## Representation decisions

* **Projective tensors** (TeX L1267-1271): `B ⊗̂_π B ⊗̂_π B` is `HRS.projTensor B 3`, the closure of the
  span of the elementary tensors in the dual `TensorDual B 3` of the bounded trilinear forms (this is
  isometric to the projective tensor product, see `HRS/Prob/Gaussian.lean`); the projective norm
  `‖·‖_π` is its norm, the pairing `⟨D³Φ(z), 𝒦⟩` is `𝒦 (D³Φ(z))` with `D³Φ(z) =
  iteratedFDeriv ℝ 3 Φ z`.  "Symmetric" means invariance under `domDomCongr σ`, `σ ∈ S₃`.
* **The second-moment tensor** `C_{a,T} = E[Z^{a+·} ⊗ Z^{a+·}]` is not constructed as an element of
  `projTensor B 2` (that needs a Bochner-integrability argument in the dual); its projective distance
  to `C_{∞,T}` is expressed through the dual formula
  `‖C_{a,T} - C_{∞,T}‖_π = sup_{‖M‖≤1} |E M(Z^{a+·},Z^{a+·}) - E M(Z_{β,T},Z_{β,T})|` over bounded
  bilinear forms `M` (the norm of the Bochner tensor in `(B ⊗̂_π B)* = B[×2]→L ℝ`).
* **The cubic tensor** `𝒦_{a,T}` is specified (TeX L1287, L1303-1312) by its evaluations
  `κ_{ijk}` (`cubicKappa`) on the trilinear forms `(w₁,w₂,w₃) ↦ ℓ_i(w₁)ℓ_j(w₂)ℓ_k(w₃)`, with
  `ℓ_i w = ⟨w^{t_i - a}, φ_i⟩` the observations at times `t_i ∈ [a,a+T]` (`pathEval`); the smooth
  signed densities `χ_i^r` of `H:eq:cross-covariance-density` are quantified in the premise of the
  formula (`SatisfiesCubicFormula`): the formula is asserted whenever such smooth densities are given
  (their existence is part of the prose of L1297-1299, and is the open assertion
  `CrossCovDensitiesExist`, below).  This is part of the *conclusion* of Theorem 2.13
  (`IsWindowEdgeworth.formula`), "the tensor is specified by `H:eq:cubic-formula` below" (L1287).
  The uniqueness `cubic_tensor_unique` is therefore stated under `CrossCovDensitiesExist` (2026-10-20).
* The two Gaussian objects: `Z` is the centered Gaussian solution of the linear equation with `q = β⁻¹`
  and initial covariance `preparedCov` (a `IsPreparedLinear` process; window `Z^{a+·}`, not stationary);
  `Z_{β,T}` is the stationary field (`IsStationaryGaussianField`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

namespace Main

variable {d : ℕ}

/-! ### Auxiliary notions -/

open Classical in
/-- The value `w^τ ∈ E_m` of a path `w ∈ 𝒳_{m,T}` at a time `τ ∈ [0,T]` (`0` outside, junk). -/
def pathEval {m T : ℝ} (w : PathSpace d m T) (τ : ℝ) : NegSobolev d m :=
  if h : τ ∈ Set.Icc (0 : ℝ) T then PathSpace.at' w ⟨τ, h⟩ else 0

/-- The cyclic sum `∑_{cyc(i,j,k)} F(i,j,k)` over the three observation slots (three terms counted
with multiplicity, TeX L1313). -/
def cyc3 (F : Fin 3 → Fin 3 → Fin 3 → ℝ) : ℝ := F 0 1 2 + F 1 2 0 + F 2 0 1

/-- The pair kernel `h_v(x,y) = (v(x) - v(y))·∇g(x - y)` of a vector field `v` (TeX L1301-1302). -/
def hKernel (d : ℕ) (s : ℝ) (v : Torus d → Euc d) (x y : Torus d) : ℝ :=
  inner ℝ (v x - v y) (periodicRieszGrad d s (x - y))

/-- The three-term coefficient `κ_{ijk}` of `H:eq:cubic-formula` (TeX L1303-1312) on three
observations `(t_i, φ_i)` (physical times `t_i`), for the mean-field coefficients `(D, ρ)`, physical
temperature `β`, preparation `(β₀, μ°)`, with `f_i^r = U^{r,t_i}φ_i` (`propagator`),
`r_i° = R_{β₀,μ°}P_{μ°}f_i^0` (`responseInverse`) and the cross-covariance densities `χ_i^r`:
`κ_{ijk} = μ°(r_i° r_j° r_k°) - ∑_cyc ∫_0^{t_i}∬ h_{∇f_i^r}(x,y)χ_j^r(x)χ_k^r(y) dx dy dr
 + (2/β) ∑_cyc ∫_0^{t_i∧t_j}∫ ∇f_i^r·∇f_j^r χ_k^r dx dr` (the integrals begin at physical time zero). -/
def cubicKappa (D : DynData d) (ρ : ℝ → Torus d → ℝ) (β β₀ : ℝ) (μ0 : Measure (Torus d))
    (t : Fin 3 → ℝ) (φ : Fin 3 → Torus d → ℝ) (χ : Fin 3 → ℝ → Torus d → ℝ) : ℝ :=
  (∫ x, responseInverse (periodicRiesz d D.s) μ0 β₀ (propagator D ρ 0 (t 0) (φ 0)) x *
        responseInverse (periodicRiesz d D.s) μ0 β₀ (propagator D ρ 0 (t 1) (φ 1)) x *
        responseInverse (periodicRiesz d D.s) μ0 β₀ (propagator D ρ 0 (t 2) (φ 2)) x ∂μ0) -
    cyc3 (fun i j k => ∫ r in Set.Icc 0 (t i), ∫ x, ∫ y,
      hKernel d D.s (Torus.grad (propagator D ρ r (t i) (φ i))) x y * χ j r x * χ k r y) +
    (2 / β) * cyc3 (fun i j k => ∫ r in Set.Icc 0 (min (t i) (t j)), ∫ x,
      inner ℝ (Torus.grad (propagator D ρ r (t i) (φ i)) x)
        (Torus.grad (propagator D ρ r (t j) (φ j)) x) * χ k r x)

/-- The standing hypotheses of Section 2.6 (TeX L1257-1268): `s < d/2` (and `d ≥ 2`, `β > 0`,
smooth `V`, smooth positive `μ°` are in `PreparedData`), `m > 3d + 8`, preparation `ℚ_{N,β₀}(μ°)`
with fixed `β₀ > 0`, and `β₀ = 0` additionally permitted for the logarithm (`s = 0`). -/
structure EdgeworthHyp (S : PreparedData d) (β₀ m : ℝ) : Prop where
  s_lt : S.s < (d : ℝ) / 2
  m_gt : 3 * (d : ℝ) + 8 < m
  β₀_nonneg : 0 ≤ β₀
  β₀_pos : 0 < β₀ ∨ S.s = 0

/-- The distance of the second-moment tensors of two random paths, in the projective norm:
`‖E[Z₁⊗Z₁] - E[Z₂⊗Z₂]‖_π = sup_{‖M‖≤1}|E M(Z₁,Z₁) - E M(Z₂,Z₂)|`, `M` bounded bilinear forms
(duality `(B ⊗̂_π B)* = B[×2]→L ℝ`; the TeX norms `E[Z⊗Z]` of `Z` with finite second moment,
TeX L1334-1340). -/
def covDist {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] {Ω₁ Ω₂ : Type*}
    [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] (P₁ : Measure Ω₁) (P₂ : Measure Ω₂)
    (Z₁ : Ω₁ → B) (Z₂ : Ω₂ → B) : ℝ :=
  ⨆ M : {M : B [×2]→L[ℝ] ℝ // ‖M‖ ≤ 1},
    |∫ ω, M.1 ![Z₁ ω, Z₁ ω] ∂P₁ - ∫ ω, M.1 ![Z₂ ω, Z₂ ω] ∂P₂|

/-! ### Theorem 2.13 -/

/-- The coordinate formula `H:eq:cubic-formula` for a tensor `Kt` and window start `a` (TeX L1291-1312):
for observations `(t_i,φ_i)`, `t_i ∈ [a,a+T]`, `φ_i` smooth, bounded linear functionals `ℓ_i` on
`𝒳_{m,T}` with `ℓ_i w = ⟨w^{t_i - a}, φ_i⟩`, every Gaussian `Z` (centered, linear equation with
`q = β⁻¹`, initial covariance `preparedCov`, on the horizon `a+T`) and smooth densities `χ_i^r` with
`∫ψχ_i^r dx = Cov(Z^r(ψ), Z^{t_i}(φ_i))` for smooth `ψ` and **every** `0 ≤ r ≤ a+T` (the formula uses
`χ_j^r, χ_k^r` for `r` up to `t_i`, which may exceed `t_j, t_k`; TeX L1297-1299 defines `χ_i^r` for every `r`)
(`H:eq:cross-covariance-density`), `Kt(ℓ_i ⊗ ℓ_j ⊗ ℓ_k) = κ_{ijk}` (`cubicKappa`). -/
def SatisfiesCubicFormula (S : PreparedData d) (β₀ m T a : ℝ)
    (Kt : projTensor (PathSpace d m T) 3) : Prop :=
  ∀ (t : Fin 3 → ℝ) (φ : Fin 3 → Torus d → ℝ),
    (∀ i, t i ∈ Set.Icc a (a + T)) → (∀ i, Torus.IsSmooth (φ i)) →
  ∀ (ℓ : Fin 3 → (PathSpace d m T →L[ℝ] ℝ)),
    (∀ i w, ℓ i w = NegSobolev.eval (pathEval w (t i - a)) (φ i)) →
  ∀ (ν : Measure (NegSobolev d m)),
    IsCenteredGaussianWithCov m ν (preparedCov d S.s β₀ S.μ0) →
  ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Z₀ : Ω' → NegSobolev d m) (Z : ℝ → Ω' → NegSobolev d m),
    IsPreparedLinear S m (a + T) ν P' Z₀ Z →
  ∀ χ : Fin 3 → ℝ → Torus d → ℝ, (∀ i r, Torus.IsSmooth (χ i r)) →
    (∀ i, ∀ r ∈ Set.Icc (0 : ℝ) (a + T), ∀ ψ : Torus d → ℝ, Torus.IsSmooth ψ →
      ∫ x, ψ x * χ i r x = ∫ ω, NegSobolev.eval (Z r ω) ψ * NegSobolev.eval (Z (t i) ω) (φ i) ∂P') →
    ((Kt : projTensor (PathSpace d m T) 3) : TensorDual (PathSpace d m T) 3)
      ((ContinuousMultilinearMap.mkPiAlgebraFin ℝ 3 ℝ).compContinuousLinearMap ℓ) =
      cubicKappa S.dyn S.ρ S.β β₀ S.μ0 t φ χ

/-- The conclusion of Theorem 2.13 `M:H:thm:edgeworth` (TeX L1273-1289) for a family `K = (𝒦_{a,T})_{a ≥ 0}`
of tensors and a sequence `ε = (ε_N(T))`: `K a` is a symmetric projective tensor on `𝒳 = 𝒳_{m,T}`,
`sup_{a ≥ 0}‖K a‖_π < ∞`, `ε_N → 0`, and for every window start `a ≥ 0`, `N ≥ 2`, every particle system
(`SelectedFlow` on `[0,a+T]` with `law X₀ = ℚ_{N,β₀}(μ°)`), every Gaussian `Z` (the centered Gaussian
solution of the linear equation with `q = β⁻¹` and initial covariance `preparedCov`), and every
`Φ` in the unit ball of `C_b^5(𝒳)`,
`|√N(E Φ(ζ_N^{a+·}) - E Φ(Z^{a+·})) - (1/6)E⟨D³Φ(Z^{a+·}), 𝒦_{a,T}⟩| ≤ ε_N(T)`
(`H:eq:window-edgeworth`; `ζ_N` centered at the actual finite-particle first marginal, `windowZeta`),
and `K a` is specified by `H:eq:cubic-formula` (`SatisfiesCubicFormula`).

Statement repair (ISSUES.md, entry "Filtered strong solutions: follow-up repairs"): the proof of Theorem 2.13 applies the path Itô identity `F:eq:path-Ito` (the duality identity `B:prop:duality-identity`), which needs a Brownian filtration, so the expansion is asserted for filtered strong solutions (`∃ ℱ W', IsFilteredSolution P ℱ W' W X`, the strong-solution adaptedness of A.1 that `SelectedFlow` records only as measurability, ISSUES D1). -/
structure IsWindowEdgeworth (S : PreparedData d) (β₀ m T : ℝ)
    (K : ℝ → projTensor (PathSpace d m T) 3) (ε : ℕ → ℝ) : Prop where
  symmetric : ∀ a : ℝ, 0 ≤ a → ∀ (M : (PathSpace d m T) [×3]→L[ℝ] ℝ) (σ : Equiv.Perm (Fin 3)),
    ((K a : projTensor (PathSpace d m T) 3) : TensorDual (PathSpace d m T) 3) (M.domDomCongr σ) =
      ((K a : projTensor (PathSpace d m T) 3) : TensorDual (PathSpace d m T) 3) M
  bounded : ∃ C : ℝ, ∀ a : ℝ, 0 ≤ a → ‖K a‖ ≤ C
  eps_tendsto : Tendsto ε atTop (𝓝 0)
  expansion : ∀ a : ℝ, 0 ≤ a → ∀ N : ℕ, 2 ≤ N →
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
      SelectedFlow P S.dyn (a + T) X₀ W X →
      (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
        (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X) →
      law P X₀ = modulatedGibbs (periodicRiesz d S.s) N β₀ S.μ0 →
    ∀ (ν : Measure (NegSobolev d m)),
      IsCenteredGaussianWithCov m ν (preparedCov d S.s β₀ S.μ0) →
    ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
      (Z₀ : Ω' → NegSobolev d m) (Z : ℝ → Ω' → NegSobolev d m),
      IsPreparedLinear S m (a + T) ν P' Z₀ Z →
    ∀ Φ : PathSpace d m T → ℝ, Φ ∈ CbUnitBall (PathSpace d m T) 5 →
      |Real.sqrt N * (∫ z, Φ z ∂(law P (windowZeta m T a P X)) -
          ∫ z, Φ z ∂(law P' (windowPath m T a Z))) -
        (1 / 6) * ∫ ω, ((K a : projTensor (PathSpace d m T) 3) : TensorDual (PathSpace d m T) 3)
          (iteratedFDeriv ℝ 3 Φ (windowPath m T a Z ω)) ∂P'| ≤ ε N
  formula : ∀ a : ℝ, 0 ≤ a → SatisfiesCubicFormula S β₀ m T a (K a)

/-- Theorem 2.13 `M:H:thm:edgeworth` (TeX L1273-1289), the first non-Gaussian correction, uniformly
over window starts.  Standing hypotheses `EdgeworthHyp` (TeX L1257-1268: `s < d/2`, `m > 3d + 8`,
preparation `ℚ_{N,β₀}(μ°)`, `β₀ > 0` or `β₀ = 0` for the logarithm; `S` the smooth setting) and
`T > 0`: there are symmetric projective tensors `𝒦_{a,T}`, `sup_{a ≥ 0}‖𝒦_{a,T}‖_π < ∞`, and a sequence
`ε_N(T) → 0` with the expansion `H:eq:window-edgeworth` and the cubic formula (all in
`IsWindowEdgeworth`, whose expansion now assumes the filtered strong solution of the particle system, see there).
No polynomial rate for `ε_N(T)` is asserted.
The initial-variance hypothesis "uniformity in the physical temperature" of TeX L1243-1253 is not
part of this statement (see the report). -/
theorem edgeworth_window (S : PreparedData d) (β₀ m T : ℝ) (hE : EdgeworthHyp S β₀ m) (hT : 0 < T) :
    ∃ (K : ℝ → projTensor (PathSpace d m T) 3) (ε : ℕ → ℝ), IsWindowEdgeworth S β₀ m T K ε := by
  sorry

/-- OPEN REGULARITY ASSERTION (TeX L1296-1299, `H:eq:cross-covariance-density`): for every observation triple
`(t_i, φ_i)` with `t_i ∈ [a, a+T]`, `φ_i` smooth, and every prepared linear Gaussian field `Z`, there are smooth
densities `χ_i^r` (`r ∈ [0, a+T]`) with `∫ ψ χ_i^r dx = Cov(Z^r(ψ), Z^{t_i}(φ_i))` for all smooth `ψ`.  The TeX asserts
this in prose; it is not proved in Lean, and `cross_cov_densities_exist` below states it as an open row.
`SatisfiesCubicFormula` is vacuous at a triple for which no such `χ` exists. -/
def CrossCovDensitiesExist (S : PreparedData d) (β₀ m T a : ℝ) : Prop :=
  ∀ (t : Fin 3 → ℝ) (φ : Fin 3 → Torus d → ℝ),
    (∀ i, t i ∈ Set.Icc a (a + T)) → (∀ i, Torus.IsSmooth (φ i)) →
  ∀ (ν : Measure (NegSobolev d m)),
    IsCenteredGaussianWithCov m ν (preparedCov d S.s β₀ S.μ0) →
  ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Z₀ : Ω' → NegSobolev d m) (Z : ℝ → Ω' → NegSobolev d m),
    IsPreparedLinear S m (a + T) ν P' Z₀ Z →
  ∃ χ : Fin 3 → ℝ → Torus d → ℝ, (∀ i r, Torus.IsSmooth (χ i r)) ∧
    ∀ i, ∀ r ∈ Set.Icc (0 : ℝ) (a + T), ∀ ψ : Torus d → ℝ, Torus.IsSmooth ψ →
      ∫ x, ψ x * χ i r x = ∫ ω, NegSobolev.eval (Z r ω) ψ * NegSobolev.eval (Z (t i) ω) (φ i) ∂P'

/-- OPEN ROW: the cross-covariance densities of `H:eq:cross-covariance-density` exist (TeX L1296-1299, asserted
in prose).  Not proved. -/
theorem cross_cov_densities_exist (S : PreparedData d) (β₀ m T a : ℝ) (hE : EdgeworthHyp S β₀ m)
    (hT : 0 < T) (ha : 0 ≤ a) : CrossCovDensitiesExist S β₀ m T a := by
  sorry

/-- `M:prose:L1290-1331` (TeX L1317-1318, proof L8936-8938): "these evaluations determine the
projective tensor, including coincident times", i.e. a projective tensor satisfying the coordinate
formula `H:eq:cubic-formula` for all observations is unique (so `𝒦_{a,T}` of Theorem 2.13 is
determined by the formula).  CONDITIONAL on `CrossCovDensitiesExist` (hypothesis `hχ`): without the
cross-covariance densities the formula `SatisfiesCubicFormula` quantifies over an empty set of `χ` for
some observation triples and does not determine the tensor (statement repair, 2026-10-20 10:05Z, ISSUES
"cubic_tensor_unique"). -/
theorem cubic_tensor_unique (S : PreparedData d) (β₀ m T a : ℝ) (hE : EdgeworthHyp S β₀ m)
    (hT : 0 < T) (ha : 0 ≤ a) (hχ : CrossCovDensitiesExist S β₀ m T a)
    (K₁ K₂ : projTensor (PathSpace d m T) 3)
    (h₁ : SatisfiesCubicFormula S β₀ m T a K₁) (h₂ : SatisfiesCubicFormula S β₀ m T a K₂) :
    K₁ = K₂ := by
  sorry

/-! ### Corollary 2.14 -/

/-- Corollary 2.14 `M:H:cor:stationary-correction` (TeX L1332-1361), relaxation of the tensors
(`H:eq:tensor-relaxation`).  Let `𝒦_{a,T}`, `ε_N(T)` be as in Theorem 2.13 (`IsWindowEdgeworth`).  There
are a stationary cubic tensor `𝒦_{∞,T}` and `C_T, c > 0` such that for all `a ≥ 0`
`‖𝒦_{a,T} - 𝒦_{∞,T}‖_π ≤ C_T e^{-ca}` (no Gaussian object occurs, so this bound is unconditional), and,
for the Gaussian `Z` of Theorem 2.13 and the stationary window `Z_{β,T}` (`IsStationaryGaussianField`,
thermal density `ρβ`), `‖C_{a,T} - C_{∞,T}‖_π ≤ C_T e^{-ca}` (the two bounds with the same constant are
equivalent to the TeX sum up to the constant).  `C_{a,T} = E[Z^{a+·}⊗Z^{a+·}]` is expressed through the
dual formula `covDist`.  Non-vacuity of the Gaussian part: `stationaryField_exists`,
`preparedLinear_exists`, `preparedGaussian_exists`. -/
theorem stationary_tensor_relaxation (S : PreparedData d) (β₀ m T : ℝ) (hE : EdgeworthHyp S β₀ m)
    (hT : 0 < T) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) (K : ℝ → projTensor (PathSpace d m T) 3)
    (ε : ℕ → ℝ) (hK : IsWindowEdgeworth S β₀ m T K ε) :
    ∃ (Kst : projTensor (PathSpace d m T) 3) (C c : ℝ), 0 < C ∧ 0 < c ∧
      (∀ a : ℝ, 0 ≤ a → ‖K a - Kst‖ ≤ C * Real.exp (-c * a)) ∧
      ∀ a : ℝ, 0 ≤ a →
      ∀ (ν : Measure (NegSobolev d m)),
        IsCenteredGaussianWithCov m ν (preparedCov d S.s β₀ S.μ0) →
      ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
        (Z₀ : Ω' → NegSobolev d m) (Z : ℝ → Ω' → NegSobolev d m),
        IsPreparedLinear S m (a + T) ν P' Z₀ Z →
      ∀ {Ω'' : Type} [MeasurableSpace Ω''] (P'' : Measure Ω'') [IsProbabilityMeasure P'']
        (Zs : ℝ → Ω'' → NegSobolev d m),
        IsStationaryGaussianField P'' S.s S.β S.hs0 S.hsd S.hβ S.V ρβ m Zs →
        covDist P' P'' (windowPath m T a Z) (windowPath m T 0 Zs) ≤ C * Real.exp (-c * a) := by
  sorry

/-- Corollary 2.14 `M:H:cor:stationary-correction` (TeX L1342-1348), the hybrid correction
`H:eq:hybrid-correction`: for every `a_N → ∞`, uniformly on the `C_b^5` unit ball,
`E Φ(ζ_N^{a_N+·}) = E Φ(Z^{a_N+·}) + (6√N)⁻¹ E⟨D³Φ(Z_{β,T}), 𝒦_{∞,T}⟩ + o(N^{-1/2})`
(`𝒦_{∞,T}` the stationary tensor of `stationary_tensor_relaxation`, taken as an argument with the
relaxation property; the `o(N^{-1/2})` is `ε/√N` for every `ε > 0` and `N ≥ N₀(ε)`).

Statement repair (ISSUES.md, entry "Filtered strong solutions: follow-up repairs"): the particle system is a filtered strong solution (`∃ ℱ W', IsFilteredSolution P ℱ W' W X`), as in `IsWindowEdgeworth.expansion` which this corollary consumes through Theorem 2.13 (Itô/duality identity). -/
theorem hybrid_correction (S : PreparedData d) (β₀ m T : ℝ) (hE : EdgeworthHyp S β₀ m)
    (hT : 0 < T) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) (K : ℝ → projTensor (PathSpace d m T) 3) (ε : ℕ → ℝ)
    (hK : IsWindowEdgeworth S β₀ m T K ε) (Kst : projTensor (PathSpace d m T) 3) (C c : ℝ)
    (hC : 0 < C) (hc : 0 < c)
    (hrel : ∀ a : ℝ, 0 ≤ a → ‖K a - Kst‖ ≤ C * Real.exp (-c * a))
    (a : ℕ → ℝ) (ha0 : ∀ N, 0 ≤ a N) (ha : Tendsto a atTop atTop)
    (ν : Measure (NegSobolev d m)) (hν : IsCenteredGaussianWithCov m ν (preparedCov d S.s β₀ S.μ0))
    {Ω'' : Type} [MeasurableSpace Ω''] (P'' : Measure Ω'') [IsProbabilityMeasure P'']
    (Zs : ℝ → Ω'' → NegSobolev d m) (hZs : IsStationaryGaussianField P'' S.s S.β S.hs0 S.hsd S.hβ S.V ρβ m Zs) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        SelectedFlow P S.dyn (a N + T) X₀ W X →
        (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
          (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X) →
        law P X₀ = modulatedGibbs (periodicRiesz d S.s) N β₀ S.μ0 →
      ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
        (Z₀ : Ω' → NegSobolev d m) (Z : ℝ → Ω' → NegSobolev d m),
        IsPreparedLinear S m (a N + T) ν P' Z₀ Z →
      ∀ Φ : PathSpace d m T → ℝ, Φ ∈ CbUnitBall (PathSpace d m T) 5 →
        |∫ z, Φ z ∂(law P (windowZeta m T (a N) P X)) -
            ∫ z, Φ z ∂(law P' (windowPath m T (a N) Z)) -
          (1 / (6 * Real.sqrt N)) * ∫ ω, ((Kst : projTensor (PathSpace d m T) 3) :
            TensorDual (PathSpace d m T) 3)
              (iteratedFDeriv ℝ 3 Φ (windowPath m T 0 Zs ω)) ∂P''| ≤ η / Real.sqrt N := by
  sorry

/-- Corollary 2.14 `M:H:cor:stationary-correction` (TeX L1349-1360), the two-parameter expansion
`H:eq:two-parameter`: with `ΔC_a = C_{a,T} - C_{∞,T}`, uniformly over `a ≥ 0`, `N ≥ 2` and the
`C_b^5` unit ball,
`E Φ(ζ_N^{a+·}) = E Φ(Z_{β,T}) + ½E⟨D²Φ(Z_{β,T}), ΔC_a⟩ + (6√N)⁻¹E⟨D³Φ(Z_{β,T}), 𝒦_{∞,T}⟩
 + O(‖ΔC_a‖²_π + N^{-1/2}(ε_N(T) + e^{-ca}))`
(`ΔC_a`'s pairing is `∫ ΔC_a(D²Φ(z)) dlaw(Z_{β,T})(z)`, with `ΔC_a(M) = E M(Z^{a+·},Z^{a+·}) -
E M(Z_{β,T},Z_{β,T})`; `‖ΔC_a‖_π` is `covDist`; `c, 𝒦_{∞,T}` and the constant `C₁` are those of the
relaxation estimate `stationary_tensor_relaxation`, given as hypotheses `hrel` (tensor half) and `hcov` (covariance half
`‖ΔC_a‖_π ≤ C₁e^{-ca}`, TeX `H:eq:tensor-relaxation`); the constant `C` is
chosen after them and before `a, N`, the realization, `Z`, `Φ`).

Statement repair (ISSUES.md, entry "Filtered strong solutions: follow-up repairs"): the particle system is a filtered strong solution (`∃ ℱ W', IsFilteredSolution P ℱ W' W X`), as in `IsWindowEdgeworth.expansion` which this corollary consumes through Theorem 2.13 (Itô/duality identity).

Statement repair 2 (ISSUES.md, "TWO-PARAM-EXPANSION"): the covariance half `hcov` of `H:eq:tensor-relaxation` is a hypothesis; without it the term `N^{-1/2}‖ΔC_a‖_π` coming from the cubic term is not absorbed. -/
theorem two_parameter_expansion (S : PreparedData d) (β₀ m T : ℝ) (hE : EdgeworthHyp S β₀ m)
    (hT : 0 < T) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) (K : ℝ → projTensor (PathSpace d m T) 3) (ε : ℕ → ℝ)
    (hK : IsWindowEdgeworth S β₀ m T K ε) (Kst : projTensor (PathSpace d m T) 3) (C₁ c : ℝ)
    (hC₁ : 0 < C₁) (hc : 0 < c)
    (hrel : ∀ a' : ℝ, 0 ≤ a' → ‖K a' - Kst‖ ≤ C₁ * Real.exp (-c * a'))
    (hcov : ∀ a' : ℝ, 0 ≤ a' → ∀ (ν : Measure (NegSobolev d m)),
        IsCenteredGaussianWithCov m ν (preparedCov d S.s β₀ S.μ0) →
      ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
        (Z₀ : Ω' → NegSobolev d m) (Z : ℝ → Ω' → NegSobolev d m),
        IsPreparedLinear S m (a' + T) ν P' Z₀ Z →
      ∀ {Ω'' : Type} [MeasurableSpace Ω''] (P'' : Measure Ω'')
        [IsProbabilityMeasure P''] (Zs : ℝ → Ω'' → NegSobolev d m),
        IsStationaryGaussianField P'' S.s S.β S.hs0 S.hsd S.hβ S.V ρβ m Zs →
        covDist P' P'' (windowPath m T a' Z) (windowPath m T 0 Zs) ≤ C₁ * Real.exp (-c * a')) :
    ∃ C : ℝ, 0 < C ∧
      ∀ a : ℝ, 0 ≤ a → ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        SelectedFlow P S.dyn (a + T) X₀ W X →
        (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
          (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X) →
        law P X₀ = modulatedGibbs (periodicRiesz d S.s) N β₀ S.μ0 →
      ∀ (ν : Measure (NegSobolev d m)),
        IsCenteredGaussianWithCov m ν (preparedCov d S.s β₀ S.μ0) →
      ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
        (Z₀ : Ω' → NegSobolev d m) (Z : ℝ → Ω' → NegSobolev d m),
        IsPreparedLinear S m (a + T) ν P' Z₀ Z →
      ∀ {Ω'' : Type} [MeasurableSpace Ω''] (P'' : Measure Ω'')
        [IsProbabilityMeasure P''] (Zs : ℝ → Ω'' → NegSobolev d m),
        IsStationaryGaussianField P'' S.s S.β S.hs0 S.hsd S.hβ S.V ρβ m Zs →
      ∀ Φ : PathSpace d m T → ℝ, Φ ∈ CbUnitBall (PathSpace d m T) 5 →
        |∫ z, Φ z ∂(law P (windowZeta m T a P X)) - ∫ z, Φ z ∂(law P'' (windowPath m T 0 Zs)) -
            (1 / 2) * ∫ ω'', (∫ ω, (iteratedFDeriv ℝ 2 Φ (windowPath m T 0 Zs ω''))
                ![windowPath m T a Z ω, windowPath m T a Z ω] ∂P' -
              ∫ ω₂, (iteratedFDeriv ℝ 2 Φ (windowPath m T 0 Zs ω''))
                ![windowPath m T 0 Zs ω₂, windowPath m T 0 Zs ω₂] ∂P'') ∂P'' -
            (1 / (6 * Real.sqrt N)) * ∫ ω, ((Kst : projTensor (PathSpace d m T) 3) :
              TensorDual (PathSpace d m T) 3)
                (iteratedFDeriv ℝ 3 Φ (windowPath m T 0 Zs ω)) ∂P''| ≤
          C * (covDist P' P'' (windowPath m T a Z) (windowPath m T 0 Zs) ^ 2 +
            (Real.sqrt N)⁻¹ * (ε N + Real.exp (-c * a))) := by
  sorry

/-! ### Sharpness of the root-`N` rate below `d/2` -/

/-- `M:prose:L1104-1148` (TeX L1117-1121): "the rate `√N δ_N` (`= N^{-1/2}` below `d/2`) is order-sharp when
a cubic coefficient is nonzero".  Consequence of Theorem 2.13 (`IsWindowEdgeworth`): if for some test
`Φ` in the `C_b^5` unit ball the first correction `(1/6)E⟨D³Φ(Z^{a+·}), 𝒦_{a,T}⟩` is nonzero, then for
particle systems `X_N` started from `ℚ_{N,β₀}(μ°)` (windows starting at `a`), the exactly centered fields
satisfy `liminf √N d_5(ζ_N^{a+·}, Z^{a+·}) ≥ |(1/6)E⟨D³Φ(Z^{a+·}), 𝒦_{a,T}⟩| > 0`.

Statement repair (ISSUES.md, entry "Filtered strong solutions: follow-up repairs"): `hfilt` makes each `X_N` a filtered strong solution, which the expansion of Theorem 2.13 (`IsWindowEdgeworth.expansion`, Itô/duality identity) now requires. -/
theorem edgeworth_sharpness (S : PreparedData d) (β₀ m T : ℝ) (hE : EdgeworthHyp S β₀ m)
    (hT : 0 < T) (K : ℝ → projTensor (PathSpace d m T) 3) (ε : ℕ → ℝ)
    (hK : IsWindowEdgeworth S β₀ m T K ε) (a : ℝ) (ha : 0 ≤ a)
    (ν : Measure (NegSobolev d m)) (hν : IsCenteredGaussianWithCov m ν (preparedCov d S.s β₀ S.μ0))
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Z₀ : Ω' → NegSobolev d m) (Z : ℝ → Ω' → NegSobolev d m)
    (hZ : IsPreparedLinear S m (a + T) ν P' Z₀ Z)
    (Φ : PathSpace d m T → ℝ) (hΦ : Φ ∈ CbUnitBall (PathSpace d m T) 5)
    (Ω : ℕ → Type) [∀ N, MeasurableSpace (Ω N)] (P : ∀ N, Measure (Ω N))
    [∀ N, IsProbabilityMeasure (P N)] (X₀ : ∀ N, Ω N → Config d N)
    (W : ∀ N, ℝ≥0 → Ω N → (Fin N → Euc d)) (X : ∀ N, ℝ≥0 → Ω N → Config d N)
    (hflow : ∀ N : ℕ, 2 ≤ N → SelectedFlow (P N) S.dyn (a + T) (X₀ N) (W N) (X N))
    (hfilt : ∀ N : ℕ, 2 ≤ N → ∃ (ℱ : MeasureTheory.Filtration ℝ (inferInstance : MeasurableSpace (Ω N)))
      (W' : ℝ≥0 → Ω N → (Fin N × Fin d) → ℝ), IsFilteredSolution (P N) ℱ W' (W N) (X N))
    (hinit : ∀ N : ℕ, 2 ≤ N → law (P N) (X₀ N) = modulatedGibbs (periodicRiesz d S.s) N β₀ S.μ0) :
    ENNReal.ofReal |(1 / 6) * ∫ ω, ((K a : projTensor (PathSpace d m T) 3) :
        TensorDual (PathSpace d m T) 3) (iteratedFDeriv ℝ 3 Φ (windowPath m T a Z ω)) ∂P'| ≤
      liminf (fun N : ℕ => ENNReal.ofReal (Real.sqrt N *
        smoothDist 5 (law (P N) (windowZeta m T a (P N) (X N)))
          (law P' (windowPath m T a Z)))) atTop := by
  sorry

/-- `M:prose:L1104-1148` (TeX L1117-1121) with `M:prose:L1290-1331` (L1322-1326): sharpness on the
homogeneous torus.  `V = 0`, `ρ° = 1`, preparation at the physical temperature `β₀ = β`, window
start `a = 0`: for `k ≠ 0`, `b ≠ 0`, the one-time observation `φ = ψ_k + bψ_{2k}` at time `0` has the
nonzero cubic coefficient `3b v_{β,k}²v_{β,2k}/√2` (`homogeneous_cubic_coefficients`), hence the
root-`N` rate is sharp: there is a test `Φ` in the `C_b^5` unit ball of `𝒳_{m,T}` with
`liminf √N d_5(ζ_N, Z) > 0` (for the particle systems of `edgeworth_sharpness`).

Statement repair (ISSUES.md, entry "Filtered strong solutions: follow-up repairs"): `hfilt` makes each `X_N` a filtered strong solution, which the expansion of Theorem 2.13 (`IsWindowEdgeworth.expansion`, Itô/duality identity) now requires. -/
theorem edgeworth_sharpness_homogeneous (S : PreparedData d) (m T : ℝ)
    (hE : EdgeworthHyp S S.β m) (hT : 0 < T) (hV : S.V = fun _ => 0) (hρ0 : S.ρ0 = fun _ => 1)
    (k : Lattice d) (hk : k ≠ 0) (b : ℝ) (hb : b ≠ 0)
    (K : ℝ → projTensor (PathSpace d m T) 3) (ε : ℕ → ℝ) (hK : IsWindowEdgeworth S S.β m T K ε)
    (ν : Measure (NegSobolev d m)) (hν : IsCenteredGaussianWithCov m ν (preparedCov d S.s S.β S.μ0))
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Z₀ : Ω' → NegSobolev d m) (Z : ℝ → Ω' → NegSobolev d m)
    (hZ : IsPreparedLinear S m (0 + T) ν P' Z₀ Z)
    (Ω : ℕ → Type) [∀ N, MeasurableSpace (Ω N)] (P : ∀ N, Measure (Ω N))
    [∀ N, IsProbabilityMeasure (P N)] (X₀ : ∀ N, Ω N → Config d N)
    (W : ∀ N, ℝ≥0 → Ω N → (Fin N → Euc d)) (X : ∀ N, ℝ≥0 → Ω N → Config d N)
    (hflow : ∀ N : ℕ, 2 ≤ N → SelectedFlow (P N) S.dyn (0 + T) (X₀ N) (W N) (X N))
    (hfilt : ∀ N : ℕ, 2 ≤ N → ∃ (ℱ : MeasureTheory.Filtration ℝ (inferInstance : MeasurableSpace (Ω N)))
      (W' : ℝ≥0 → Ω N → (Fin N × Fin d) → ℝ), IsFilteredSolution (P N) ℱ W' (W N) (X N))
    (hinit : ∀ N : ℕ, 2 ≤ N → law (P N) (X₀ N) = modulatedGibbs (periodicRiesz d S.s) N S.β S.μ0) :
    ∃ Φ : PathSpace d m T → ℝ, Φ ∈ CbUnitBall (PathSpace d m T) 5 ∧
      0 < liminf (fun N : ℕ => ENNReal.ofReal (Real.sqrt N *
        smoothDist 5 (law (P N) (windowZeta m T 0 (P N) (X N)))
          (law P' (windowPath m T 0 Z)))) atTop := by
  sorry

/-! ### `M:prose:L1290-1331`: explicit coefficients on the homogeneous torus -/

/-- `M:prose:L1290-1331` (TeX L1322-1326): on a homogeneous torus (`μ° = dx`, preparation at the
physical temperature `β₀ = β`), the initial term `μ°(r³)` of the cubic coefficient
(`H:eq:cubic-formula`; at a single time `t = 0` the other two terms are integrals over `[0,0]` and
vanish, so this is the full stationary one-time coefficient), `r = R_{β,dx}P φ` (`responseInverse`),
satisfies, with `ψ_k = √2cos(2πk·x)` (`PDE.cosTest`) and `v_{β,k} = (1 + βĝ(k))⁻¹`
(`d ≥ 2`, `0 ≤ s < d`, `β > 0`, `k ≠ 0`):
a single cosine has zero cubic coefficient, `∫ (R ψ_k)³ dx = 0`; and for `φ = ψ_k + bψ_{2k}`,
`∫ (R φ)³ dx = 3b v_{β,k}² v_{β,2k}/√2`, which is nonzero for `b ≠ 0`. -/
theorem homogeneous_cubic_coefficients (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ)
    (hβ : 0 < β) (k : Lattice d) (hk : k ≠ 0) (b : ℝ) :
    (∫ x, responseInverse (periodicRiesz d s) (volume : Measure (Torus d)) β (PDE.cosTest k) x ^ 3) =
        0 ∧
    (∫ x, responseInverse (periodicRiesz d s) (volume : Measure (Torus d)) β
        (fun x => PDE.cosTest k x + b * PDE.cosTest ((2 : ℤ) • k) x) x ^ 3) =
      3 * b * (1 + β * rieszCoeff d s k)⁻¹ ^ 2 * (1 + β * rieszCoeff d s ((2 : ℤ) • k))⁻¹ /
        Real.sqrt 2 ∧
    (b ≠ 0 → 3 * b * (1 + β * rieszCoeff d s k)⁻¹ ^ 2 *
        (1 + β * rieszCoeff d s ((2 : ℤ) • k))⁻¹ / Real.sqrt 2 ≠ 0) := by
  have hk2 : (2 : ℤ) • k ≠ 0 := q42_two_smul_ne hk
  have hne1 : (1 + β * rieszCoeff d s k) ≠ 0 := (q42_one_add_pos hd hs0 hsd hβ k).ne'
  have hne2 : (1 + β * rieszCoeff d s ((2 : ℤ) • k)) ≠ 0 :=
    (q42_one_add_pos hd hs0 hsd hβ _).ne'
  refine ⟨?_, ?_, ?_⟩
  · have hae := q42_responseInverse_eq hd hs0 hsd hβ k hk (PDE.cosTest k) 1 0 (fun x => by simp)
    have e1 : ∫ x : Torus d, responseInverse (periodicRiesz d s) (volume : Measure (Torus d)) β
        (PDE.cosTest k) x ^ 3 = ∫ x : Torus d, ((1 * (1 + β * rieszCoeff d s k)⁻¹) * PDE.cosTest k x +
          (0 * (1 + β * rieszCoeff d s ((2 : ℤ) • k))⁻¹) * PDE.cosTest ((2 : ℤ) • k) x) ^ 3 :=
      integral_congr_ae (hae.mono fun x hx => by simp only [hx])
    rw [e1, q42_cube k hk]
    simp
  · have hae := q42_responseInverse_eq hd hs0 hsd hβ k hk
      (fun x => PDE.cosTest k x + b * PDE.cosTest ((2 : ℤ) • k) x) 1 b (fun x => by simp)
    have e2 : ∫ x : Torus d, responseInverse (periodicRiesz d s) (volume : Measure (Torus d)) β
        (fun x => PDE.cosTest k x + b * PDE.cosTest ((2 : ℤ) • k) x) x ^ 3 =
        ∫ x : Torus d, ((1 * (1 + β * rieszCoeff d s k)⁻¹) * PDE.cosTest k x +
          (b * (1 + β * rieszCoeff d s ((2 : ℤ) • k))⁻¹) * PDE.cosTest ((2 : ℤ) • k) x) ^ 3 :=
      integral_congr_ae (hae.mono fun x hx => by simp only [hx])
    rw [e2, q42_cube k hk]
    ring
  · intro hb
    exact div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hb)
      (pow_ne_zero 2 (inv_ne_zero hne1))) (inv_ne_zero hne2))
      (Real.sqrt_pos.mpr (by norm_num)).ne'

/-! ### Rows pointing to later sections

* `M:prose:L1242-1272`, uniformity paragraph (L1243-1253): the temperature-uniformity of "every
  positive-temperature assertion" is a meta-quantifier remark (no new statement beyond the
  temperature-uniform path bound `critical_centered_path_uniform` of `HeadlineEquilibrium.lean`);
  the Edgeworth standing hypotheses and the projective tensors are `EdgeworthHyp`, `projTensor`.
* `M:prose:L1362-1395`: the exact covariance transient `H:eq:preparation-transient` is Proposition 7.13
  (`M:E:prop:quench`), the waiting-time criterion `a_N - (4λ_*)⁻¹ log N → +∞` is Corollary 7.14
  (`M:E:cor:critical-Edgeworth`), the chaos threshold at `s = d/2` is Proposition 7.18
  (`HRS.chaos_tendsto`, `HRS.localDiv_critical`) and the unbounded supremum over the half-line is
  Proposition 5.18 (`M:U:prop:unbounded`): the statements belong to those rows and are not restated.
* `M:prose:L1396-1420` (besides `empirical_field_deterministic_bound` of `Headline.lean`): the bounded spectral summary is Proposition 4.21/Corollary 4.22
  (`HRS.static_field_limit_general`, `HRS.static_field_limit_canonical`, `HRS.negSpectralCoeff`);
  the mesoscopic screening paragraph is Proposition 6.1 (`M:O:prop:screening`).
-/

end Main

end HRS
