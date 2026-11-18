import HRS.Main.Linearization
import HRS.PDE.MeanField
import HRS.Equilibrium.PoleCavity
import HRS.Equilibrium.Response
import HRS.Dynamics.InitialData
import HRS.Stochastic.SelectedFlow
import HRS.Sections.Sec5
import HRS.Main.Q42Aux2
import HRS.Sections.Q41Aux21

/-!
# Section 2 of the main manuscript: the general fluctuation scale and prepared nonequilibrium
fluctuations (headline results and prose claims, part 1)

Specification file SPEC-2 (statements with `sorry` proofs; definitions contain no `sorry`).
Source: `HRS_periodic_main_20261008T010000Z.tex` ("M"), Section 2, lines 471-902.

Rows covered (see the docstring of each declaration for the printed number and TeX lines):
`M:prose:L471-528`, `M:prose:L529-579`, `M:prose:L621-666`, `M:H:ex:deterministic` (2.2),
`M:@remark:L684`, `M:prose:L720-765`, `M:H:thm:prepared` (2.5), `M:prose:L805-835`,
`M:H:ex:mixture` (2.6), `M:H:cor:thermalization` (2.7), `M:@remark:L891`.

## Representation decisions

* **Windows.**  The shifted observation path `w^{a+·}` restricted to `[0,T]` (TeX L526-528) of a
  particle system, of a centered particle system and of a linear process is `windowFluc`,
  `windowZeta`, `windowPath`.  As in `HRS.flucPath` / `HRS.toPath` a path that is not continuous is
  sent to `0` (junk value; the particle paths are a.s. continuous, `IsStrongSolution.cont`).
* **Section 2.4 data** (`PreparedData`, TeX L739-747): `d ≥ 2`, `0 ≤ s < d`, `β > 0`, `V` smooth, the
  smooth strictly positive initial density `ρ°`, and the global smooth solution `ρ` of the
  mean-field equation, represented as the `C([0,∞);H^K)` solution of Proposition 5.1 for every
  `K > d/2 + 6` (`PDE.IsMFSolutionHK`): "global smooth positive solution" is not an extra hypothesis
  but the objects of Proposition 5.1 (its existence/uniqueness is `PDE.finite_reg_exists_unique`).
* **Particle system.**  `SelectedFlow` (Assumption A.1, cases (a),(b),(d); the gradient model with
  `β > 0` is covered) on the horizon `a + T` for the window start `a`; the actual particle law is
  `f_N^0 = law P X₀`.  Different `a` use different horizons (the constants are chosen before `a`).
* **Linear process `Y`** (`H:eq:linear-equation`, `q = β⁻¹`) is any `IsLinearFluctuationSolution`
  with initial law `ν = Law(η°)` (the law of the path is unique, Proposition A.33), on the horizon
  `a + T`; only laws enter the metrics.
* **Distances in `ℝ≥0∞`.**  `a_{N,p}` is `wassersteinE` and may be `∞`; the theorem assumes it finite
  where the TeX says "whenever the displayed initial moments are finite".  Expectations of norms are
  `lintegral`s of `‖·‖ₑ`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

namespace Main

variable {d : ℕ}

/-! ### Window paths (TeX L520-528) -/

section Windows

variable {Ω : Type*} {N : ℕ}

/-- The window `t ↦ σ(μ_N^{a+t} - μ^{a+t})`, `0 ≤ t ≤ T`, of the (rescaled) fluctuation path
(`η_N^{a+·}` for `σ = √N`; TeX L526-528 and `H:eq:centerings`, L463-464).  It is `HRS.flucPath`
of the shifted objects (`0` path if it is not continuous). -/
def windowFluc (m T a σ : ℝ) (X : ℝ≥0 → Ω → Config d N) (ρ : ℝ → Torus d → ℝ) (ω : Ω) :
    PathSpace d m T :=
  flucPath m T σ (fun t => X (Real.toNNReal a + t)) (fun t => ρ (a + t)) ω

/-- The window `t ↦ Y^{a+t}`, `0 ≤ t ≤ T`, of a linear process (`Y^{a+·}`, TeX L526-528). -/
def windowPath (m T a : ℝ) (Y : ℝ → Ω → NegSobolev d m) (ω : Ω) : PathSpace d m T :=
  toPath m T (fun t => Y (a + t)) ω

open Classical in
/-- The window `t ↦ ζ_N^{a+t} = √N(μ_N^{a+t} - m_N^{a+t})`, `0 ≤ t ≤ T`, of the exactly centered
field (`H:eq:centerings`, TeX L465): the center at time `a+t` is the actual mean empirical measure
`m_N^{a+t} = E[μ_N^{a+t}]` of the law of `X^{a+t}` under `P` (`HRS.zetaE`).  `0` path if not
continuous. -/
def windowZeta [MeasurableSpace Ω] (m T a : ℝ) (P : Measure Ω) (X : ℝ≥0 → Ω → Config d N)
    (ω : Ω) : PathSpace d m T :=
  if h : Continuous fun t : Set.Icc (0 : ℝ) T =>
      zetaE m (P.map (X (Real.toNNReal (a + t)))) (X (Real.toNNReal (a + t)) ω) then ⟨_, h⟩ else 0

end Windows

/-! ### The stationary linear Gaussian field `Z_β` (TeX L932-939) -/

/-! The stationary Gaussian field `Z_β` of Section 2.5 (TeX L930-939) is the single predicate
`HRS.IsStationaryGaussianField` of `HRS/Sections/Sec3.lean` (a measurable, a.s. continuous
`E_m`-valued process on `[0,∞)` whose finite-dimensional laws against smooth tests are the centered
Gaussians with covariance `PDE.stationaryLagCov`; the dynamics are `PDE.mfData`, i.e. `M = -I`,
`β⁻¹`, potential `V`).  The earlier draft predicate of this file (which also carried the thermal
equation for `ρβ`) is dropped: the thermal equation is a separate hypothesis `IsThermalDensity` in
each statement.  Non-vacuity: `stationaryField_exists` below. -/

/-- Existence of the stationary Gaussian field `Z_β` on `E_m` (source: Corollary 5.3,
`M:C:cor:linear`, TeX L5917-5932, and the prose L930-939; the coordinate processes are the
stationary Ornstein-Uhlenbeck modes): for `d ≥ 2`, `0 ≤ s < d`, `β > 0`, smooth `V`, the thermal
density `ρβ` and `m > max{d+1, d/2+2}` (this contains `m > d+2`, `m > 3d+8`, `m ≥ 24d+240`), there
is a probability space carrying a stationary Gaussian field.  Stated here so that the statements about
`Z_β` are not vacuous. -/
theorem stationaryField_exists (hd : 2 ≤ d) {s β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (m : ℝ)
    (hm : max ((d : ℝ) + 1) ((d : ℝ) / 2 + 2) < m) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (Z : ℝ → Ω → NegSobolev d m), IsStationaryGaussianField P s β hs0 hsd hβ V ρβ m Z := by
  have h1 : (d : ℝ) + 1 < m := lt_of_le_of_lt (le_max_left _ _) hm
  exact HRS.Q41.q41_field_exists hd hs0 hsd hβ V hV ρβ hρβ m
    (by nlinarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)])

/-! ### `M:prose:L471-528`: the linearization -/

/-- `M:prose:L471-528` (TeX L477-487), the gradient case of the backward generator
`H:eq:backward-generator`: "in the gradient case the last term has a plus sign".  For `M = -I`,
`𝓛_rφ = β⁻¹Δφ - ∇(V + g*ρ)·∇φ + ∑_j ∂_j g * (ρ ∂_jφ)`, with both convolutions by the
cancellation convention (`convGradConv`, `∂_j g * f` the `j`-th component of `∇g * f`). -/
theorem backwardGenerator_gradient (D : DynData d) (hM : D.M = -1) (ρ φ : Torus d → ℝ)
    (x : Torus d) :
    backwardGenerator D ρ φ x =
      D.invβ * Torus.laplacian φ x -
        inner ℝ (convGradConv (periodicRieszGrad d D.s) ρ x + Torus.grad D.V x) (Torus.grad φ x) +
        ∑ j : Fin d, (convGradConv (periodicRieszGrad d D.s)
          (fun y => ρ y * (Torus.grad φ y) j) x) j := by
  have hMv : ∀ v : Euc d, Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ) v = -v := by
    intro v; simp [Torus.matVec]
  have hneg : ∀ (h : Torus d → ℝ) (z : Torus d),
      convGradConv (periodicRieszGrad d D.s) (fun y => -h y) z =
        -convGradConv (periodicRieszGrad d D.s) h z := by
    intro h z
    unfold convGradConv
    rw [← integral_neg]
    congr 1
    funext y
    split_ifs
    · rw [show -h y - -h z = -(h y - h z) by ring, neg_smul]
    · rw [neg_smul]
  unfold backwardGenerator meanFieldDrift
  rw [hM, Matrix.transpose_neg, Matrix.transpose_one]
  simp only [hMv, PiLp.neg_apply, mul_neg, hneg, Finset.sum_neg_distrib]
  rw [inner_sub_left, inner_neg_left, inner_add_left]
  ring

/-! ### `M:prose:L621-666`: remarks after Theorem 2.1 -/

/-- `M:prose:L621-666` (TeX L627-630; the balanced-weight limits `H:eq:balanced-weights` of TeX L635-651 are
`HRS.balanced_weights`, `HRS.balanced_weights_zero`, `HRS.balanced_weights_infty` in
`HRS/Dynamics/InitialData.lean`): "For gradient dynamics with `s + 2 - d ≤ 1`, the same
one-space comparison also holds without a positive lower density bound if the stated derivative
bounds hold" (the estimates `H:eq:general-smooth`-`H:eq:general-W2` of Theorem 2.1 on
`𝒳_{γ,T}`, with `PosDensityWith` replaced by `s + 2 - d ≤ 1`; the transport improvement still
needs the lower bound and is `general_fluctuation_transport`).  Same hypotheses and constants as
`HRS.GeneralSetup.general_fluctuation` otherwise.

Statement repair (ISSUES.md, entries "5.14 `criterion_comparison`…" and "N:thm:dynamic …"; final entry "Filtered strong solutions …"): its proof (U-section, `U:eq:quantitative-mild`) rests on the exact empirical-adjoint identity `B:prop:duality-identity` (Lemma 3.7), whose Itô calculus needs a Brownian filtration, so `X` is assumed a filtered strong solution (`IsFilteredSolution`), the strong-solution adaptedness of A.1 that `IsStrongSolution` (measurability only, ISSUES D1) does not record.

Statement repair 2026-10-16 (ISSUES "SPEC-C0"): the completion constant `C₀` of `o_N` must be taken large enough (TeX M L546-555, L2279-2299 "Increasing its constant once suffices"), so the conclusion is now stated for every `C₀ ≥ C₀min` (with `C₀min` independent of `C₀`) and the setups `Within { b with C₀ := C₀ }`; previously `C₀` was pinned to `b.C₀` with no lower bound. -/
theorem general_fluctuation_noLowerBound (b : GeneralBounds d) :
    ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ → ∃ C : ℝ, 0 < C ∧
      ∀ S : GeneralSetup d, S.Within { b with C₀ := C₀ } → S.MFHyp →
      S.s + 2 - (d : ℝ) ≤ 1 →
      ∀ (N : ℕ) (_ : 2 ≤ N) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P]
      (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (_ : IsVectorBrownian P W)
      (X : ℝ≥0 → Ω → Config d N) (_ : IsStrongSolution P (S.dyn N) S.T X₀ W X)
      (_ : ∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
        (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X)
      (_ : S.EnergyMomentFinite P N X)
      (η₀ : Ω → NegSobolev d S.γ) (_ : Measurable η₀)
      (_ : ProbabilityTheory.IndepFun (fun ω => (X₀ ω, η₀ ω)) (fun ω => fun t => W t ω) P)
      (_ : S.InitialErrorFinite P N 1 X₀ η₀)
      (Y : ℝ → Ω → NegSobolev d S.γ)
      (_ : IsLinearFluctuationSolution P (S.dyn N) (S.ρ N) S.γ (qScale N (S.κ N) (S.invβ N)) S.T
        (fun ω => Ascale N (S.κ N) (S.invβ N) • η₀ ω) Y),
      let σ := sigmaScale N (S.κ N) (S.invβ N)
      let A := Ascale N (S.κ N) (S.invβ N)
      let q := qScale N (S.κ N) (S.invβ N)
      let 𝔈 := S.energyMoment P N X
      let Ξ := law P (flucPath S.γ S.T σ X (S.ρ N))
      let YN := law P (toPath S.γ S.T Y)
      smoothDist 2 Ξ YN ≤
          C * (A * S.initialError P N 1 X₀ η₀ + σ * 𝔈 + q * (Real.sqrt 𝔈 + (N : ℝ) ^ (-(2 : ℝ) / d))) ∧
      wassersteinE 1 Ξ YN ≤ ENNReal.ofReal
          (C * (A * S.initialError P N 1 X₀ η₀ + σ * 𝔈 +
            Real.sqrt q * (𝔈 ^ ((1 : ℝ) / 4) + (N : ℝ) ^ (-(1 : ℝ) / d)))) ∧
      (S.EnergyMoment2Finite P N X →
        Integrable (fun ω => ‖flucPath S.γ S.T σ X (S.ρ N) ω‖ ^ 2) P →
        S.InitialErrorFinite P N 2 X₀ η₀ →
        wassersteinE 2 Ξ YN ≤ ENNReal.ofReal
          (C * (A * S.initialError P N 2 X₀ η₀ + σ * S.energyMoment2 P N X +
            Real.sqrt q * (𝔈 ^ ((1 : ℝ) / 4) + (N : ℝ) ^ (-(1 : ℝ) / d))))) := by
  sorry

/-- `(N^a)^2 N = N^(2a+1)` for real `N > 0`. -/
private lemma q35_rpow_sq_mul (N : ℝ) (hN : 0 < N) (a : ℝ) :
    (N ^ a) ^ 2 * N = N ^ (2 * a + 1) := by
  have h1 : (N ^ a) ^ 2 = N ^ (a * 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]
    norm_num
  rw [h1, show 2 * a + 1 = a * 2 + 1 by ring, Real.rpow_add hN, Real.rpow_one]


/-- `M:prose:L621-666` (TeX L653-665, `H:eq:amplitude-condition`), the elementary consequences of the
amplitude condition for positive powers `0 < s < d` (`σ_N = min{κ_N, √(Nβ_N)}`,
`β_N⁻¹ = invβ N`; `𝔈_N` a sequence of energy bounds):
(a) if `𝔈_N = O(N^{s/d-1})` (`|𝔈 N| ≤ C₀ N^{s/d-1}` for `N ≥ 1`) and
`min{κ_N,√(Nβ_N)} N^{s/d-1} → 0`, then the nonlinear smallness `σ_N 𝔈_N → 0`;
(b) in the thermal branch `σ_N = √(Nβ_N)` (i.e. `√(Nβ_N) ≤ κ_N`, `β_N < ∞`) the condition
`√(Nβ_N) N^{s/d-1} → 0` is equivalent to `β_N N^{2s/d-1} → 0`;
(c) `β_N N^{2s/d-1} → 0` implies the microscopic weakness `β_N N^{s/d-1} → 0` (it is stronger).
Here `β_N = 1/invβ N`, so (b), (c) are stated with `(invβ N)⁻¹`, `invβ N > 0`. -/
theorem amplitude_condition (s : ℝ) (hs0 : 0 < s) (hsd : s < d) (κ invβ 𝔈 : ℕ → ℝ)
    (hκ : ∀ N, 0 < κ N) (hinvβ : ∀ N, 0 ≤ invβ N)
    (C₀ : ℝ) (hE : ∀ N : ℕ, 1 ≤ N → |𝔈 N| ≤ C₀ * (N : ℝ) ^ (s / d - 1)) :
    (Tendsto (fun N : ℕ => sigmaScale N (κ N) (invβ N) * (N : ℝ) ^ (s / d - 1)) atTop (𝓝 0) →
      Tendsto (fun N : ℕ => sigmaScale N (κ N) (invβ N) * 𝔈 N) atTop (𝓝 0)) ∧
    ((∀ N : ℕ, 1 ≤ N → 0 < invβ N ∧ Real.sqrt ((N : ℝ) / invβ N) ≤ κ N) →
      (Tendsto (fun N : ℕ => sigmaScale N (κ N) (invβ N) * (N : ℝ) ^ (s / d - 1)) atTop (𝓝 0) ↔
        Tendsto (fun N : ℕ => (invβ N)⁻¹ * (N : ℝ) ^ (2 * s / d - 1)) atTop (𝓝 0))) ∧
    (Tendsto (fun N : ℕ => (invβ N)⁻¹ * (N : ℝ) ^ (2 * s / d - 1)) atTop (𝓝 0) →
      Tendsto (fun N : ℕ => (invβ N)⁻¹ * (N : ℝ) ^ (s / d - 1)) atTop (𝓝 0)) := by
  have hσnn : ∀ N, 0 ≤ sigmaScale N (κ N) (invβ N) := by
    intro N
    unfold sigmaScale
    split_ifs with h
    · exact (hκ N).le
    · exact le_min (hκ N).le (Real.sqrt_nonneg _)
  refine ⟨fun hσ => ?_, fun hcond => ?_, fun hc => ?_⟩
  · have h2 := hσ.const_mul C₀
    rw [mul_zero] at h2
    refine squeeze_zero_norm' ?_ h2
    filter_upwards [eventually_ge_atTop 1] with N hN
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hσnn N)]
    calc sigmaScale N (κ N) (invβ N) * |𝔈 N|
        ≤ sigmaScale N (κ N) (invβ N) * (C₀ * (N : ℝ) ^ (s / d - 1)) :=
          mul_le_mul_of_nonneg_left (hE N hN) (hσnn N)
      _ = C₀ * (sigmaScale N (κ N) (invβ N) * (N : ℝ) ^ (s / d - 1)) := by ring
  · have hsq : ∀ N : ℕ, 1 ≤ N →
        (sigmaScale N (κ N) (invβ N) * (N : ℝ) ^ (s / d - 1)) ^ 2
          = (invβ N)⁻¹ * (N : ℝ) ^ (2 * s / d - 1) := by
      intro N hN
      obtain ⟨hpos, hle⟩ := hcond N hN
      have hNpos : (0 : ℝ) < N := Nat.cast_pos.2 (by omega)
      have hσ : sigmaScale N (κ N) (invβ N) = Real.sqrt ((N : ℝ) / invβ N) := by
        unfold sigmaScale
        rw [if_neg hpos.ne', min_eq_right hle]
      rw [hσ, mul_pow, Real.sq_sqrt (div_nonneg hNpos.le hpos.le)]
      have key := q35_rpow_sq_mul (N : ℝ) hNpos (s / d - 1)
      calc (N : ℝ) / invβ N * ((N : ℝ) ^ (s / d - 1)) ^ 2
          = (invβ N)⁻¹ * (((N : ℝ) ^ (s / d - 1)) ^ 2 * N) := by ring
        _ = (invβ N)⁻¹ * (N : ℝ) ^ (2 * (s / d - 1) + 1) := by rw [key]
        _ = (invβ N)⁻¹ * (N : ℝ) ^ (2 * s / d - 1) := by
          rw [show 2 * (s / d - 1) + 1 = 2 * s / d - 1 by ring]
    constructor
    · intro h
      have h2 := h.pow 2
      rw [zero_pow two_ne_zero] at h2
      refine h2.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with N hN
      exact hsq N hN
    · intro h
      have hs : Tendsto (fun N : ℕ => Real.sqrt ((invβ N)⁻¹ * (N : ℝ) ^ (2 * s / d - 1)))
          atTop (𝓝 0) := by
        have := (Real.continuous_sqrt.tendsto 0).comp h
        rw [Real.sqrt_zero] at this
        exact this
      refine hs.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with N hN
      rw [← hsq N hN, Real.sqrt_sq (mul_nonneg (hσnn N) (Real.rpow_nonneg (Nat.cast_nonneg N) _))]
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hc ?_ ?_
    · filter_upwards with N
      exact mul_nonneg (inv_nonneg.2 (hinvβ N)) (Real.rpow_nonneg (Nat.cast_nonneg N) _)
    · filter_upwards [eventually_ge_atTop 1] with N hN
      have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.2 (hinvβ N))
      apply Real.rpow_le_rpow_of_exponent_le hN1
      have h0 : 0 ≤ s / (d : ℝ) := div_nonneg hs0.le (Nat.cast_nonneg _)
      have e : 2 * s / (d : ℝ) = 2 * (s / d) := by ring
      linarith

/-! ### Example 2.2 -/

/-- Example 2.2 `M:H:ex:deterministic` (TeX L667-682), gradient case.  `β_N = ∞` (`invβ N = 0`),
deterministic initial configuration `x₀` (`X₀ ≡ x₀`), deterministic `η° = F ∈ E_γ`.  In a verified
mean-field and energy regime (the hypotheses of `HRS.GeneralSetup.general_fluctuation`), the
quantitative deterministic estimate
`sup_{t ≤ T} ‖κ_N(μ_N^t - μ^t) - V^{t,0}η°‖_{H^{-γ}} ≤ C_T(ε_{N,1} + κ_N 𝔈_N)`
holds (almost surely; the zero-temperature dynamics is deterministic), with
`ε_{N,1} = ‖κ_N(μ_N^0 - μ^0) - F‖_{H^{-γ}}` and `V^{t,0}F = transportField`.  The Gaussian term is
identically zero because `q_N = 0`, `A_N = 1`.  The supremum is stated as a bound for every
`t ∈ [0,T]` (a real `iSup` of an unbounded family would be a junk value).  Related qualitative
statement: Example A.16 (`deterministic_example`).

Statement repair (ISSUES.md, entries "5.14 `criterion_comparison`…" and "N:thm:dynamic …"; final entry "Filtered strong solutions …"): Example 2.2 is Theorem 2.1 for deterministic data, whose proof rests on the duality identity `B:prop:duality-identity` (Lemma 3.7; the Lean duality lemma is stated for `IsFilteredSolution` also at `β = ∞`), which needs a Brownian filtration, so `X` is assumed a filtered strong solution (`IsFilteredSolution`), the strong-solution adaptedness of A.1 that `IsStrongSolution` (measurability only, ISSUES D1) does not record.

Statement repair 2026-10-16 (ISSUES "SPEC-C0"): the completion constant `C₀` of `o_N` must be taken large enough (TeX M L546-555, L2279-2299 "Increasing its constant once suffices"), so the conclusion is now stated for every `C₀ ≥ C₀min` (with `C₀min` independent of `C₀`) and the setups `Within { b with C₀ := C₀ }`; previously `C₀` was pinned to `b.C₀` with no lower bound. -/
theorem deterministic_comparison (b : GeneralBounds d) :
    ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ → ∃ C : ℝ, 0 < C ∧
      ∀ S : GeneralSetup d, S.Within { b with C₀ := C₀ } → S.MFHyp → S.PosDensityWith b.c →
      (∀ N, S.invβ N = 0) →
      ∀ (N : ℕ) (_ : 2 ≤ N) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (x₀ : Config d N)
      (W : ℝ≥0 → Ω → (Fin N → Euc d)) (_ : IsVectorBrownian P W)
      (X : ℝ≥0 → Ω → Config d N)
      (_ : IsStrongSolution P (S.dyn N) S.T (fun _ => x₀) W X)
      (_ : ∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
        (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X)
      (_ : S.EnergyMomentFinite P N X) (F : NegSobolev d (S.γ : ℝ)),
      ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) S.T,
        ‖S.κ N • NegSobolev.ofMeasureDiff (S.γ : ℝ) (empirical (X (Real.toNNReal t) ω))
            (withDensityReal (S.ρ N t)) - transportField (S.dyn N) (S.ρ N) t (S.γ : ℝ) F‖ ≤
          C * (‖S.κ N • NegSobolev.ofMeasureDiff (S.γ : ℝ) (empirical x₀)
              (withDensityReal (S.ρ N 0)) - F‖ + S.κ N * S.energyMoment P N X) := by
  sorry

/-- Example 2.2, general-matrix version (TeX L678: "uses `H^{-(γ+2)}`"): `Sym M ≤ 0`, the adjoint
input `AdjointInput M K` of Theorem 2.1, the path estimate in `E_{γ+2}` (`F` embedded by
`NegSobolev.embed`), the initial error still measured in `E_γ`.

Statement repair (ISSUES.md, entries "5.14 `criterion_comparison`…" and "N:thm:dynamic …"; final entry "Filtered strong solutions …"): Example 2.2 is Theorem 2.1 for deterministic data, whose proof rests on the duality identity `B:prop:duality-identity` (Lemma 3.7), which needs a Brownian filtration, so `X` is assumed a filtered strong solution (`IsFilteredSolution`), the strong-solution adaptedness of A.1 that `IsStrongSolution` (measurability only, ISSUES D1) does not record.

Statement repair 2026-10-16 (ISSUES "SPEC-C0"): the completion constant `C₀` of `o_N` must be taken large enough (TeX M L546-555, L2279-2299 "Increasing its constant once suffices"), so the conclusion is now stated for every `C₀ ≥ C₀min` (with `C₀min` independent of `C₀`) and the setups `Within { b with C₀ := C₀ }`; previously `C₀` was pinned to `b.C₀` with no lower bound. -/
theorem deterministic_comparison_matrix (b : GeneralBounds d) (M : Matrix (Fin d) (Fin d) ℝ)
    (hM : Torus.SymNonpos M) (K : ℝ) :
    ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ → ∃ C : ℝ, 0 < C ∧
      ∀ S : GeneralSetup d, S.Within { b with C₀ := C₀ } → S.MFHypM M → S.AdjointInput M K →
      (∀ N, S.invβ N = 0) →
      ∀ (N : ℕ) (_ : 2 ≤ N) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (x₀ : Config d N)
      (W : ℝ≥0 → Ω → (Fin N → Euc d)) (_ : IsVectorBrownian P W)
      (X : ℝ≥0 → Ω → Config d N)
      (_ : IsStrongSolution P (S.dynM M N) S.T (fun _ => x₀) W X)
      (_ : ∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
        (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X)
      (_ : S.EnergyMomentFinite P N X) (F : NegSobolev d (S.γ : ℝ)),
      ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) S.T,
        ‖S.κ N • NegSobolev.ofMeasureDiff ((S.γ : ℝ) + 2) (empirical (X (Real.toNNReal t) ω))
            (withDensityReal (S.ρ N t)) -
          transportField (S.dynM M N) (S.ρ N) t ((S.γ : ℝ) + 2)
            (NegSobolev.embed ((S.γ : ℝ) + 2) F)‖ ≤
          C * (‖S.κ N • NegSobolev.ofMeasureDiff (S.γ : ℝ) (empirical x₀)
              (withDensityReal (S.ρ N 0)) - F‖ + S.κ N * S.energyMoment P N X) := by
  sorry

/-! ### Remark after Example 2.2: evaluation maps -/

/-- `M:@remark:L684` (TeX L685-690), first paragraph: evaluation at finitely many times
`t_1,…,t_p ∈ [0,T]` is a bounded linear map `𝒳_{m,T} → E_m^p` (product with the sup norm), of norm
at most one: `‖(w^{t_i})_i‖_∞ ≤ ‖w‖_{𝒳_{m,T}}`. -/
theorem pathEval_bounded (m T : ℝ) (p : ℕ) (ts : Fin p → Set.Icc (0 : ℝ) T) :
    ∃ L : PathSpace d m T →L[ℝ] (Fin p → NegSobolev d m),
      (∀ w i, L w i = PathSpace.at' w (ts i)) ∧ ‖L‖ ≤ 1 := by
  let L0 : C(Set.Icc (0 : ℝ) T, NegSobolev d m) →L[ℝ] (Fin p → NegSobolev d m) :=
    ContinuousLinearMap.pi fun i => ContinuousMap.evalCLM ℝ (ts i)
  refine ⟨L0, fun w i => rfl, ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => ?_⟩
  rw [one_mul]
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  exact ContinuousMap.norm_coe_le_norm w (ts i)

/-- `M:@remark:L684` (TeX L687-688): a scalar observation `w ↦ ⟨w^t, φ⟩` of a path, `φ ∈ H^m`, is a
bounded linear functional on `𝒳_{m,T}` of norm at most `‖φ‖_{H^m}`. -/
theorem pathObservation_bounded (m T : ℝ) (t : Set.Icc (0 : ℝ) T) (φ : Torus d → ℝ)
    (hφ : MemSobolev m φ) :
      ∃ ℓ : PathSpace d m T →L[ℝ] ℝ,
      (∀ w, ℓ w = NegSobolev.eval (PathSpace.at' w t) φ) ∧ ‖ℓ‖ ≤ sobolevNorm m φ := by
  have hS : Summable fun k : NonzeroLattice d => (Lattice.jp k.1 ^ m * Torus.funRealCoeff φ k) ^ 2 := by
    refine hφ.2.congr fun k => ?_
    rw [mul_pow, Torus.jp_rpow_sq]
  let yL : lp (fun _ : NonzeroLattice d => ℝ) 2 :=
    ⟨fun k => Lattice.jp k.1 ^ m * Torus.funRealCoeff φ k, (Torus.memℓp_two_iff _).2 hS⟩
  let y : NegSobolev d m := yL
  let ℓ0 : NegSobolev d m →L[ℝ] ℝ := innerSL ℝ y
  have hev : ∀ F : NegSobolev d m, ℓ0 F = NegSobolev.eval F φ := by
    intro F
    change inner ℝ yL (show lp (fun _ : NonzeroLattice d => ℝ) 2 from F) = _
    rw [lp.inner_eq_tsum]
    unfold NegSobolev.eval NegSobolev.fourierCoeff
    refine tsum_congr fun k => ?_
    simp only [yL, RCLike.inner_apply, conj_trivial]
    change _ * (Lattice.jp k.1 ^ m * Torus.funRealCoeff φ k) = _
    unfold NegSobolev.coord
    ring
  have hy : ‖y‖ ≤ sobolevNorm m φ := by
    have h2 : ‖yL‖ ^ 2 = ∑' k : NonzeroLattice d, (Lattice.jp k.1 ^ m * Torus.funRealCoeff φ k) ^ 2 :=
      (Torus.lp_two_sq yL).2
    have h3 : ∑' k : NonzeroLattice d, (Lattice.jp k.1 ^ m * Torus.funRealCoeff φ k) ^ 2 =
        ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (2 * m) * Torus.funRealCoeff φ k ^ 2 :=
      tsum_congr fun k => by rw [mul_pow, Torus.jp_rpow_sq]
    unfold sobolevNorm
    rw [← Real.sqrt_sq (norm_nonneg y)]
    refine Real.sqrt_le_sqrt ?_
    change ‖yL‖ ^ 2 ≤ _
    rw [h2, h3]
    exact le_add_of_nonneg_left (sq_nonneg _)
  refine ⟨(ℓ0.comp (ContinuousMap.evalCLM ℝ t) : PathSpace d m T →L[ℝ] ℝ), fun w => hev _, ?_⟩
  have key : ∀ F : NegSobolev d m, ‖ℓ0 F‖ ≤ ‖y‖ * ‖F‖ := fun F => by
    simp only [ℓ0, innerSL_apply_apply, Real.norm_eq_abs]
    exact abs_real_inner_le_norm y F
  refine (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg y) fun w => ?_).trans hy
  exact (key _).trans (mul_le_mul_of_nonneg_left (ContinuousMap.norm_coe_le_norm w t) (norm_nonneg y))

section Contractions

variable {B B' : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B] [BorelSpace B]
  [NormedAddCommGroup B'] [NormedSpace ℝ B'] [MeasurableSpace B'] [BorelSpace B']

/-- `M:@remark:L684` (TeX L687-689): "the path bounds imply the corresponding fixed-time field
bounds and scalar bounds, with the norm of the evaluation map included": the pushforward by a bounded
linear map `L` (an evaluation map) multiplies `W_p` by at most `‖L‖`. -/
theorem wassersteinE_map_clm_le (L : B →L[ℝ] B') (p : ℝ) (hp : 1 ≤ p) (P Q : Measure B)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    wassersteinE p (P.map L) (Q.map L) ≤ ENNReal.ofReal ‖L‖ * wassersteinE p P Q := by
  have hLm : Measurable L := L.continuous.measurable
  have hp0 : 0 < p := by linarith
  have hprod : Measurable (Prod.map L L) := hLm.prodMap hLm
  have key : ∀ π : Measure (B × B), IsCoupling π P Q →
      wassersteinE p (P.map L) (Q.map L) ≤
        ENNReal.ofReal ‖L‖ * (∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ p) ∂π) ^ (1 / p) := by
    intro π hπ
    have hmap : IsCoupling (π.map (Prod.map L L)) (P.map L) (Q.map L) := by
      constructor
      · rw [Measure.map_map measurable_fst hprod, show (Prod.fst ∘ Prod.map L L) = L ∘ Prod.fst from rfl,
          ← Measure.map_map hLm measurable_fst, hπ.1]
      · rw [Measure.map_map measurable_snd hprod, show (Prod.snd ∘ Prod.map L L) = L ∘ Prod.snd from rfl,
          ← Measure.map_map hLm measurable_snd, hπ.2]
    refine (wassersteinE_le_cost (p := p) hmap).trans ?_
    refine (ENNReal.rpow_le_rpow (lintegral_map_le (fun z : B' × B' => ENNReal.ofReal (‖z.1 - z.2‖ ^ p))
      hprod.aemeasurable) (by positivity)).trans ?_
    have hpt : ∀ z : B × B, ENNReal.ofReal (‖L z.1 - L z.2‖ ^ p) ≤
        ENNReal.ofReal ‖L‖ ^ p * ENNReal.ofReal (‖z.1 - z.2‖ ^ p) := by
      intro z
      have h1 : ‖L z.1 - L z.2‖ ≤ ‖L‖ * ‖z.1 - z.2‖ := by
        rw [← map_sub]; exact L.le_opNorm _
      have h2 : ‖L z.1 - L z.2‖ ^ p ≤ (‖L‖ * ‖z.1 - z.2‖) ^ p :=
        Real.rpow_le_rpow (norm_nonneg _) h1 hp0.le
      rw [Real.mul_rpow (norm_nonneg _) (norm_nonneg _)] at h2
      rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le, ← ENNReal.ofReal_mul
        (Real.rpow_nonneg (norm_nonneg _) _)]
      exact ENNReal.ofReal_le_ofReal h2
    calc (∫⁻ z, ENNReal.ofReal (‖L z.1 - L z.2‖ ^ p) ∂π) ^ (1 / p)
        ≤ (∫⁻ z, ENNReal.ofReal ‖L‖ ^ p * ENNReal.ofReal (‖z.1 - z.2‖ ^ p) ∂π) ^ (1 / p) :=
          ENNReal.rpow_le_rpow (lintegral_mono fun z => hpt z) (by positivity)
      _ = ENNReal.ofReal ‖L‖ * (∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ p) ∂π) ^ (1 / p) := by
          rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp0.le ENNReal.ofReal_ne_top),
            ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
            mul_one_div_cancel hp0.ne', ENNReal.rpow_one]
  have hne : Nonempty (couplings P Q) := by
    refine ⟨⟨P.prod Q, ?_, ?_⟩⟩
    · simp [Measure.map_fst_prod]
    · simp [Measure.map_snd_prod]
  calc wassersteinE p (P.map L) (Q.map L)
      ≤ ⨅ π : couplings P Q, ENNReal.ofReal ‖L‖ *
          (∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ p) ∂π.1) ^ (1 / p) :=
        le_iInf fun π => key π.1 π.2
    _ = ENNReal.ofReal ‖L‖ * wassersteinE p P Q := by
        unfold wassersteinE
        rw [ENNReal.mul_iInf' (fun h => absurd h ENNReal.ofReal_ne_top) (fun _ => hne)]

/-- `M:@remark:L684` (same remark), smooth metrics: pull-back of a `C_b^k` function by `L` has
`C_b^k` norm at most `max{1,‖L‖^k}` times its own (TeX L5748 uses this, `d_k` of the pushforwards
is at most `max{1,‖L‖^k} d_k`). -/
theorem smoothDist_map_clm_le (L : B →L[ℝ] B') (k : ℕ) (P Q : Measure B) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] :
    smoothDist k (P.map L) (Q.map L) ≤ max 1 (‖L‖ ^ k) * smoothDist k P Q := by
  set c : ℝ := max 1 (‖L‖ ^ k) with hc_def
  have hc1 : 1 ≤ c := le_max_left _ _
  have hcpos : 0 < c := by linarith
  have hLm : Measurable L := L.continuous.measurable
  have hpow : ∀ j ≤ k, ‖L‖ ^ j ≤ c := by
    intro j hj
    rcases le_total ‖L‖ 1 with h | h
    · exact le_trans (pow_le_one₀ (norm_nonneg _) h) hc1
    · exact le_trans (pow_le_pow_right₀ h hj) (le_max_right _ _)
  refine Real.iSup_le (fun Φ => ?_) (mul_nonneg (le_trans zero_le_one hc1) (smoothDist_nonneg k P Q))
  obtain ⟨hΦd, hΦb, hΦn⟩ := Φ.2
  set M : ℕ → ℝ := fun j => ⨆ y : B', ‖iteratedFDeriv ℝ j Φ.1 y‖ with hM_def
  have hM0 : ∀ j, 0 ≤ M j := fun j => Real.iSup_nonneg fun _ => norm_nonneg _
  have hcomp : ∀ j ≤ k, ∀ z : B, ‖iteratedFDeriv ℝ j (fun z => Φ.1 (L z)) z‖ ≤ ‖L‖ ^ j * M j := by
    intro j hj z
    have e := ContinuousLinearMap.iteratedFDeriv_comp_right (𝕜 := ℝ) L hΦd (x := z) (i := j)
      (by exact_mod_cast hj)
    rw [show (fun z => Φ.1 (L z)) = Φ.1 ∘ L from rfl, e]
    have h1 := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
      (iteratedFDeriv ℝ j Φ.1 (L z)) (fun _ : Fin j => L)
    have h2 : ‖iteratedFDeriv ℝ j Φ.1 (L z)‖ ≤ M j :=
      le_ciSup (hΦb j (by exact_mod_cast hj)) (L z)
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1
    calc _ ≤ _ := h1
      _ ≤ M j * ‖L‖ ^ j := mul_le_mul h2 le_rfl (by positivity) (hM0 j)
      _ = _ := mul_comm _ _
  set Ψ : B → ℝ := fun z => c⁻¹ • Φ.1 (L z) with hΨ_def
  have hΨD : ∀ j ≤ k, ∀ z : B, ‖iteratedFDeriv ℝ j Ψ z‖ ≤ M j := by
    intro j hj z
    have e : iteratedFDeriv ℝ j Ψ z = c⁻¹ • iteratedFDeriv ℝ j (fun z => Φ.1 (L z)) z :=
      iteratedFDeriv_const_smul_apply'
        (((hΦd.comp L.contDiff).of_le (by exact_mod_cast hj : (j : WithTop ℕ∞) ≤ k)).contDiffAt)
    rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hcpos)]
    calc c⁻¹ * ‖iteratedFDeriv ℝ j (fun z => Φ.1 (L z)) z‖ ≤ c⁻¹ * (‖L‖ ^ j * M j) :=
          mul_le_mul_of_nonneg_left (hcomp j hj z) (inv_nonneg.mpr hcpos.le)
      _ ≤ c⁻¹ * (c * M j) := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (hpow j hj) (hM0 j)) (inv_nonneg.mpr hcpos.le)
      _ = M j := by field_simp
  have hΨmem : Ψ ∈ CbUnitBall B k := by
    refine ⟨(hΦd.comp L.contDiff).const_smul c⁻¹, fun j hj => ⟨M j, ?_⟩, ?_⟩
    · rintro _ ⟨z, rfl⟩
      exact hΨD j hj z
    · unfold cbNorm
      calc ∑ j ∈ Finset.range (k + 1), ⨆ z : B, ‖iteratedFDeriv ℝ j Ψ z‖
          ≤ ∑ j ∈ Finset.range (k + 1), M j :=
            Finset.sum_le_sum fun j hj => ciSup_le fun z =>
              hΨD j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) z
        _ = cbNorm k Φ.1 := rfl
        _ ≤ 1 := hΦn
  have hsd := abs_integral_sub_le_smoothDist hΨmem P Q
  have hΦc : Continuous Φ.1 := hΦd.continuous
  have e : ∫ z, Φ.1 (L z) ∂P - ∫ z, Φ.1 (L z) ∂Q = c * (∫ z, Ψ z ∂P - ∫ z, Ψ z ∂Q) := by
    have hcc : c * c⁻¹ = 1 := mul_inv_cancel₀ hcpos.ne'
    simp only [hΨ_def, smul_eq_mul, integral_const_mul]
    linear_combination (-(∫ z, Φ.1 (L z) ∂P - ∫ z, Φ.1 (L z) ∂Q)) * hcc
  rw [smoothDist, show |∫ z, Φ.1 z ∂(P.map L) - ∫ z, Φ.1 z ∂(Q.map L)| =
      |∫ z, Φ.1 (L z) ∂P - ∫ z, Φ.1 (L z) ∂Q| by
    rw [integral_map hLm.aemeasurable hΦc.aestronglyMeasurable,
      integral_map hLm.aemeasurable hΦc.aestronglyMeasurable]]
  rw [e, abs_mul, abs_of_pos hcpos]
  exact mul_le_mul_of_nonneg_left hsd hcpos.le

end Contractions


/-! ### Section 2.4: prepared nonequilibrium fluctuations -/

/-- The setting of Section 2.4 (TeX L736-747): `d ≥ 2`, `0 ≤ s < d`, fixed `β > 0`, `M = -I`
(gradient dynamics, `dyn`), `V` smooth on the torus, a smooth strictly positive initial density `ρ°`
(`SmoothPosDensity`) and the global smooth solution `ρ` of the mean-field equation `H:eq:meanfield`
with `ρ⁰ = ρ°` (L740-741: "for every smooth strictly positive initial density `ρ°`, `H:eq:meanfield`
has a global smooth positive solution"), represented as the `C([0,∞);H^K)` solution of
Proposition 5.1 (`PDE.IsMFSolutionHK`) for every `K > d/2 + 6` (these solutions are unique and
smooth positive, `PDE.finite_reg_exists_unique`, `PDE.finite_reg_uniform_bounds`).
The analytic facts quoted in L741-746 (uniform bounds, exponential convergence to the unique thermal
equilibrium, decay of the backward adjoint modulo constants; no smallness assumption) are
Propositions 5.1 and 5.2 (rows `M:O:prop:finite-reg`, `M:C:prop:adjoint`) and are not restated. -/
structure PreparedData (d : ℕ) where
  s : ℝ
  hs0 : 0 ≤ s
  hsd : s < d
  hd : 2 ≤ d
  β : ℝ
  hβ : 0 < β
  V : Torus d → ℝ
  hV : Torus.IsSmooth V
  ρ0 : Torus d → ℝ
  hρ0 : SmoothPosDensity ρ0
  ρ : ℝ → Torus d → ℝ
  /-- technical: the solution starts from `ρ°` (implied by `IsMFSolutionHK.init`) -/
  hρ_init : ρ 0 = ρ0
  hρ : ∀ K : ℕ, (d : ℝ) / 2 + 6 < K →
    ∃ ρc : ℝ → PDE.Coeff d, PDE.IsMFSolutionHK d s V β⁻¹ (K : ℝ) ρ0 ρc ∧ PDE.mfPath ρc = ρ

namespace PreparedData

variable (S : PreparedData d)

/-- The dynamics data at inverse temperature `β` with `M = -I` and potential `V`. -/
def dyn : DynData d := PDE.mfData d S.s S.hs0 S.hsd S.V S.β S.hβ

/-- `μ° = ρ° dx`. -/
def μ0 : Measure (Torus d) := withDensityReal S.ρ0

/-- The moving reference `Q_N^t = ℚ_{N,β}(μ^t)` (TeX L756; `H:eq:modulated-gibbs`). -/
def refMeasure (N : ℕ) (t : ℝ) : Measure (Config d N) :=
  modulatedGibbs (periodicRiesz d S.s) N S.β (withDensityReal (S.ρ t))

/-- `B_N = 1 + H(f_N^0 | Q_N^0) + Nδ_N` (`H:eq:entropy-bound`, TeX L760), for the initial law `f0`
(`H` is `HRS.relEntropy`, the unnormalized relative entropy; the real value `toReal` is only used
where the entropy is finite). -/
def B (N : ℕ) (f0 : Measure (Config d N)) : ℝ :=
  1 + (relEntropy f0 (S.refMeasure N 0)).toReal + (N : ℝ) * deltaN d S.s N

/-- `J_N = 1 + Nδ_N + log ‖h_N^0‖_{L^{p_0}(Q_N^0)}`, `h_N^0 = df_N^0/dQ_N^0` (`H:eq:strong-bound`,
TeX L786); meaningful when `h_N^0 ∈ L^{p_0}(Q_N^0)`. -/
def J (N : ℕ) (f0 : Measure (Config d N)) (p0 : ℝ) : ℝ :=
  1 + (N : ℝ) * deltaN d S.s N +
    Real.log (eLpNorm (fun X => ((f0.rnDeriv (S.refMeasure N 0)) X).toReal) (ENNReal.ofReal p0)
      (S.refMeasure N 0)).toReal

/-- `a_{N,p} = W_p^{E_m}(η_N^0, η°)` (`H:eq:entropy-bound`, TeX L761), `η_N^0 = √N(μ_N^0 - μ°)`,
the prescribed initial field `η°` being given by its law `ν` on `E_m`. -/
def initW (m p : ℝ) {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (P : Measure Ω) (X₀ : Ω → Config d N)
    (ν : Measure (NegSobolev d m)) : ℝ≥0∞ :=
  wassersteinE p (law P (fun ω => etaE m (X₀ ω) S.μ0)) ν

/-- The law on `𝒳_{m,T}` of the window `η_N^{a+·}` of the particle system `X` (centered at the
mean-field measure `μ^t`). -/
def etaLaw (m T a : ℝ) {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (P : Measure Ω)
    (X : ℝ≥0 → Ω → Config d N) : Measure (PathSpace d m T) :=
  law P (windowFluc m T a (Real.sqrt N) X S.ρ)

end PreparedData

/-- `Y` is a solution of the linear equation `H:eq:linear-equation` with `q = β⁻¹`, coefficients
`(β, μ^t)` of the setting `S`, on the horizon `T'`, with initial field of law `ν` (TeX L763-764:
"let `Y` be `H:eq:linear-equation` with initial field `η°` and `q = β⁻¹`"). -/
structure IsPreparedLinear (S : PreparedData d) (m T' : ℝ) (ν : Measure (NegSobolev d m))
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') (Y₀ : Ω' → NegSobolev d m)
    (Y : ℝ → Ω' → NegSobolev d m) : Prop where
  meas : Measurable Y₀
  law_init : law P' Y₀ = ν
  sol : IsLinearFluctuationSolution P' S.dyn S.ρ m S.β⁻¹ T' Y₀ Y

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

/-- case `s = d/2`: `√N δ_N = (1 + log N) N^{-1/2}` for `N ≥ 1`. -/
private lemma q35_sqrt_delta_mid {d : ℕ} {s : ℝ} (h : s = (d : ℝ) / 2) :
    ∀ᶠ N : ℕ in atTop, Real.sqrt N * deltaN d s N = (1 + Real.log N) * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.2 (by omega)
  have hδ : deltaN d s N = (N : ℝ) ^ (-1 : ℝ) * (1 + Real.log N) := by
    unfold deltaN
    rw [if_neg (not_lt.2 h.ge), if_pos h, Real.rpow_neg_one,
      Real.log_mul (Real.exp_pos 1).ne' hN0.ne', Real.log_exp]
  have hpow : (N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (-1 : ℝ) = (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_add hN0]; norm_num
  rw [hδ, Real.sqrt_eq_rpow]
  linear_combination (1 + Real.log N) * hpow


/-- `δ_N → 0` for `0 ≤ s < d`. -/
private lemma q35_delta_tendsto {d : ℕ} (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    Tendsto (fun N : ℕ => deltaN d s N) atTop (𝓝 0) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  rcases lt_trichotomy s ((d : ℝ) / 2) with h | h | h
  · have hfun : (fun N : ℕ => deltaN d s N) = fun N : ℕ => (N : ℝ) ^ (-1 : ℝ) := by
      funext N
      unfold deltaN
      rw [if_pos h, Real.rpow_neg_one]
    rw [hfun]
    exact q35_tendsto_natpow (by norm_num)
  · have hprod : ∀ᶠ N : ℕ in atTop,
        deltaN d s N = (N : ℝ) ^ (-(1 / 2 : ℝ)) * (Real.sqrt N * deltaN d s N) := by
      filter_upwards [eventually_ge_atTop 1] with N hN
      have hN0 : (0 : ℝ) < N := Nat.cast_pos.2 (by omega)
      rw [Real.sqrt_eq_rpow, ← mul_assoc, ← Real.rpow_add hN0]
      norm_num
    have hsq : Tendsto (fun N : ℕ => Real.sqrt N * deltaN d s N) atTop (𝓝 0) :=
      q35_tendsto_log_mul.congr' ((q35_sqrt_delta_mid h).mono fun N hN => hN.symm)
    have hzero := (q35_tendsto_natpow (e := -(1 / 2 : ℝ)) (by norm_num)).mul hsq
    rw [mul_zero] at hzero
    exact hzero.congr' (hprod.mono fun N hN => hN.symm)
  · have hspos : 0 < s := by linarith
    have hfun : (fun N : ℕ => deltaN d s N) = fun N : ℕ => (N : ℝ) ^ (1 - (d : ℝ) / s) := by
      funext N
      unfold deltaN
      rw [if_neg (not_lt.2 h.le), if_neg (ne_of_gt h)]
    have h1 : 1 < (d : ℝ) / s := (one_lt_div hspos).2 hsd
    rw [hfun]
    exact q35_tendsto_natpow (by linarith)

/-- `√N δ_N → 0` for `0 ≤ s < 2d/3`. -/
private lemma q35_sqrt_delta_tendsto {d : ℕ} (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s)
    (hs : s < 2 * (d : ℝ) / 3) :
    Tendsto (fun N : ℕ => Real.sqrt N * deltaN d s N) atTop (𝓝 0) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  rcases lt_trichotomy s ((d : ℝ) / 2) with h | h | h
  · refine (q35_tendsto_natpow (e := -(1 / 2 : ℝ)) (by norm_num)).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (0 : ℝ) < N := Nat.cast_pos.2 (by omega)
    unfold deltaN
    rw [if_pos h, Real.sqrt_eq_rpow, ← Real.rpow_neg_one, ← Real.rpow_add hN0]
    norm_num
  · exact q35_tendsto_log_mul.congr' ((q35_sqrt_delta_mid h).mono fun N hN => hN.symm)
  · have hspos : 0 < s := by linarith
    have h32 : 3 / 2 < (d : ℝ) / s := (lt_div_iff₀ hspos).2 (by linarith)
    refine (q35_tendsto_natpow (e := 1 / 2 + (1 - (d : ℝ) / s)) (by linarith)).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (0 : ℝ) < N := Nat.cast_pos.2 (by omega)
    unfold deltaN
    rw [if_neg (not_lt.2 h.le), if_neg (ne_of_gt h), Real.sqrt_eq_rpow, ← Real.rpow_add hN0]


/-- `M:prose:L720-765` (TeX L748-755, `H:eq:delta`), the facts about the scale `δ_N` used in the
remarks after Theorem 2.5 (`0 ≤ s < d`, `N ≥ 1`): `Nδ_N ≥ 1` (TeX L6764: "since `Nδ_N ≥ 1`"),
hence `√δ_N ≤ √N δ_N`. -/
theorem deltaN_basic (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (N : ℕ) (hN : 1 ≤ N) :
    1 ≤ (N : ℝ) * deltaN d s N ∧ Real.sqrt (deltaN d s N) ≤ Real.sqrt N * deltaN d s N := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨hδ0, hprod⟩ : 0 ≤ deltaN d s N ∧ 1 ≤ (N : ℝ) * deltaN d s N := by
    unfold deltaN
    split_ifs with h1 h2
    · refine ⟨inv_nonneg.2 hNpos.le, ?_⟩
      rw [mul_inv_cancel₀ hNpos.ne']
    · have hL : 1 ≤ Real.log (Real.exp 1 * N) := by
        rw [Real.log_mul (Real.exp_pos 1).ne' hNpos.ne', Real.log_exp]
        have := Real.log_nonneg hN1
        linarith
      refine ⟨mul_nonneg (inv_nonneg.2 hNpos.le) (by linarith), ?_⟩
      rw [← mul_assoc, mul_inv_cancel₀ hNpos.ne', one_mul]
      exact hL
    · have h3 : (d : ℝ) / 2 < s := lt_of_le_of_ne (not_lt.1 h1) (Ne.symm h2)
      have hs : (0 : ℝ) < s := by linarith
      have hdle : (d : ℝ) / s ≤ 2 := by rw [div_le_iff₀ hs]; linarith
      have hexp : 0 ≤ 1 + (1 - (d : ℝ) / s) := by linarith
      have key : (N : ℝ) ^ (1 + (1 - (d : ℝ) / s)) = (N : ℝ) * (N : ℝ) ^ (1 - (d : ℝ) / s) := by
        rw [Real.rpow_add hNpos, Real.rpow_one]
      refine ⟨Real.rpow_nonneg hNpos.le _, ?_⟩
      rw [← key]
      exact Real.one_le_rpow hN1 hexp
  refine ⟨hprod, ?_⟩
  have hsq1 : Real.sqrt ((N : ℝ) * deltaN d s N) = Real.sqrt N * Real.sqrt (deltaN d s N) :=
    Real.sqrt_mul hNpos.le _
  have h1 : 1 ≤ Real.sqrt N * Real.sqrt (deltaN d s N) := by
    rw [← hsq1]
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt ((N : ℝ) * deltaN d s N) := Real.sqrt_le_sqrt hprod
  have hsδ : Real.sqrt (deltaN d s N) * Real.sqrt (deltaN d s N) = deltaN d s N :=
    Real.mul_self_sqrt hδ0
  have h0 : 0 ≤ Real.sqrt (deltaN d s N) := Real.sqrt_nonneg _
  calc Real.sqrt (deltaN d s N) = Real.sqrt (deltaN d s N) * 1 := (mul_one _).symm
    _ ≤ Real.sqrt (deltaN d s N) * (Real.sqrt N * Real.sqrt (deltaN d s N)) :=
        mul_le_mul_of_nonneg_left h1 h0
    _ = Real.sqrt N * (Real.sqrt (deltaN d s N) * Real.sqrt (deltaN d s N)) := by ring
    _ = Real.sqrt N * deltaN d s N := by rw [hsδ]

/-- `M:prose:L720-765` (TeX L800-801): "these errors tend to zero for `0 ≤ s < 2d/3`":
`√N δ_N → 0` and `δ_N^{1/4} → 0`. -/
theorem deltaN_errors_tendsto (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < 2 * (d : ℝ) / 3) :
    Tendsto (fun N : ℕ => Real.sqrt N * deltaN d s N) atTop (𝓝 0) ∧
      Tendsto (fun N : ℕ => deltaN d s N ^ ((1 : ℝ) / 4)) atTop (𝓝 0) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  refine ⟨q35_sqrt_delta_tendsto hd hs0 hs, ?_⟩
  have h := (q35_delta_tendsto hd hs0 (by linarith)).rpow_const
    (Or.inr (by norm_num : (0 : ℝ) ≤ 1 / 4))
  rwa [Real.zero_rpow (by norm_num : (1 / 4 : ℝ) ≠ 0)] at h

/-- `M:prose:L1104-1148` (TeX L1133-1137, `H:eq:upper-range-rate`): for `3d/5 ≤ s < 2d/3`,
`δ_N^{1/4} ≤ √N δ_N` for all `N ≥ 1`. -/
theorem deltaN_upper_range_rate (hd : 1 ≤ d) {s : ℝ} (hs1 : 3 * (d : ℝ) / 5 ≤ s)
    (hs2 : s < 2 * (d : ℝ) / 3) (N : ℕ) (hN : 1 ≤ N) :
    deltaN d s N ^ ((1 : ℝ) / 4) ≤ Real.sqrt N * deltaN d s N := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hs : (d : ℝ) / 2 < s := by linarith
  have hspos : 0 < s := by linarith
  have hfun : deltaN d s N = (N : ℝ) ^ (1 - (d : ℝ) / s) := by
    unfold deltaN
    rw [if_neg (not_lt.2 hs.le), if_neg (ne_of_gt hs)]
  have hdiv : (d : ℝ) / s ≤ 5 / 3 := by
    rw [div_le_iff₀ hspos]
    linarith
  rw [hfun, Real.sqrt_eq_rpow, ← Real.rpow_mul hN0.le, ← Real.rpow_add hN0]
  exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)

/-- `M:prose:L1198-1218` (TeX L1208-1213, "the two appearances of `2d/3`"): for `d/2 < s < d` the
mean translation `√N δ_N` and the averaged covariance discrepancy `δ_N` compare with the root-`N`
rate as follows: `δ_N → 0`; `√N δ_N → 0` for `s < 2d/3`, `√N δ_N = 1` for all `N ≥ 1` at `s = 2d/3`
(the exponent `3/2 - d/s` vanishes), and `√N δ_N → ∞` for `s > 2d/3`; `δ_N ≥ N^{-1/2}` exactly when
`s ≥ 2d/3`, i.e. `√N δ_N → ∞` iff `s > 2d/3` (the covariance discrepancy exceeds the root-`N` error
precisely when `s > 2d/3`, although it still tends to zero). -/
theorem deltaN_two_thirds (hd : 1 ≤ d) {s : ℝ} (hs1 : (d : ℝ) / 2 < s) (hsd : s < d) :
    Tendsto (fun N : ℕ => deltaN d s N) atTop (𝓝 0) ∧
    (s < 2 * (d : ℝ) / 3 → Tendsto (fun N : ℕ => Real.sqrt N * deltaN d s N) atTop (𝓝 0)) ∧
    (s = 2 * (d : ℝ) / 3 → ∀ N : ℕ, 1 ≤ N → Real.sqrt N * deltaN d s N = 1) ∧
    (2 * (d : ℝ) / 3 < s → Tendsto (fun N : ℕ => Real.sqrt N * deltaN d s N) atTop atTop) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hspos : 0 < s := by linarith
  have hs0 : 0 ≤ s := hspos.le
  have hfun : ∀ N : ℕ, deltaN d s N = (N : ℝ) ^ (1 - (d : ℝ) / s) := fun N => by
    unfold deltaN
    rw [if_neg (not_lt.2 hs1.le), if_neg (ne_of_gt hs1)]
  refine ⟨q35_delta_tendsto hd hs0 hsd, fun h2 => q35_sqrt_delta_tendsto hd hs0 h2, ?_, ?_⟩
  · intro h3 N hN
    have hN0 : (0 : ℝ) < N := Nat.cast_pos.2 (by omega)
    have hdiv : (d : ℝ) / s = 3 / 2 := by
      have hd0 : (0 : ℝ) < d := by linarith
      rw [h3]
      field_simp
    rw [hfun, Real.sqrt_eq_rpow, ← Real.rpow_add hN0]
    have h0 : (1 : ℝ) / 2 + (1 - (d : ℝ) / s) = 0 := by
      rw [hdiv]
      norm_num
    rw [h0, Real.rpow_zero]
  · intro h4
    have hlt : (d : ℝ) / s < 3 / 2 := (div_lt_iff₀ hspos).2 (by linarith)
    have hlim : Tendsto (fun N : ℕ => (N : ℝ) ^ (1 / 2 + (1 - (d : ℝ) / s))) atTop atTop :=
      (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (0 : ℝ) < N := Nat.cast_pos.2 (by omega)
    rw [hfun, Real.sqrt_eq_rpow, ← Real.rpow_add hN0]

/-! The initial independent-field errors `i_{N,m}`, `j_{N,m}` of `H:eq:iid-errors` (TeX L821-825,
`M:prose:L805-835`) are `HRS.iidRateSmooth`, `HRS.iidRateW` (`HRS/Sections/Sec5.lean`). -/

/-- The covariance of the initial Gaussian field for preparation `ℚ_{N,β₀}(μ°)` (TeX L813-819):
for independent data (`β₀ = 0`) the bridge covariance `Cov_{μ°}(φ,ψ) = μ°(φψ) - μ°(φ)μ°(ψ)`
(`iidCov`), for a Gibbs preparation `β₀ > 0` the prepared susceptibility
`⟨P_{μ°}φ, (I + β₀K_{μ°})^{-1}P_{μ°}ψ⟩_{L²(μ°)}` (`H:eq:prepared-susceptibility`,
`HRS.susceptibilityCov`; TeX L816-819, `K_μ f = P_μ[g*(fμ)]` is `HRS.Kop`). -/
def preparedCov (d : ℕ) (s β₀ : ℝ) (μ : Measure (Torus d)) (φ ψ : Torus d → ℝ) : ℝ :=
  if β₀ = 0 then iidCov μ φ ψ else susceptibilityCov (periodicRiesz d s) μ β₀ φ ψ

/-! #### Theorem 2.5 -/

/-- Theorem 2.5 `M:H:thm:prepared` (TeX L766-793), smooth and `W_1` bounds, uniform in the window
start.  Setting `PreparedData` (so `m > d + 2` real, `T < ∞`; `N ≥ 2` standing, TeX L420), the particle
system a `SelectedFlow` on `[0,a+T]` with `H(f_N^0 | Q_N^0) < ∞` (`f_N^0 = law P X₀`).  There are
`C_T, c > 0` independent of `N`, of the window start `a ≥ 0`, of the particle initial law and of the
prescribed initial field (the constants are chosen before them) such that, whenever
`a_{N,1} < ∞` ("whenever the displayed initial moments are finite"),
`d_2^{𝒳_{m,T}}(η_N^{a+·}, Y^{a+·}) ≤ C_T(e^{-ca}a_{N,1} + B_N/√N + √(B_N/N))` (`H:eq:prepared-smooth`),
`W_1 ≤ C_T(e^{-ca}a_{N,1} + B_N/√N + (B_N/N)^{1/4})` (`H:eq:prepared-W1`), and, as a separate bound
(TeX L781-782), `d_2 ≤ C_T(d_2^{E_m}(η_N^0, η°) + B_N/√N + √(B_N/N))`.
(`Y` is any solution with initial law `ν`, `IsPreparedLinear`.)
Technical hypotheses: none beyond `N ≥ 2` and `T > 0`.  The `W_2` bound with the extra moment
(`H:eq:prepared-W2`) is `prepared_fluctuations_W2`.

Statement repair (ISSUES.md, entry "Statement sweep repairs (ADAPTSPEC3)"): the proof rests on Theorem 2.1 and the duality identity `B:prop:duality-identity`, whose Itô calculus needs a Brownian filtration, so `X` is assumed a filtered strong solution (`∃ ℱ W', IsFilteredSolution P ℱ W' W X`, the strong-solution adaptedness of A.1 that `SelectedFlow` records only as measurability, ISSUES D1). -/
theorem prepared_fluctuations (S : PreparedData d) (m : ℝ) (hm : (d : ℝ) + 2 < m) (T : ℝ)
    (hT : 0 < T) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ a : ℝ, 0 ≤ a → ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        SelectedFlow P S.dyn (a + T) X₀ W X →
        (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
          (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X) →
        relEntropy (law P X₀) (S.refMeasure N 0) < ⊤ →
      ∀ (ν : Measure (NegSobolev d m)) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
        [IsProbabilityMeasure P'] (Y₀ : Ω' → NegSobolev d m) (Y : ℝ → Ω' → NegSobolev d m),
        IsPreparedLinear S m (a + T) ν P' Y₀ Y →
        (S.initW m 1 P X₀ ν ≠ ⊤ →
          smoothDist 2 (S.etaLaw m T a P X) (law P' (windowPath m T a Y)) ≤
            C * (Real.exp (-c * a) * (S.initW m 1 P X₀ ν).toReal +
              S.B N (law P X₀) / Real.sqrt N + Real.sqrt (S.B N (law P X₀) / N)) ∧
          wassersteinE 1 (S.etaLaw m T a P X) (law P' (windowPath m T a Y)) ≤
            ENNReal.ofReal (C * (Real.exp (-c * a) * (S.initW m 1 P X₀ ν).toReal +
              S.B N (law P X₀) / Real.sqrt N +
              (S.B N (law P X₀) / N) ^ ((1 : ℝ) / 4)))) ∧
        smoothDist 2 (S.etaLaw m T a P X) (law P' (windowPath m T a Y)) ≤
          C * (smoothDist 2 (law P (fun ω => etaE m (X₀ ω) S.μ0)) ν +
            S.B N (law P X₀) / Real.sqrt N + Real.sqrt (S.B N (law P X₀) / N)) := by
  sorry

/-- Theorem 2.5 `M:H:thm:prepared` (TeX L783-793), the `W_2` bound `H:eq:prepared-W2`: if, for some
fixed `p₀ > 1`, `h_N^0 = df_N^0/dQ_N^0 ∈ L^{p₀}(Q_N^0)`, then with `J_N` of `H:eq:strong-bound` and
`a_{N,2} < ∞`,
`W_2^{𝒳_{m,T}}(η_N^{a+·}, Y^{a+·}) ≤ C_T(e^{-ca}a_{N,2} + J_N/√N + (B_N/N)^{1/4})`.
**AMBIGUITY** (TeX L769, L783): the constants `C_T, c` are those of the whole theorem; here they
are chosen after `p₀` (a priori they may depend on `p₀`, which the TeX calls "fixed").

Statement repair (ISSUES.md, entry "Statement sweep repairs (ADAPTSPEC3)"): the proof rests on Theorem 2.1 and the duality identity `B:prop:duality-identity`, whose Itô calculus needs a Brownian filtration, so `X` is assumed a filtered strong solution (`∃ ℱ W', IsFilteredSolution P ℱ W' W X`, the strong-solution adaptedness of A.1 that `SelectedFlow` records only as measurability, ISSUES D1). -/
theorem prepared_fluctuations_W2 (S : PreparedData d) (m : ℝ) (hm : (d : ℝ) + 2 < m) (T : ℝ)
    (hT : 0 < T) (p₀ : ℝ) (hp₀ : 1 < p₀) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ a : ℝ, 0 ≤ a → ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        SelectedFlow P S.dyn (a + T) X₀ W X →
        (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
          (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X) →
        relEntropy (law P X₀) (S.refMeasure N 0) < ⊤ →
        MemLp (fun Y => (((law P X₀).rnDeriv (S.refMeasure N 0)) Y).toReal) (ENNReal.ofReal p₀)
          (S.refMeasure N 0) →
      ∀ (ν : Measure (NegSobolev d m)) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
        [IsProbabilityMeasure P'] (Y₀ : Ω' → NegSobolev d m) (Y : ℝ → Ω' → NegSobolev d m),
        IsPreparedLinear S m (a + T) ν P' Y₀ Y →
        S.initW m 2 P X₀ ν ≠ ⊤ →
          wassersteinE 2 (S.etaLaw m T a P X) (law P' (windowPath m T a Y)) ≤
            ENNReal.ofReal (C * (Real.exp (-c * a) * (S.initW m 2 P X₀ ν).toReal +
              S.J N (law P X₀) p₀ / Real.sqrt N +
              (S.B N (law P X₀) / N) ^ ((1 : ℝ) / 4))) := by
  sorry

/-- Theorem 2.5 `M:H:thm:prepared` (TeX L795-801), the last paragraph, for the preparation
`ℚ_{N,β₀}(μ°)`, `β₀ ≥ 0` (including independent sampling `β₀ = 0`): the initial law `f_N^0` has
finite entropy relative to `Q_N^0` and `B_N ≤ C Nδ_N`; moreover, when `β₀ > 0`, and also at `β₀ = 0`
for `s = 0`, there is `p₀ > 1` with `h_N^0 ∈ L^{p₀}(Q_N^0)` and `J_N ≤ C Nδ_N`
(the proof, TeX L6748-6760, chooses `p₀` close to one). -/
theorem prepared_scales (S : PreparedData d) (β₀ : ℝ) (hβ₀ : 0 ≤ β₀) :
    (∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
      relEntropy (modulatedGibbs (periodicRiesz d S.s) N β₀ S.μ0) (S.refMeasure N 0) < ⊤ ∧
      S.B N (modulatedGibbs (periodicRiesz d S.s) N β₀ S.μ0) ≤ C * ((N : ℝ) * deltaN d S.s N)) ∧
    ((0 < β₀ ∨ S.s = 0) →
      ∃ p₀ : ℝ, 1 < p₀ ∧ ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
        MemLp (fun Y => (((modulatedGibbs (periodicRiesz d S.s) N β₀ S.μ0).rnDeriv
            (S.refMeasure N 0)) Y).toReal) (ENNReal.ofReal p₀) (S.refMeasure N 0) ∧
        S.J N (modulatedGibbs (periodicRiesz d S.s) N β₀ S.μ0) p₀ ≤ C * ((N : ℝ) * deltaN d S.s N)) := by
  sorry

/-! #### `M:prose:L805-835`: full path bounds with an initial Gaussian -/

/-- `M:prose:L805-835` (TeX L812-834): the full path bounds for the standard preparations
`ℚ_{N,β₀}(μ°)`, `m > d + 2`, in which the prescribed initial field `η°` is the Gaussian `ν` with
covariance `preparedCov` (bridge for `β₀ = 0`, prepared susceptibility for `β₀ > 0`), each uniform in
the window start `a ≥ 0`:
(i) independent data (`β₀ = 0`): smooth `C_T(√Nδ_N + i_{N,m})`, `W_1`: `C_T(√Nδ_N + δ_N^{1/4} + j_{N,m})`;
(ii) Gibbs preparation (`β₀ > 0`): smooth `C_T√Nδ_N`, `W_2`: `C_T(√Nδ_N + δ_N^{1/4})`;
(iii) independent logarithmic data (`β₀ = 0`, `s = 0`): `W_2`: `C_T(N^{-1/4} + j_{N,m}^{1/3})`.
(The initial rates are "sufficient and not claimed optimal", TeX L833-834; no `W_2` bound is claimed
for independent positive-power data, TeX L891-902.)  The first marginal of the preparation is the
actual particle initial law, `law P X₀ = ℚ_{N,β₀}(μ°)`.

Statement repair (ISSUES.md, entry "Statement sweep repairs (ADAPTSPEC3)"): the proof is Theorem 2.5 (hence Theorem 2.1 and the duality identity) applied to the standard preparations, whose Itô calculus needs a Brownian filtration, so `X` is assumed a filtered strong solution (`∃ ℱ W', IsFilteredSolution P ℱ W' W X`, the strong-solution adaptedness of A.1 that `SelectedFlow` records only as measurability, ISSUES D1). -/
theorem prepared_full_bounds (S : PreparedData d) (m : ℝ) (hm : (d : ℝ) + 2 < m) (T : ℝ)
    (hT : 0 < T) (β₀ : ℝ) (hβ₀ : 0 ≤ β₀) :
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
        (Y₀ : Ω' → NegSobolev d m) (Y : ℝ → Ω' → NegSobolev d m),
        IsPreparedLinear S m (a + T) ν P' Y₀ Y →
        (β₀ = 0 →
          smoothDist 2 (S.etaLaw m T a P X) (law P' (windowPath m T a Y)) ≤
            C * (Real.sqrt N * deltaN d S.s N + iidRateSmooth d m N) ∧
          wassersteinE 1 (S.etaLaw m T a P X) (law P' (windowPath m T a Y)) ≤
            ENNReal.ofReal (C * (Real.sqrt N * deltaN d S.s N +
              deltaN d S.s N ^ ((1 : ℝ) / 4) + iidRateW d m N))) ∧
        (0 < β₀ →
          smoothDist 2 (S.etaLaw m T a P X) (law P' (windowPath m T a Y)) ≤
            C * (Real.sqrt N * deltaN d S.s N) ∧
          wassersteinE 2 (S.etaLaw m T a P X) (law P' (windowPath m T a Y)) ≤
            ENNReal.ofReal (C * (Real.sqrt N * deltaN d S.s N +
              deltaN d S.s N ^ ((1 : ℝ) / 4)))) ∧
        (β₀ = 0 → S.s = 0 →
          wassersteinE 2 (S.etaLaw m T a P X) (law P' (windowPath m T a Y)) ≤
            ENNReal.ofReal (C * ((N : ℝ) ^ (-(1 : ℝ) / 4) + iidRateW d m N ^ ((1 : ℝ) / 3)))) := by
  sorry

/-! #### Example 2.6 -/

/-- The non-Gaussian mixture preparation of Example 2.6 (TeX L836-847): with probability `1/2`
(`U = +1`) resp. `1/2` (`U = -1`) the `N` particles are sampled independently from
`(1 + a₀ U b/√N) μ°` resp. `(1 - a₀ b/√N) μ°` (`U` a fair random sign).  Only meaningful for `N` so
large that the densities are positive. -/
def mixturePrep (μ : Measure (Torus d)) (b : Torus d → ℝ) (a₀ : ℝ) (N : ℕ) :
    Measure (Config d N) :=
  (1 / 2 : ℝ≥0∞) • Measure.pi (fun _ : Fin N =>
      μ.withDensity fun x => ENNReal.ofReal (1 + a₀ * b x / Real.sqrt N)) +
    (1 / 2 : ℝ≥0∞) • Measure.pi (fun _ : Fin N =>
      μ.withDensity fun x => ENNReal.ofReal (1 - a₀ * b x / Real.sqrt N))

/-- Example 2.6 `M:H:ex:mixture` (TeX L836-847, `H:eq:mixture-limit`): `b` a fixed smooth (hence
bounded) function with `μ°(b) = 0`, `a₀ ∈ ℝ`.  For every `N ≥ 1` with `|a₀ b| < √N` (the densities are
positive) the unconditional first marginal of `mixturePrep` is exactly `μ°` (and the mixture is a
probability measure), whereas for `m > d/2` the law of `η_N^0 = √N(μ_N^0 - μ°)` in `E_m` converges
weakly (`ConvergesInLaw`) to the law of `G_{μ°} + a₀ U b μ°`: the equal mixture of the translates by
`±a₀ bμ°` of a centered Gaussian `γ` with the bridge covariance `iidCov μ°` (`G_{μ°}` independent of
`U`). -/
theorem mixture_limit (S : PreparedData d) (b : Torus d → ℝ) (hb : Torus.IsSmooth b)
    (hb0 : pair S.μ0 b = 0) (a₀ : ℝ) (m : ℝ) (hm : (d : ℝ) / 2 < m)
    (γ : Measure (NegSobolev d m)) (hγ : IsCenteredGaussianWithCov m γ (iidCov S.μ0)) :
    (∀ N : ℕ, 1 ≤ N → (∀ x, |a₀ * b x| < Real.sqrt N) →
      IsProbabilityMeasure (mixturePrep S.μ0 b a₀ N) ∧
        firstMarginal (mixturePrep S.μ0 b a₀ N) = S.μ0) ∧
    ConvergesInLaw
      (fun N : ℕ => law (mixturePrep S.μ0 b a₀ N) (fun X => etaE m X S.μ0))
      ((1 / 2 : ℝ≥0∞) • γ.map (fun F => F + a₀ • NegSobolev.ofFun m (fun x => b x * S.ρ0 x)) +
        (1 / 2 : ℝ≥0∞) • γ.map (fun F => F - a₀ • NegSobolev.ofFun m (fun x => b x * S.ρ0 x))) := by
  sorry

/-- Example 2.6 `M:H:ex:mixture` (TeX L848-852): "the prepared theorem and the same initial
smooth/`W_1` bounds propagate this non-Gaussian initial field for `s < 2d/3`; independent logarithmic
preparation also gives the stated `W_2` bound".  For the mixture preparation (`N ≥ max{2, 4a₀²‖b‖²_∞}`, `‖b‖_∞ = ⨆ x, |b x|`, the condition of Prop 5.9, TeX L6799-6800;
Proposition 5.9, TeX L6781-6800, gives the initial bounds), `Y` with the initial law `ν_mix`
(the limit of `mixture_limit`): `d_2 ≤ C_T(√Nδ_N + i_{N,m})`, `W_1 ≤ C_T(√Nδ_N + δ_N^{1/4} + j_{N,m})`,
and for `s = 0` `W_2 ≤ C_T(N^{-1/4} + j_{N,m}^{1/3})`, uniformly in the window start.

Statement repair (ISSUES.md, entry "Statement sweep repairs (ADAPTSPEC3)"): the proof is Theorem 2.5 (hence Theorem 2.1 and the duality identity) applied to the mixture preparation, whose Itô calculus needs a Brownian filtration, so `X` is assumed a filtered strong solution (`∃ ℱ W', IsFilteredSolution P ℱ W' W X`, the strong-solution adaptedness of A.1 that `SelectedFlow` records only as measurability, ISSUES D1). -/
theorem mixture_full_bounds (S : PreparedData d) (m : ℝ) (hm : (d : ℝ) + 2 < m) (T : ℝ)
    (hT : 0 < T) (b : Torus d → ℝ) (hb : Torus.IsSmooth b) (hb0 : pair S.μ0 b = 0) (a₀ : ℝ)
    (γ : Measure (NegSobolev d m)) (hγ : IsCenteredGaussianWithCov m γ (iidCov S.μ0)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ a : ℝ, 0 ≤ a → ∀ N : ℕ, 2 ≤ N → 4 * a₀ ^ 2 * (⨆ x, |b x|) ^ 2 ≤ (N : ℝ) →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        SelectedFlow P S.dyn (a + T) X₀ W X →
        (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
          (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X) →
        law P X₀ = mixturePrep S.μ0 b a₀ N →
      ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
        (Y₀ : Ω' → NegSobolev d m) (Y : ℝ → Ω' → NegSobolev d m),
        IsPreparedLinear S m (a + T)
          ((1 / 2 : ℝ≥0∞) • γ.map (fun F => F + a₀ • NegSobolev.ofFun m (fun x => b x * S.ρ0 x)) +
            (1 / 2 : ℝ≥0∞) • γ.map (fun F => F - a₀ • NegSobolev.ofFun m (fun x => b x * S.ρ0 x)))
          P' Y₀ Y →
        smoothDist 2 (S.etaLaw m T a P X) (law P' (windowPath m T a Y)) ≤
          C * (Real.sqrt N * deltaN d S.s N + iidRateSmooth d m N) ∧
        wassersteinE 1 (S.etaLaw m T a P X) (law P' (windowPath m T a Y)) ≤
          ENNReal.ofReal (C * (Real.sqrt N * deltaN d S.s N + deltaN d S.s N ^ ((1 : ℝ) / 4) +
            iidRateW d m N)) ∧
        (S.s = 0 →
          wassersteinE 2 (S.etaLaw m T a P X) (law P' (windowPath m T a Y)) ≤
            ENNReal.ofReal (C * ((N : ℝ) ^ (-(1 : ℝ) / 4) + iidRateW d m N ^ ((1 : ℝ) / 3)))) := by
  sorry

/-! #### Corollary 2.7 -/

/-- Corollary 2.7 `M:H:cor:thermalization` (TeX L855-868), thermalization with the evolving center.
Under Theorem 2.5 (same setting; `Z` is the stationary linear Gaussian field `Z_β` of the next
subsection (`IsStationaryGaussianField`, thermal density `ρβ` of `(V,β)`), on its own probability space; its
window law is the law of `Z` on `𝒳_{m,T}`): there are `C_T, c > 0` such that
`W_1(η_N^{a+·}, Z_β) ≤ C_T(B_N/√N + (B_N/N)^{1/4} + e^{-ca}(1 + ‖η_N^0‖_{L^1(E_m)}))`
(`H:eq:thermalization`), the smooth estimate replaces the quarter power by `√(B_N/N)`, and, if
`h_N^0 ∈ L^{p₀}(Q_N^0)`, the `W_2` estimate uses `J_N/√N` and the initial `L²(E_m)` norm
`(E‖η_N^0‖²)^{1/2}`.  Norms of `η_N^0` are `lintegral`s (the bound is vacuous if infinite), so the
right-hand sides live in `ℝ≥0∞`.

Statement repair (ISSUES.md, entry "Statement sweep repairs (ADAPTSPEC3)"): the proof is Theorem 2.5 (hence Theorem 2.1 and the duality identity) plus the stationary comparison, whose Itô calculus needs a Brownian filtration, so `X` is assumed a filtered strong solution (`∃ ℱ W', IsFilteredSolution P ℱ W' W X`, the strong-solution adaptedness of A.1 that `SelectedFlow` records only as measurability, ISSUES D1). -/
theorem thermalization (S : PreparedData d) (m : ℝ) (hm : (d : ℝ) + 2 < m) (T : ℝ) (hT : 0 < T)
    (ρβ : Torus d → ℝ) (hρβ : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ a : ℝ, 0 ≤ a → ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        SelectedFlow P S.dyn (a + T) X₀ W X →
        (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
          (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X) →
        relEntropy (law P X₀) (S.refMeasure N 0) < ⊤ →
      ∀ {Ω'' : Type} [MeasurableSpace Ω''] (P'' : Measure Ω'') [IsProbabilityMeasure P'']
        (Z : ℝ → Ω'' → NegSobolev d m), IsStationaryGaussianField P'' S.s S.β S.hs0 S.hsd S.hβ S.V ρβ m Z →
        ENNReal.ofReal (smoothDist 2 (S.etaLaw m T a P X) (law P'' (windowPath m T 0 Z))) ≤
          ENNReal.ofReal (C * (S.B N (law P X₀) / Real.sqrt N +
              Real.sqrt (S.B N (law P X₀) / N))) +
            ENNReal.ofReal (C * Real.exp (-c * a)) *
              (1 + ∫⁻ ω, ‖etaE m (X₀ ω) S.μ0‖ₑ ∂P) ∧
        wassersteinE 1 (S.etaLaw m T a P X) (law P'' (windowPath m T 0 Z)) ≤
          ENNReal.ofReal (C * (S.B N (law P X₀) / Real.sqrt N +
              (S.B N (law P X₀) / N) ^ ((1 : ℝ) / 4))) +
            ENNReal.ofReal (C * Real.exp (-c * a)) *
              (1 + ∫⁻ ω, ‖etaE m (X₀ ω) S.μ0‖ₑ ∂P) := by
  sorry

/-- Corollary 2.7 `M:H:cor:thermalization` (TeX L865-866), the `W_2` estimate under
`H:eq:strong-bound`.

Statement repair (ISSUES.md, entry "Statement sweep repairs (ADAPTSPEC3)"): the proof is Theorem 2.5 (hence Theorem 2.1 and the duality identity) plus the stationary comparison, whose Itô calculus needs a Brownian filtration, so `X` is assumed a filtered strong solution (`∃ ℱ W', IsFilteredSolution P ℱ W' W X`, the strong-solution adaptedness of A.1 that `SelectedFlow` records only as measurability, ISSUES D1). -/
theorem thermalization_W2 (S : PreparedData d) (m : ℝ) (hm : (d : ℝ) + 2 < m) (T : ℝ)
    (hT : 0 < T) (ρβ : Torus d → ℝ) (hρβ : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ)
    (p₀ : ℝ) (hp₀ : 1 < p₀) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ a : ℝ, 0 ≤ a → ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        SelectedFlow P S.dyn (a + T) X₀ W X →
        (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
          (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X) →
        relEntropy (law P X₀) (S.refMeasure N 0) < ⊤ →
        MemLp (fun Y => (((law P X₀).rnDeriv (S.refMeasure N 0)) Y).toReal) (ENNReal.ofReal p₀)
          (S.refMeasure N 0) →
      ∀ {Ω'' : Type} [MeasurableSpace Ω''] (P'' : Measure Ω'') [IsProbabilityMeasure P'']
        (Z : ℝ → Ω'' → NegSobolev d m), IsStationaryGaussianField P'' S.s S.β S.hs0 S.hsd S.hβ S.V ρβ m Z →
        wassersteinE 2 (S.etaLaw m T a P X) (law P'' (windowPath m T 0 Z)) ≤
          ENNReal.ofReal (C * (S.J N (law P X₀) p₀ / Real.sqrt N +
              (S.B N (law P X₀) / N) ^ ((1 : ℝ) / 4))) +
            ENNReal.ofReal (C * Real.exp (-c * a)) *
              (1 + (∫⁻ ω, ‖etaE m (X₀ ω) S.μ0‖ₑ ^ (2 : ℝ) ∂P) ^ ((1 : ℝ) / 2)) := by
  sorry

/-- Corollary 2.7 `M:H:cor:thermalization` (TeX L866-868): "for the stated standard preparations in
`s < 2d/3` these initial norms are uniformly bounded where required": for `0 ≤ s < 2d/3`, `m > d + 2`
and every `β₀ ≥ 0`, the initial `L¹(E_m)` norms `E‖η_N^0‖_{E_m}` of the preparation
`ℚ_{N,β₀}(μ°)` are bounded uniformly in `N ≥ 2`, and so are the `L²` norms when `β₀ > 0` or `s = 0`
(the cases of the strong bound `J_N ≤ C Nδ_N`, `prepared_scales`). -/
theorem standard_preparation_norms (S : PreparedData d) (hs : S.s < 2 * (d : ℝ) / 3) (m : ℝ)
    (hm : (d : ℝ) + 2 < m) (β₀ : ℝ) (hβ₀ : 0 ≤ β₀) :
    ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
      (∫⁻ X, ‖etaE m X S.μ0‖ₑ ∂(modulatedGibbs (periodicRiesz d S.s) N β₀ S.μ0)) ≤
        ENNReal.ofReal C ∧
      ((0 < β₀ ∨ S.s = 0) →
        (∫⁻ X, ‖etaE m X S.μ0‖ₑ ^ (2 : ℝ) ∂(modulatedGibbs (periodicRiesz d S.s) N β₀ S.μ0)) ≤
          ENNReal.ofReal C) := by
  sorry

/-- Corollary 2.7 `M:H:cor:thermalization` (TeX L868-869): "every `a_N → ∞` gives the corresponding
stationary-window limit".  For `0 ≤ s < 2d/3`, `m > d + 2`, `β₀ ≥ 0`, particle systems `X_N` started
from `ℚ_{N,β₀}(μ°)` on windows starting at `a_N → ∞`: `d_2`, `W_1` (and `W_2` for `β₀ > 0` or `s = 0`)
between `η_N^{a_N+·}` and `Z_β` tend to `0`.

Statement repair (ISSUES.md, entry "Statement sweep repairs (ADAPTSPEC3)"): the limit follows from the quantitative Corollary 2.7 / Theorem 2.5 (Itô/duality calculus), so each `X N` (`N ≥ 2`) is assumed a filtered strong solution (`hfilt`, `IsFilteredSolution`). -/
theorem thermalization_limit (S : PreparedData d) (hs : S.s < 2 * (d : ℝ) / 3) (m : ℝ)
    (hm : (d : ℝ) + 2 < m) (T : ℝ) (hT : 0 < T) (ρβ : Torus d → ℝ) (hρβ : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ)
    (β₀ : ℝ) (hβ₀ : 0 ≤ β₀)
    (a : ℕ → ℝ) (ha0 : ∀ N, 0 ≤ a N) (ha : Tendsto a atTop atTop)
    (Ω : ℕ → Type) [∀ N, MeasurableSpace (Ω N)] (P : ∀ N, Measure (Ω N))
    [∀ N, IsProbabilityMeasure (P N)]
    (X₀ : ∀ N, Ω N → Config d N) (W : ∀ N, ℝ≥0 → Ω N → (Fin N → Euc d))
    (X : ∀ N, ℝ≥0 → Ω N → Config d N)
    (hflow : ∀ N : ℕ, 2 ≤ N → SelectedFlow (P N) S.dyn (a N + T) (X₀ N) (W N) (X N))
    (hfilt : ∀ N : ℕ, 2 ≤ N → ∃ (ℱ : MeasureTheory.Filtration ℝ (inferInstance : MeasurableSpace (Ω N)))
      (W' : ℝ≥0 → Ω N → (Fin N × Fin d) → ℝ), IsFilteredSolution (P N) ℱ W' (W N) (X N))
    (hinit : ∀ N : ℕ, 2 ≤ N →
      law (P N) (X₀ N) = modulatedGibbs (periodicRiesz d S.s) N β₀ S.μ0)
    {Ω'' : Type} [MeasurableSpace Ω''] (P'' : Measure Ω'') [IsProbabilityMeasure P'']
    (Z : ℝ → Ω'' → NegSobolev d m) (hZ : IsStationaryGaussianField P'' S.s S.β S.hs0 S.hsd S.hβ S.V ρβ m Z) :
    Tendsto (fun N : ℕ => smoothDist 2 (S.etaLaw m T (a N) (P N) (X N))
        (law P'' (windowPath m T 0 Z))) atTop (𝓝 0) ∧
      Tendsto (fun N : ℕ => wassersteinE 1 (S.etaLaw m T (a N) (P N) (X N))
        (law P'' (windowPath m T 0 Z))) atTop (𝓝 0) ∧
      ((0 < β₀ ∨ S.s = 0) →
        Tendsto (fun N : ℕ => wassersteinE 2 (S.etaLaw m T (a N) (P N) (X N))
          (law P'' (windowPath m T 0 Z))) atTop (𝓝 0)) := by
  sorry

/-- Corollary 2.7 `M:H:cor:thermalization` (TeX L869-870): replacing the evolving center `μ^{a+t}` by
`μ_β` (`ρβ`) in the field adds at most the deterministic error
`√N sup_{t≤T}‖μ^{a+t} - μ_β‖_{E_m}` to the distance to any target law (stated for `d_2`, `W_1`,
`W_2`, with the sup in `ℝ≥0∞`).

Statement repair THERM-R (ISSUES.md, 2026-10-17, reviewed ACCEPT WITH NOTES): `hm : d/2 < m` added. For `m ≤ d/2`
the embedding of measures into `E_m` is the junk value (`NegSobolev.ofSeq` of a non-`ℓ²` sequence is `0`), so the
statement degenerated. The TeX works in the `E_m` setting `m > d + 2`, which implies `hm`. -/
theorem thermalization_recentered (S : PreparedData d) (m : ℝ) (hm : (d : ℝ) / 2 < m) (T : ℝ) (hT : 0 < T)
    (ρβ : Torus d → ℝ) (hρβ : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) (a : ℝ) (ha : 0 ≤ a) (N : ℕ) (hN : 2 ≤ N)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (hflow : SelectedFlow P S.dyn (a + T) X₀ W X)
    (Q : Measure (PathSpace d m T)) [IsProbabilityMeasure Q] :
    let shift : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt N) *
      ⨆ t : Set.Icc (0 : ℝ) T, ‖NegSobolev.ofMeasureDiff m (withDensityReal (S.ρ (a + t)))
        (withDensityReal ρβ)‖ₑ
    let recentered := law P (windowFluc m T a (Real.sqrt N) X (fun _ => ρβ))
    ENNReal.ofReal (smoothDist 2 recentered Q) ≤
      ENNReal.ofReal (smoothDist 2 (S.etaLaw m T a P X) Q) + shift ∧
    wassersteinE 1 recentered Q ≤ wassersteinE 1 (S.etaLaw m T a P X) Q + shift ∧
    wassersteinE 2 recentered Q ≤ wassersteinE 2 (S.etaLaw m T a P X) Q + shift := by
  sorry

/-! ### `M:@remark:L891`: the positive-power independent-data `W_2` problem -/

/-- `M:@remark:L891` (TeX L895-897): "an inverse-Gibbs `L^{1+ε}` density moment is infinite for every
`s > 0`, because a colliding pair produces an attractive exponential `exp(c/(N|x-y|^s))`":
for `d ≥ 2`, `0 < s < d`, `β > 0`, a smooth positive density `ρ`, `N ≥ 2` and `ε > 0`,
`∫ (d(μ^{⊗N})/dℚ_{N,β}(μ))^{1+ε} dℚ_{N,β}(μ) = ∞`.  (The second claim of the remark, that the
instantaneous symmetrized commutator is not square integrable at `s = d/2`, is Proposition 7.17,
`HRS.localDiv_critical`; the open problem itself is not a statement.) -/
theorem inverse_gibbs_moment_infinite (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 < s) (hsd : s < d)
    (β : ℝ) (hβ : 0 < β) {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) (N : ℕ) (hN : 2 ≤ N)
    (ε : ℝ) (hε : 0 < ε) :
    ∫⁻ X, ((Measure.pi fun _ : Fin N => withDensityReal ρ).rnDeriv
        (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) X) ^ (1 + ε)
      ∂(modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) = ⊤ :=
  q42_gibbs_moment hd hs0 hsd β hβ hρ N hN ε hε


/-! ### Existence of the objects the statements quantify over -/

/-- Existence of a solution of the linear equation `H:eq:linear-equation` with `q = β⁻¹` and prescribed
initial law `ν` on `E_m` (`IsPreparedLinear`), `m > d + 2`, on every horizon `T' > 0` (source:
Proposition A.33 `M:prop:periodic-limit-field`, TeX L11310-11318, with the adjoint estimates of
Propositions 5.1-5.2).  Stated so that the statements about `Y`, `Z` are not vacuous. -/
theorem preparedLinear_exists (S : PreparedData d) (m : ℝ) (hm : (d : ℝ) + 2 < m) (T' : ℝ)
    (hT' : 0 < T') (ν : Measure (NegSobolev d m)) [IsProbabilityMeasure ν] :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (_ : IsProbabilityMeasure P')
      (Y₀ : Ω' → NegSobolev d m) (Y : ℝ → Ω' → NegSobolev d m),
      IsPreparedLinear S m T' ν P' Y₀ Y := by
  sorry

/-- Existence of the initial Gaussian field of `preparedCov` (bridge for `β₀ = 0`, prepared
susceptibility for `β₀ > 0`) on `E_m`, `m > d/2` (source: Proposition 5.9 / `HRS.exists_iid_gaussian_field`
for `β₀ = 0`; TeX L813-819, `HRS.exists_unique_response` for the susceptibility). -/
theorem preparedGaussian_exists (S : PreparedData d) (β₀ : ℝ) (hβ₀ : 0 ≤ β₀) (m : ℝ)
    (hm : (d : ℝ) / 2 < m) :
    ∃ ν : Measure (NegSobolev d m), IsProbabilityMeasure ν ∧
      IsCenteredGaussianWithCov m ν (preparedCov d S.s β₀ S.μ0) := by
  sorry

/-! ### Remaining claims of the prose rows -/

/-- `M:prose:L1396-1420` (TeX L1397-1399): "for fixed `N`, the periodic empirical field is bounded by a
deterministic multiple of `√N` in that norm": for `m > d/2` there is `C` with
`‖√N(μ_N - μ)‖_{E_m} ≤ C√N` for every `N`, every configuration and every probability measure `μ`. -/
theorem empirical_field_deterministic_bound (hd : 1 ≤ d) (m : ℝ) (hm : (d : ℝ) / 2 < m) :
    ∃ C : ℝ, ∀ (N : ℕ) (X : Config d N) (μ : Measure (Torus d)) [IsProbabilityMeasure μ],
      ‖etaE m X μ‖ ≤ C * Real.sqrt N := by
  have hdm : (d : ℝ) < 2 * m := by linarith
  refine ⟨Real.sqrt (∑' k : NonzeroLattice d, 8 * Lattice.jp k.1 ^ (-(2 * m))), fun N X μ _ => ?_⟩
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [etaE, flucE]
  haveI : IsProbabilityMeasure (empirical X) := empirical_isProbabilityMeasure hN X
  have hbound : ∀ k : NonzeroLattice d,
      |Torus.measureRealCoeff (empirical X) k - Torus.measureRealCoeff μ k| ≤ 2 * Real.sqrt 2 := by
    intro k
    have h1 := Torus.abs_measureRealCoeff_le (empirical X) k
    have h2 := Torus.abs_measureRealCoeff_le μ k
    simp only [measure_univ, ENNReal.toReal_one, mul_one] at h1 h2
    calc _ ≤ |Torus.measureRealCoeff (empirical X) k| + |Torus.measureRealCoeff μ k| := abs_sub _ _
      _ ≤ Real.sqrt 2 + Real.sqrt 2 := add_le_add h1 h2
      _ = 2 * Real.sqrt 2 := by ring
  set F : NegSobolev d m := NegSobolev.ofMeasureDiff m (empirical X) μ with hF
  have hmem : Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m) *
      (Torus.measureRealCoeff (empirical X) k - Torus.measureRealCoeff μ k)) 2 :=
    NegSobolev.memℓp_of_bounded hdm _ ⟨_, hbound⟩
  have hcoord : ∀ k : NonzeroLattice d, NegSobolev.coord F k =
      Lattice.jp k.1 ^ (-m) * (Torus.measureRealCoeff (empirical X) k - Torus.measureRealCoeff μ k) :=
    fun k => NegSobolev.coord_ofSeq_of_mem _ hmem k
  have hsq : ‖F‖ ^ 2 ≤ ∑' k : NonzeroLattice d, 8 * Lattice.jp k.1 ^ (-(2 * m)) := by
    rw [(NegSobolev.coord_sq F).2]
    refine Summable.tsum_le_tsum (fun k => ?_) (NegSobolev.coord_sq F).1
      ((summable_jp_rpow m hdm).mul_left 8)
    rw [hcoord k, mul_pow, Torus.jp_rpow_sq]
    have ha : (Torus.measureRealCoeff (empirical X) k - Torus.measureRealCoeff μ k) ^ 2 ≤ 8 := by
      have h0 := hbound k
      have h3 : |Torus.measureRealCoeff (empirical X) k - Torus.measureRealCoeff μ k| ^ 2 ≤
          (2 * Real.sqrt 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h0 2
      rw [sq_abs, mul_pow, Real.sq_sqrt (by norm_num)] at h3
      linarith
    have hj : (0 : ℝ) ≤ Lattice.jp k.1 ^ (2 * -m) := (Real.rpow_nonneg (Torus.jp_pos k.1).le _)
    rw [show 2 * -m = -(2 * m) by ring] at hj ⊢
    nlinarith
  have hF' : ‖F‖ ≤ Real.sqrt (∑' k : NonzeroLattice d, 8 * Lattice.jp k.1 ^ (-(2 * m))) := by
    calc ‖F‖ = Real.sqrt (‖F‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ _ := Real.sqrt_le_sqrt hsq
  unfold etaE flucE
  rw [norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_comm]
  exact mul_le_mul_of_nonneg_right hF' (Real.sqrt_nonneg _)

/-- `M:H:prop:field-singularity` follow-up (TeX L730-731, "the same separation passes to path laws by
evaluation at one time"): mutual singularity of the laws of two random elements of `E` passes to any
law whose pushforward by a measurable map is one of them.  General form: if the pushforwards of `P, Q`
by a measurable `f` are mutually singular then `P ⟂ₘ Q`. -/
theorem mutuallySingular_of_map {E F : Type*} [MeasurableSpace E] [MeasurableSpace F] (f : E → F)
    (hf : Measurable f) (P Q : Measure E) (h : P.map f ⟂ₘ Q.map f) : P ⟂ₘ Q := by
  obtain ⟨s, hs, h1, h2⟩ := h
  refine ⟨f ⁻¹' s, hf hs, ?_, ?_⟩
  · rw [← Measure.map_apply hf hs]; exact h1
  · rw [← Set.preimage_compl, ← Measure.map_apply hf hs.compl]; exact h2

/-- Path-space form of Proposition 2.4 (TeX L730-731): let `Γ` be a law on `𝒳_{m,T}`, `m > d/2`, whose
time-`t` marginal is a centered Gaussian `γ` with `L²`-comparable covariance (the susceptibility Gaussian
has this property), and `Q` a law on `𝒳_{m,T}` whose time-`t` marginal is the law of
`√N(μ_N - ν_N)` (`μ_N` the empirical measure under the particle law `P`).  Then `Γ ⟂ₘ Q`, so the path laws
are mutually singular for every finite `N`. -/
theorem field_singularity_path (hd : 1 ≤ d) (m T : ℝ) (hm : (d : ℝ) / 2 < m)
    (t : Set.Icc (0 : ℝ) T) (Γ Q : Measure (PathSpace d m T)) (γ : Measure (NegSobolev d m))
    [IsProbabilityMeasure γ] (hΓ : Γ.map (fun w => PathSpace.at' w t) = γ)
    (hγ : IsCenteredGaussian γ) (hcov : HasL2ComparableCov m γ)
    (N : ℕ) (P : Measure (Config d N)) [IsProbabilityMeasure P] (ν : Measure (Torus d))
    [IsProbabilityMeasure ν]
    (hQ : Q.map (fun w => PathSpace.at' w t) =
      law P (fun X => Real.sqrt N • NegSobolev.ofMeasureDiff m (empirical X) ν)) :
    Γ ⟂ₘ Q := by
  have hcont : Continuous (fun w : C(Set.Icc (0 : ℝ) T, NegSobolev d m) => w t) :=
    continuous_eval_const t
  have hf : Measurable (fun w : PathSpace d m T => PathSpace.at' w t) := hcont.measurable
  refine mutuallySingular_of_map _ hf Γ Q ?_
  rw [hΓ, hQ]
  exact field_singularity hd m hm γ hγ hcov N P ν

/-- The heat regularization on `E_m`: each Fourier coordinate is multiplied by the heat multiplier
`e^{-τ(2π|k|)²}` (TeX L731-732: "injective heat regularization"). -/
def heatRegularize (m τ : ℝ) (F : NegSobolev d m) : NegSobolev d m :=
  NegSobolev.ofSeq m fun k =>
    Real.exp (-τ * (2 * Real.pi * Lattice.enorm k.1) ^ 2) * NegSobolev.fourierCoeff F k

/-- `M:H:prop:field-singularity` follow-up (TeX L731-733): "it survives injective heat regularization:
divide each Fourier coordinate by its nonzero heat multiplier in the separating Borel set": for `τ > 0`,
`heatRegularize m τ` is measurable and injective, and mutual singularity of two laws on `E_m` is preserved
by it. -/
theorem heatRegularize_multiplier_mem (m τ : ℝ) (hτ : 0 < τ) (k : NonzeroLattice d) :
    0 ≤ Real.exp (-τ * (2 * Real.pi * Lattice.enorm k.1) ^ 2) ∧
      Real.exp (-τ * (2 * Real.pi * Lattice.enorm k.1) ^ 2) ≤ 1 := by
  refine ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr ?_⟩
  have := mul_nonneg hτ.le (sq_nonneg (2 * Real.pi * Lattice.enorm k.1))
  linarith

theorem heatRegularize_coord (m τ : ℝ) (hτ : 0 < τ) (F : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.coord (heatRegularize (d := d) m τ F) k =
      Real.exp (-τ * (2 * Real.pi * Lattice.enorm k.1) ^ 2) * NegSobolev.coord F k := by
  have hb := heatRegularize_multiplier_mem (d := d) m τ hτ
  have hmem : Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m) *
      (Real.exp (-τ * (2 * Real.pi * Lattice.enorm k.1) ^ 2) *
        NegSobolev.fourierCoeff F k)) 2 := by
    have e : (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m) *
        (Real.exp (-τ * (2 * Real.pi * Lattice.enorm k.1) ^ 2) *
          NegSobolev.fourierCoeff F k)) =
        fun k => Real.exp (-τ * (2 * Real.pi * Lattice.enorm k.1) ^ 2) * NegSobolev.coord F k := by
      funext k
      have hj : Lattice.jp k.1 ^ (-m) * Lattice.jp k.1 ^ m = 1 := by
        rw [← Real.rpow_add (Torus.jp_pos k.1), neg_add_cancel, Real.rpow_zero]
      unfold NegSobolev.fourierCoeff
      linear_combination (Real.exp (-τ * (2 * Real.pi * Lattice.enorm k.1) ^ 2) *
        NegSobolev.coord F k) * hj
    rw [e, Torus.memℓp_two_iff]
    refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => ?_)
      (NegSobolev.coord_sq F).1
    rw [mul_pow]
    have h1 := (hb k).2
    have h0 := (hb k).1
    have : Real.exp (-τ * (2 * Real.pi * Lattice.enorm k.1) ^ 2) ^ 2 ≤ 1 := by nlinarith
    calc _ ≤ 1 * NegSobolev.coord F k ^ 2 := mul_le_mul_of_nonneg_right this (sq_nonneg _)
      _ = _ := one_mul _
  unfold heatRegularize
  rw [NegSobolev.coord_ofSeq_of_mem _ hmem k]
  unfold NegSobolev.fourierCoeff
  have hj : Lattice.jp k.1 ^ (-m) * Lattice.jp k.1 ^ m = 1 := by
    rw [← Real.rpow_add (Torus.jp_pos k.1), neg_add_cancel, Real.rpow_zero]
  linear_combination (Real.exp (-τ * (2 * Real.pi * Lattice.enorm k.1) ^ 2) *
    NegSobolev.coord F k) * hj

theorem heatRegularize_lipschitz (m τ : ℝ) (hτ : 0 < τ) (F G : NegSobolev d m) :
    ‖heatRegularize (d := d) m τ F - heatRegularize m τ G‖ ≤ ‖F - G‖ := by
  have hsq : ‖heatRegularize (d := d) m τ F - heatRegularize m τ G‖ ^ 2 ≤ ‖F - G‖ ^ 2 := by
    rw [(NegSobolev.coord_sq _).2, (NegSobolev.coord_sq _).2]
    refine Summable.tsum_le_tsum (fun k => ?_) (NegSobolev.coord_sq _).1 (NegSobolev.coord_sq _).1
    have hc : ∀ H : NegSobolev d m, ∀ j, NegSobolev.coord (H : NegSobolev d m) j = NegSobolev.coord H j :=
      fun _ _ => rfl
    have hsub : ∀ (A B : NegSobolev d m) (j : NonzeroLattice d),
        NegSobolev.coord (A - B) j = NegSobolev.coord A j - NegSobolev.coord B j := fun _ _ _ => rfl
    rw [hsub, hsub, heatRegularize_coord m τ hτ, heatRegularize_coord m τ hτ]
    have hb := heatRegularize_multiplier_mem (d := d) m τ hτ k
    have : Real.exp (-τ * (2 * Real.pi * Lattice.enorm k.1) ^ 2) ^ 2 ≤ 1 := by nlinarith
    rw [← mul_sub, mul_pow]
    calc _ ≤ 1 * (NegSobolev.coord F k - NegSobolev.coord G k) ^ 2 :=
          mul_le_mul_of_nonneg_right this (sq_nonneg _)
      _ = _ := one_mul _
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq

theorem singular_heatRegularize (hd : 1 ≤ d) (m τ : ℝ) (hτ : 0 < τ) :
    Measurable (heatRegularize (d := d) m τ) ∧ Function.Injective (heatRegularize (d := d) m τ) ∧
      ∀ P Q : Measure (NegSobolev d m), P ⟂ₘ Q →
        P.map (heatRegularize m τ) ⟂ₘ Q.map (heatRegularize m τ) := by
  have hlip : LipschitzWith 1 (heatRegularize (d := d) m τ) := by
    refine LipschitzWith.of_dist_le_mul fun F G => ?_
    rw [dist_eq_norm, dist_eq_norm]
    simpa using heatRegularize_lipschitz m τ hτ F G
  have hmeas : Measurable (heatRegularize (d := d) m τ) := hlip.continuous.measurable
  have hinj : Function.Injective (heatRegularize (d := d) m τ) := by
    intro F G h
    have hc : ∀ j : NonzeroLattice d, NegSobolev.coord F j = NegSobolev.coord G j := by
      intro j
      have h2 := congrArg (fun H => NegSobolev.coord H j) h
      rw [heatRegularize_coord m τ hτ, heatRegularize_coord m τ hτ] at h2
      have hpos : Real.exp (-τ * (2 * Real.pi * Lattice.enorm j.1) ^ 2) ≠ 0 := (Real.exp_pos _).ne'
      exact mul_left_cancel₀ hpos h2
    exact lp.ext (funext hc :)
  exact ⟨hmeas, hinj, fun P Q hPQ =>
    (hmeas.measurableEmbedding hinj).mutuallySingular_map hPQ⟩

end Main

end HRS
