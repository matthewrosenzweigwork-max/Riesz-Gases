import HRS.Energy.Modulated
import HRS.Prob.Gaussian
import HRS.Prob.CLT
import HRS.Stochastic.Brownian

/-!
# The particle system, the mean-field equation, the linearised evolution, and the general
fluctuation theorem

Sources (HRS periodic main paper):
* Particle system `H:eq:intro-particles` (source lines 170-178):
  `dx_i = (N⁻¹ ∑_{j≠i} M ∇g(x_i - x_j) - ∇V(x_i)) dt + √(2/β_N) dW_i`, independent Brownian
  motions, independent of the initial configuration.
* Mean-field equation `H:eq:meanfield` (lines 191-194):
  `∂_t ρ = β_N⁻¹ Δρ - Div(ρ (M ∇g*ρ - ∇V))`, `μ^t = ρ^t dx`; weak formulation `B:eq:mf-weak`
  (lines 10101-10104); `(r,Λ)`-regularity `B:eq:mf-regularity` (line 10082); the force
  convention `B:eq:nabla-g-convolution` (lines 10091-10101).
* Backward generator `H:eq:backward-generator` (lines 476-483), propagator `U^{r,t}`, transpose
  `V^{t,r}`; classical adjoint solution, Definition 3.5 (lines 1633-1635); adjoint operator,
  Definition 3.2 (lines 1587-1593).
* Linear fluctuation equation `H:eq:linear-equation` and mild form `H:eq:linear-mild`
  (lines 489-500); noise covariance `2q μ^r(∇φ·∇ψ) dr`.
* General scale: `H:eq:intro-scales` (line 216) `σ_N = min{κ_N, √(Nβ_N)}`;
  `H:eq:general-scale-ratios` (lines 565-569); `H:eq:general-initial-errors` (571-575);
  `𝔈_N`, `𝔈_{N,2}` (556-560); hypotheses (538-579); energy completion (546-555).
* Theorem 2.1 `M:H:thm:general` (lines 580-620): gradient case (582-597), transport
  improvement (598-604), general-matrix clause (609-619).

## Representation decisions (consequential; see `docs/ISSUES.md` §D1-D4 and `docs/SPEC_AUDIT.md`)

* **The particle SDE has additive noise**, so a strong solution is represented *pathwise*
  (no Itô integral needed): `X_t = X_0 + ∫_0^t b(X_s) ds + √(2/β_N) W_t` on the covering
  space `(ℝ^d)^N`, projected to the torus by `Torus.mk`.  `W_i` are `d`-dimensional Brownian
  motions built from Mathlib's `IsBrownianReal` coordinatewise with joint independence.
  `β_N = ∞` is represented by `invβ = 0` (`invβ = β_N⁻¹ ∈ [0,∞)`), as in the source
  ("`1/β := 0` when `β = ∞`", line 1592).  The drift uses `∇g` *off the diagonal*; a solution
  is required to be collision-free (`B:eq:particle-uniform-separation`).
* **The force `∇g * ρ`** is the cancellation-convention integral `B:eq:nabla-g-convolution`
  (`convGradConv`), which is the absolutely convergent integral the source prescribes for all
  `0 ≤ s < d` (for `s < d-1` and bounded `ρ` it is the plain integral).  A plain Bochner
  integral would be the junk value `0` for `d-1 ≤ s < d` (`docs/SPEC_AUDIT.md` A8(3)).
* The mean-field solution is a density `ρ : ℝ → Torus d → ℝ` with the weak formulation
  `B:eq:mf-weak` holding for every `C²` test, plus `(r,Λ)`-regularity as a hypothesis.
* The adjoint propagator `U^{r,t}φ` is the classical adjoint solution (Definition 3.5), when
  it exists; `IsClassicalAdjointSolution` is the defining predicate.  Its existence is
  Proposition 3.9 (package ADJ-01), *not* assumed in definitions.
* The linear SPDE solution `Y` (`H:eq:linear-equation`) is characterised through its mild form
  `Y^t(φ) = Y^0(U^{0,t}φ) + Gaussian stochastic convolution` by the law of the Gaussian part,
  tested on `C^∞` functions (`Torus.IsSmooth`, not `IsCk ⊤`, which is analyticity):
  `IsLinearFluctuationSolution` requires that `(Y^t(φ) - Y^0(U^{0,t}φ))_φ` be a centered
  Gaussian family independent of `Y^0` with covariance `2q ∫_0^t μ^r(∇U^{r,t}φ·∇U^{r,t}ψ) dr`
  (`B:eq:surrogate-cov`, line 10272, with `2σ_N²/(Nβ_N) = 2q_N`).  This is the characterisation
  the source itself uses (`B:eq:surrogate-def`, `B:eq:surrogate-field-torus`, A.33); building the
  solution from a cylindrical Wiener process is package SPDE-01.
* **Theorem 2.1** is stated with the constant quantified *before* the setup: `∃ C, ∀ S` with
  `S` ranging over all setups sharing the stated bounds `GeneralBounds` (M L543-544, L605-607).
  The heat-kernel completion constant `C₀` is constrained by `GeneralSetup.energy_nonneg`
  (M L546-555, "chosen so that `𝓔_N^t ≥ 0`"), and the energy moments `𝔈_N`, `𝔈_{N,2}` are
  assumed finite (`EnergyMomentFinite`, `EnergyMoment2Finite`), so that the real-valued
  `energyMoment`/`energyMoment2` are the source's quantities (M L556-561).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {d N : ℕ}

/-! ### Coefficients -/

/-- Data of the periodic dynamics: dimension, Riesz exponent, constant matrix `M`,
one-body potential `V`, inverse temperature as `invβ = β⁻¹ ∈ [0,∞)` (`0` means `β = ∞`). -/
structure DynData (d : ℕ) where
  s : ℝ
  M : Matrix (Fin d) (Fin d) ℝ
  V : Torus d → ℝ
  invβ : ℝ
  hs0 : 0 ≤ s
  hsd : s < d
  hβ : 0 ≤ invβ

/-- The particle drift `b_i(X) = N⁻¹ ∑_{j≠i} M ∇g(x_i - x_j) - ∇V(x_i)` (line 171). -/
def particleDrift (D : DynData d) (X : Config d N) (i : Fin N) : Euc d :=
  (1 / (N : ℝ)) • ∑ j ∈ Finset.univ.erase i, Torus.matVec D.M (periodicRieszGrad d D.s (X i - X j))
    - Torus.grad D.V (X i)

/-- The force `∇g * ρ` by the cancellation convention `B:eq:nabla-g-convolution`
(source lines 10091-10101):
`∫ ∇g(x-y)(ρ(y)-ρ(x)) 1_{|x-y|≤1/4} dy + ∫ ∇g(x-y) 1_{|x-y|>1/4} ρ(y) dy`.
The subtracted constant contributes zero by oddness of `∇g` and symmetry of the cube
(line 10096), so for `0 ≤ s < d-1` and bounded `ρ` this is the plain integral; for
`d-1 ≤ s < d` and Hölder `ρ` it is the absolutely convergent integral the source prescribes. -/
def convGradConv (G : Torus d → Euc d) (ρ : Torus d → ℝ) (x : Torus d) : Euc d :=
  ∫ y, (if ‖x - y‖ ≤ 1 / 4 then (ρ y - ρ x) • G (x - y) else ρ y • G (x - y))

/-- The mean-field drift `M ∇g*ρ - ∇V` (convention convolution). -/
def meanFieldDrift (D : DynData d) (ρ : Torus d → ℝ) (x : Torus d) : Euc d :=
  Torus.matVec D.M (convGradConv (periodicRieszGrad d D.s) ρ x) - Torus.grad D.V x

/-! ### Brownian motion and the particle SDE -/

/-- `W : ℝ≥0 → Ω → (Fin N → Euc d)` is a family of `N` independent `d`-dimensional standard
Brownian motions: each real coordinate is a Brownian motion and all `N·d` coordinates are
jointly independent. -/
def IsVectorBrownian {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W : ℝ≥0 → Ω → (Fin N → Euc d)) : Prop :=
  (∀ i j, ProbabilityTheory.IsBrownianReal (fun t ω => W t ω i j) P) ∧
    ProbabilityTheory.iIndepFun (fun (ij : Fin N × Fin d) ω => fun t : ℝ≥0 => W t ω ij.1 ij.2) P

/-- Lift of a configuration path to the covering space: a path `Y : ℝ≥0 → Ω → (Fin N → Euc d)`
projects to the torus configuration `X t ω i = Torus.mk (Y t ω i)`. -/
def projectPath {Ω : Type*} (Y : ℝ≥0 → Ω → (Fin N → Euc d)) : ℝ≥0 → Ω → Config d N :=
  fun t ω i => Torus.mk (Y t ω i)

/-- A collision-free strong solution of the particle system `H:eq:intro-particles` on `[0,T]`
driven by `W`, with initial configuration `X₀`, in integrated (pathwise) form on the covering
space:
`Y_t = Y_0 + ∫_0^t b(mk Y_s) ds + √(2 invβ) W_t`, `X_t = mk Y_t`, with `X_0 = X₀`, the drift
integrable in time, and no collisions on `[0,T]` a.s. (`B:eq:particle-uniform-separation`). -/
structure IsStrongSolution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (D : DynData d)
    (T : ℝ) (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d))
    (X : ℝ≥0 → Ω → Config d N) : Prop where
  lift : ∃ Y : ℝ≥0 → Ω → (Fin N → Euc d),
    (∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ) ≤ T →
      (∀ i, IntegrableOn (fun s : ℝ => particleDrift D (projectPath Y (Real.toNNReal s) ω) i)
        (Set.Icc 0 (t : ℝ))) ∧
      ∀ i, Y t ω i = Y 0 ω i + (∫ s in Set.Icc (0 : ℝ) t, particleDrift D (projectPath Y (Real.toNNReal s) ω) i)
        + Real.sqrt (2 * D.invβ) • (W t ω i - W 0 ω i)) ∧
    X = projectPath Y
  init : ∀ᵐ ω ∂P, X 0 ω = X₀ ω
  cont : ∀ᵐ ω ∂P, ∀ i, Continuous fun t => X t ω i
  adapted : ∀ t : ℝ≥0, Measurable (X t)
  no_collision : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ) ≤ T → X t ω ∉ collisionSet d N

/-! `IsFilteredSolution` lives here (it was in `HRS/Stochastic/SelectedFlow.lean`, which imports this file) so that
the statements of Theorem 2.1 below can assume it (ISSUES §I, "Specification repairs: filtered strong solutions"). -/

/-- Filtration bookkeeping.  `IsStrongSolution.adapted` only asserts `mΩ`-measurability
(ISSUES D1), while every Itô identity needs a Brownian filtration to which `X` is adapted
and in which `W` is the Brownian motion.  This structure records exactly the strong-solution
adaptedness the manuscript takes for granted ("strong solution", L10131).

The field `progressive` (not in `PART01_REST_SPEC.md`) says that `X` is a progressively
measurable process.  It is implied by `adapted` and everywhere-continuity of the paths, and it
is needed because the paths of `X` are only a.s. continuous (see the module docstring). -/
structure IsFilteredSolution {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) (ℱ : Filtration ℝ mΩ)
    (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (W : ℝ≥0 → Ω → (Fin N → Euc d))
    (X : ℝ≥0 → Ω → Config d N) : Prop where
  brownian : IsBrownianFiltration P ℱ W'
  coords : ∀ᵐ ω ∂P, ∀ t i j, W' t ω (i, j) = W t ω i j
  adapted : ∀ t : ℝ≥0, Measurable[ℱ t] (X t)
  progressive : IsProgressive ℱ (ofNNRealTime X)

/-- Pathwise uniqueness on `[0,T]` among collision-free strong solutions. -/
def PathwiseUnique {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (D : DynData d) (T : ℝ)
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) : Prop :=
  ∀ X X' : ℝ≥0 → Ω → Config d N, IsStrongSolution P D T X₀ W X → IsStrongSolution P D T X₀ W X' →
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ) ≤ T → X t ω = X' t ω

/-! Proposition B.1 `M:B:thm:particle-wp` is stated and proved in
`HRS/Dynamics/ParticleWellposed.lean` (moved unchanged; its proof lives in `HRS/Stochastic`). -/

/-! ### The mean-field equation -/

/-- The symmetrised interaction pairing
`½ ∬ (∇ψ(x) - ∇ψ(y)) · M ∇g(x - y) dν(x) dν'(y)` off the diagonal
(`B:eq:mf-weak`, right-hand side; `B:eq:B-symmetrized`). -/
def interactionPairing (D : DynData d) (ψ : Torus d → ℝ) (ν ν' : Measure (Torus d)) : ℝ :=
  (1 / 2) * ∫ x, ∫ y, (if x = y then 0 else
    inner ℝ (Torus.grad ψ x - Torus.grad ψ y) (Torus.matVec D.M (periodicRieszGrad d D.s (x - y)))) ∂ν' ∂ν

/-- A weak solution of the mean-field equation `H:eq:meanfield` on `[0,T]` with viscosity
`invβ`: a time-dependent probability density `ρ`, continuous in time as a measure, satisfying
`B:eq:mf-weak` for every `C²` test, in integrated form. -/
structure IsMeanFieldSolution (D : DynData d) (T : ℝ) (ρ : ℝ → Torus d → ℝ) : Prop where
  density : ∀ t ∈ Set.Icc 0 T, IsProbDensity (ρ t)
  weak : ∀ ψ : Torus d → ℝ, Torus.IsCk 2 ψ → ∀ t ∈ Set.Icc 0 T,
    pair (withDensityReal (ρ t)) ψ - pair (withDensityReal (ρ 0)) ψ =
      ∫ r in Set.Icc 0 t,
        (pair (withDensityReal (ρ r)) (fun x => D.invβ * Torus.laplacian ψ x -
            inner ℝ (Torus.grad D.V x) (Torus.grad ψ x)) +
          interactionPairing D ψ (withDensityReal (ρ r)) (withDensityReal (ρ r)))

/-- `(r,Λ)`-regularity on `[0,T]` (`B:eq:mf-regularity`, line 10082):
`sup_{t ≤ T} ‖ρ^t‖_{C^r} ≤ Λ`. -/
def IsRegularMF (r : ℕ) (Λ T : ℝ) (ρ : ℝ → Torus d → ℝ) : Prop :=
  ∀ t ∈ Set.Icc 0 T, Torus.IsCk r (ρ t) ∧ Torus.cbNorm r (ρ t) ≤ Λ

/-! ### The backward generator, the adjoint propagator and the linear equation -/

/-- The backward generator `𝓛_r φ = β⁻¹Δφ + (M∇g*ρ^r - ∇V)·∇φ - ∑_j ∂_j g*(ρ^r (Mᵀ∇φ)_j)`
(`H:eq:backward-generator`, lines 476-483; `B:eq:adjoint-def`, line 1590), with both
convolutions by the convention `B:eq:nabla-g-convolution` (`convGradConv`). -/
def backwardGenerator (D : DynData d) (ρ : Torus d → ℝ) (φ : Torus d → ℝ) (x : Torus d) : ℝ :=
  D.invβ * Torus.laplacian φ x + inner ℝ (meanFieldDrift D ρ x) (Torus.grad φ x) -
    ∑ j : Fin d, (convGradConv (periodicRieszGrad d D.s)
      (fun y => ρ y * (Torus.matVec D.M.transpose (Torus.grad φ y)) j) x) j

/-- A classical adjoint solution on `[0,t]` with terminal datum `φ` (Definition 3.5, lines
1633-1635): `f ∈ C([0,t]; C²_b)`, `∂_r f ∈ C([0,t]; C⁰_b)`, `f(t) = φ`,
`-∂_r f = 𝓛_r f` pointwise.  Time regularity is expressed through the lift. -/
structure IsClassicalAdjointSolution (D : DynData d) (ρ : ℝ → Torus d → ℝ) (t : ℝ)
    (φ : Torus d → ℝ) (f : ℝ → Torus d → ℝ) : Prop where
  c2 : ∀ r ∈ Set.Icc 0 t, Torus.IsCk 2 (f r)
  cont_c2 : ∀ j ≤ 2, Continuous fun p : Set.Icc (0 : ℝ) t × Euc d =>
    iteratedFDeriv ℝ j (Torus.lift (f p.1)) p.2
  terminal : f t = φ
  time_deriv : ∀ x : Torus d, ∀ r ∈ Set.Ioo 0 t,
    HasDerivAt (fun r' => f r' x) (-(backwardGenerator D (ρ r) (f r) x)) r
  cont_time_deriv : Continuous fun p : Set.Icc (0 : ℝ) t × Torus d =>
    backwardGenerator D (ρ p.1) (f p.1) p.2

open Classical in
/-- The adjoint propagator `U^{r,t} φ`: the classical adjoint solution at time `r` when it
exists (`0` otherwise; existence is Proposition 3.9, package ADJ-01). -/
def propagator (D : DynData d) (ρ : ℝ → Torus d → ℝ) (r t : ℝ) (φ : Torus d → ℝ) : Torus d → ℝ :=
  if h : ∃ f, IsClassicalAdjointSolution D ρ t φ f then h.choose r else 0

/-- The noise covariance `2q ∫_0^t μ^r(∇U^{r,t}φ · ∇U^{r,t}ψ) dr` of the linear equation
(`H:eq:linear-mild`, line 498; `B:eq:surrogate-cov`, line 10272). -/
def noiseCovariance (D : DynData d) (ρ : ℝ → Torus d → ℝ) (q t : ℝ) (φ ψ : Torus d → ℝ) : ℝ :=
  2 * q * ∫ r in Set.Icc 0 t, ∫ x, inner ℝ (Torus.grad (propagator D ρ r t φ) x)
    (Torus.grad (propagator D ρ r t ψ) x) * ρ r x

/-- A solution `Y` of the linear fluctuation equation `H:eq:linear-equation` with noise level
`q ≥ 0` and initial value `Y⁰` (an `E_m`-valued random variable), on `[0,T]`, in mild form
(`H:eq:linear-mild`): for all `C^∞` tests `φ`, `Y^t(φ) - Y^0(U^{0,t}φ)` is a centered Gaussian
family independent of `Y^0`, jointly over finitely many tests and times, with covariance
`noiseCovariance` at equal times and the corresponding cross-covariance
`2q ∫_0^{t∧t'} μ^r(∇U^{r,t}φ·∇U^{r,t'}ψ) dr` at different times; paths are continuous in `E_m`. -/
structure IsLinearFluctuationSolution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (D : DynData d) (ρ : ℝ → Torus d → ℝ) (m q T : ℝ) (Y₀ : Ω → NegSobolev d m)
    (Y : ℝ → Ω → NegSobolev d m) : Prop where
  init : ∀ᵐ ω ∂P, Y 0 ω = Y₀ ω
  cont : ∀ᵐ ω ∂P, ContinuousOn (fun t => Y t ω) (Set.Icc 0 T)
  meas : ∀ t, Measurable (Y t)
  gaussian_part : ∀ (p : ℕ) (ts : Fin p → ℝ) (φ : Fin p → Torus d → ℝ),
    (∀ a, ts a ∈ Set.Icc 0 T) → (∀ a, Torus.IsSmooth (φ a)) →
    let G : Ω → EuclideanSpace ℝ (Fin p) := fun ω => WithLp.toLp 2 fun a =>
      NegSobolev.eval (Y (ts a) ω) (φ a) - NegSobolev.eval (Y₀ ω) (propagator D ρ 0 (ts a) (φ a))
    ProbabilityTheory.IndepFun G Y₀ P ∧
    law P G = ProbabilityTheory.multivariateGaussian 0 (Matrix.of fun a b =>
      2 * q * ∫ r in Set.Icc 0 (min (ts a) (ts b)), ∫ x,
        inner ℝ (Torus.grad (propagator D ρ r (ts a) (φ a)) x)
          (Torus.grad (propagator D ρ r (ts b) (φ b)) x) * ρ r x)

/-! ### Scales (`H:eq:intro-scales`, `H:eq:general-scale-ratios`) -/

/-- `σ_N = min{κ_N, √(Nβ_N)}`, with `(σ_N, A_N, q_N) = (κ_N, 1, 0)` when `β_N = ∞`
(`invβ = 0`). -/
def sigmaScale (N : ℕ) (κ invβ : ℝ) : ℝ :=
  if invβ = 0 then κ else min κ (Real.sqrt (N / invβ))

/-- `A_N = σ_N / κ_N`. -/
def Ascale (N : ℕ) (κ invβ : ℝ) : ℝ := if invβ = 0 then 1 else sigmaScale N κ invβ / κ

/-- `q_N = σ_N² /(N β_N) = σ_N² invβ / N`. -/
def qScale (N : ℕ) (κ invβ : ℝ) : ℝ := if invβ = 0 then 0 else sigmaScale N κ invβ ^ 2 * invβ / N

/-! ### Theorem 2.1 (`M:H:thm:general`, lines 538-620) -/

open Classical in
/-- The random path `t ↦ Ξ_N^t = σ_N(μ_N^t - μ^t)` in `𝒳_{γ,T}`, given a continuous particle
path and the mean-field density (`0` path if continuity fails). -/
def flucPath {Ω : Type*} (γ T : ℝ) (σ : ℝ) (X : ℝ≥0 → Ω → Config d N) (ρ : ℝ → Torus d → ℝ)
    (ω : Ω) : PathSpace d γ T :=
  if h : Continuous fun t : Set.Icc (0 : ℝ) T =>
      σ • NegSobolev.ofMeasureDiff γ (empirical (X (Real.toNNReal t) ω)) (withDensityReal (ρ t))
  then ⟨_, h⟩ else 0

open Classical in
/-- A random path in `𝒳_{γ,T}` from a continuous `E_γ`-valued process. -/
def toPath {Ω : Type*} (γ T : ℝ) (Y : ℝ → Ω → NegSobolev d γ) (ω : Ω) : PathSpace d γ T :=
  if h : Continuous fun t : Set.Icc (0 : ℝ) T => Y t ω then ⟨_, h⟩ else 0

/-- The hypotheses of Theorem 2.1 (source lines 538-579).  The heat-kernel completion constant
`C₀` is constrained by `energy_nonneg`, which is the source's "choose once a sufficiently large
heat-kernel completion `𝓔_N^t = F_N(X_N^t, μ^t) + o_N ≥ 0`" (lines 546-555). -/
structure GeneralSetup (d : ℕ) where
  s : ℝ
  hs0 : 0 ≤ s
  hsd : s < d
  hd : 2 ≤ d
  T : ℝ
  hT : 0 < T
  γ : ℕ
  hγ : 2 * d + 10 < γ
  /-- inverse temperatures `β_N⁻¹`, with `sup_N β_N⁻¹ < ∞` -/
  invβ : ℕ → ℝ
  hinvβ : ∀ N, 0 ≤ invβ N
  invβ_bdd : ∃ C, ∀ N, invβ N ≤ C
  V : Torus d → ℝ
  /-- uniform derivative bounds through order `γ + 2d + 12` on `V` -/
  V_reg : Torus.IsCk (γ + 2 * d + 12) V
  /-- the mean-field solutions `ρ_N` with uniform derivative bounds through order `γ+2d+12` -/
  ρ : ℕ → ℝ → Torus d → ℝ
  Λ : ℝ
  /-- the initial scale `κ_N > 0` -/
  κ : ℕ → ℝ
  hκ : ∀ N, 0 < κ N
  /-- the heat-kernel completion constant `C₀` of `o_N` -/
  C₀ : ℝ
  /-- `C₀` is large enough that `𝓔_N^t = F_N(X, μ_N^t) + o_N ≥ 0` off the collision set
  (`H:eq:energy-completion`, lines 546-555) -/
  energy_nonneg : ∀ N, 2 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ X : Config d N,
    X ∉ collisionSet d N →
      0 ≤ rieszEnergy d s X (withDensityReal (ρ N t)) + oN d s C₀ N

/-- The bounds on which the constant of Theorem 2.1 is allowed to depend (source lines
543-544: "the constant in each estimate is allowed to depend on these bounds and on `T, d, s`";
lines 605-607: "independent of `N` and of `β_N` subject to the stated uniform bounds"). -/
structure GeneralBounds (d : ℕ) where
  s : ℝ
  T : ℝ
  γ : ℕ
  /-- the `(γ+2d+12, Λ)`-regularity bound of the mean-field solutions -/
  Λ : ℝ
  /-- a bound on `β_N⁻¹` -/
  Bβ : ℝ
  /-- read only by `Within`; Theorem 2.1 and its variants override it by the quantified `C₀ ≥ C₀min`
  (`{ b with C₀ := C₀ }`, ISSUES "SPEC-C0") -/
  C₀ : ℝ
  V : Torus d → ℝ
  /-- the positive lower density bound of the gradient assertion -/
  c : ℝ

namespace GeneralSetup

variable (S : GeneralSetup d)

/-- `S` is a setup with the bounds `b`. -/
def Within (b : GeneralBounds d) : Prop :=
  S.s = b.s ∧ S.T = b.T ∧ S.γ = b.γ ∧ S.Λ = b.Λ ∧ (∀ N, S.invβ N ≤ b.Bβ) ∧ S.C₀ = b.C₀ ∧
    S.V = b.V

/-- The dynamics data at particle number `N` for a constant matrix `M`. -/
def dynM (M : Matrix (Fin d) (Fin d) ℝ) (N : ℕ) : DynData d :=
  ⟨S.s, M, S.V, S.invβ N, S.hs0, S.hsd, S.hinvβ N⟩

/-- The dynamics data at particle number `N` (gradient case `M = -I`). -/
def dyn (N : ℕ) : DynData d := S.dynM (-1) N

/-- Mean-field regularity hypothesis for a constant matrix `M`: `ρ_N` solves the mean-field
equation with uniform bounds through order `γ + 2d + 12` on `[0,T]`. -/
def MFHypM (M : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  ∀ N, IsMeanFieldSolution (S.dynM M N) S.T (S.ρ N) ∧
    IsRegularMF (S.γ + 2 * d + 12) S.Λ S.T (S.ρ N)

/-- Mean-field regularity hypothesis in the gradient case. -/
def MFHyp : Prop := S.MFHypM (-1)

/-- Positive density hypothesis for the gradient assertion with an explicit lower bound `c`:
`inf_{N,t,x} ρ_N^t(x) ≥ c > 0`. -/
def PosDensityWith (c : ℝ) : Prop :=
  0 < c ∧ ∀ N, ∀ t ∈ Set.Icc 0 S.T, ∀ x, c ≤ S.ρ N t x

/-- Positive density hypothesis for the gradient assertion: `inf_{N,t,x} ρ_N^t(x) > 0`. -/
def PosDensity : Prop := ∃ c, S.PosDensityWith c

/-- `𝓔_N^t = F_N(X_N^t, μ^t) + o_N ≥ 0` (`H:eq:energy-completion`). -/
def energyCompletion (N : ℕ) (X : Config d N) (t : ℝ) : ℝ :=
  rieszEnergy d S.s X (withDensityReal (S.ρ N t)) + oN d S.s S.C₀ N

/-- `𝔈_N = sup_{t≤T} E[𝓔_N^t]` (meaningful under `EnergyMomentFinite`). -/
def energyMoment {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (N : ℕ)
    (X : ℝ≥0 → Ω → Config d N) : ℝ :=
  ⨆ t : Set.Icc (0 : ℝ) S.T, ∫ ω, S.energyCompletion N (X (Real.toNNReal t) ω) t ∂P

/-- `𝔈_{N,2} = sup_{t≤T} ‖𝓔_N^t‖_{L²(P)}` (meaningful under `EnergyMoment2Finite`). -/
def energyMoment2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (N : ℕ)
    (X : ℝ≥0 → Ω → Config d N) : ℝ :=
  ⨆ t : Set.Icc (0 : ℝ) S.T, Real.sqrt (∫ ω, (S.energyCompletion N (X (Real.toNNReal t) ω) t) ^ 2 ∂P)

/-- `𝔈_N < ∞`: each `𝓔_N^t` is integrable and `t ↦ E[𝓔_N^t]` is bounded on `[0,T]`
(source lines 556-561; without this the real-valued `energyMoment` would take the junk value
`0` where the source has `𝔈_N = ∞`). -/
def EnergyMomentFinite {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (N : ℕ)
    (X : ℝ≥0 → Ω → Config d N) : Prop :=
  (∀ t ∈ Set.Icc (0 : ℝ) S.T,
    Integrable (fun ω => S.energyCompletion N (X (Real.toNNReal t) ω) t) P) ∧
  BddAbove (Set.range fun t : Set.Icc (0 : ℝ) S.T =>
    ∫ ω, S.energyCompletion N (X (Real.toNNReal t) ω) t ∂P)

/-- `𝔈_{N,2} < ∞`: each `𝓔_N^t` is in `L²(P)` and `t ↦ ‖𝓔_N^t‖_{L²}` is bounded on `[0,T]`. -/
def EnergyMoment2Finite {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (N : ℕ)
    (X : ℝ≥0 → Ω → Config d N) : Prop :=
  (∀ t ∈ Set.Icc (0 : ℝ) S.T,
    MemLp (fun ω => S.energyCompletion N (X (Real.toNNReal t) ω) t) 2 P) ∧
  BddAbove (Set.range fun t : Set.Icc (0 : ℝ) S.T =>
    Real.sqrt (∫ ω, (S.energyCompletion N (X (Real.toNNReal t) ω) t) ^ 2 ∂P))

/-- `ε_{N,p} = ‖κ_N(μ_N^0 - μ^0) - η°‖_{L^p(P; E_γ)}` (`H:eq:general-initial-errors`). -/
def initialError {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (N : ℕ) (p : ℝ)
    (X₀ : Ω → Config d N) (η₀ : Ω → NegSobolev d S.γ) : ℝ :=
  (∫ ω, ‖S.κ N • NegSobolev.ofMeasureDiff (S.γ : ℝ) (empirical (X₀ ω)) (withDensityReal (S.ρ N 0)) -
      η₀ ω‖ ^ p ∂P) ^ (1 / p)

/-- Finiteness of `ε_{N,p}`: the `p`-th power of the initial discrepancy is integrable. -/
def InitialErrorFinite {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (N : ℕ) (p : ℝ)
    (X₀ : Ω → Config d N) (η₀ : Ω → NegSobolev d S.γ) : Prop :=
  Integrable (fun ω => ‖S.κ N • NegSobolev.ofMeasureDiff (S.γ : ℝ) (empirical (X₀ ω))
    (withDensityReal (S.ρ N 0)) - η₀ ω‖ ^ p) P

/-- Theorem 2.1 `M:H:thm:general` (lines 580-607), gradient case, the three estimates
`H:eq:general-smooth`, `H:eq:general-W1`, `H:eq:general-W2` on `𝒳_{γ,T}`: for every choice of
the bounds `b` there is `C_T` (depending only on `b`, hence independent of `N`, of the
sequences `β_N`, `κ_N`, `ρ_N` and of the realisation) such that for every setup `S` with these
bounds, every `N ≥ 2`, every probability space carrying a strong solution `X` with finite
energy moments, with initial law independent of the noise, every `E_γ`-valued `η°` coupled to
`X₀` independently of the noise with finite initial errors, and every solution `Y_N` of the
linear equation with `q = q_N` and initial value `A_N η°`:

`d_2(Ξ_N, Y_N) ≤ C_T (A_N ε_{N,1} + σ_N 𝔈_N + q_N (𝔈_N^{1/2} + N^{-2/d}))`,
`W_1(Ξ_N, Y_N) ≤ C_T (A_N ε_{N,1} + σ_N 𝔈_N + √q_N (𝔈_N^{1/4} + N^{-1/d}))`,
`W_2(Ξ_N, Y_N) ≤ C_T (A_N ε_{N,2} + σ_N 𝔈_{N,2} + √q_N (𝔈_N^{1/4} + N^{-1/d}))`
(the last requires the displayed second moments to be finite, line 598).

Statement repair (ISSUES.md, entries "5.14 `criterion_comparison`…" and "N:thm:dynamic …"; final entry "Filtered strong solutions …"): its proof (U-section, `U:eq:quantitative-mild`) rests on the exact empirical-adjoint identity `B:prop:duality-identity` (Lemma 3.7), whose Itô calculus needs a Brownian filtration, so `X` is assumed a filtered strong solution (`IsFilteredSolution`), the strong-solution adaptedness of A.1 that `IsStrongSolution` (measurability only, ISSUES D1) does not record.

Statement repair 2026-10-16 (ISSUES "SPEC-C0"): the completion constant `C₀` of `o_N` must be taken large enough (TeX M L546-555, L2279-2299 "Increasing its constant once suffices"), so the conclusion is now stated for every `C₀ ≥ C₀min` (with `C₀min` independent of `C₀`) and the setups `Within { b with C₀ := C₀ }`; previously `C₀` was pinned to `b.C₀` with no lower bound. -/
theorem general_fluctuation (b : GeneralBounds d) :
    ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ → ∃ C : ℝ, 0 < C ∧
      ∀ S : GeneralSetup d, S.Within { b with C₀ := C₀ } → S.MFHyp → S.PosDensityWith b.c →
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

/-- Theorem 2.1, transport improvement `H:eq:general-transport-improvement` (lines 598-604):
under the hypotheses of `general_fluctuation` (gradient case, positive density bound), the
covariance contribution in the two Wasserstein estimates can be replaced by
`C_T √q_N min{𝔈_N^{1/4} + N^{-1/d}, 𝔈_N^{1/max{2, d-s}} + N^{-1/d}}`.

Statement repair (ISSUES.md, entries "5.14 `criterion_comparison`…" and "N:thm:dynamic …"; final entry "Filtered strong solutions …"): its proof (U-section, `U:eq:quantitative-mild`) rests on the exact empirical-adjoint identity `B:prop:duality-identity` (Lemma 3.7), whose Itô calculus needs a Brownian filtration, so `X` is assumed a filtered strong solution (`IsFilteredSolution`), the strong-solution adaptedness of A.1 that `IsStrongSolution` (measurability only, ISSUES D1) does not record.

Statement repair 2026-10-16 (ISSUES "SPEC-C0"): the completion constant `C₀` of `o_N` must be taken large enough (TeX M L546-555, L2279-2299 "Increasing its constant once suffices"), so the conclusion is now stated for every `C₀ ≥ C₀min` (with `C₀min` independent of `C₀`) and the setups `Within { b with C₀ := C₀ }`; previously `C₀` was pinned to `b.C₀` with no lower bound. -/
theorem general_fluctuation_transport (b : GeneralBounds d) :
    ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ → ∃ C : ℝ, 0 < C ∧
      ∀ S : GeneralSetup d, S.Within { b with C₀ := C₀ } → S.MFHyp → S.PosDensityWith b.c →
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
      let cov := Real.sqrt q * min (𝔈 ^ ((1 : ℝ) / 4) + (N : ℝ) ^ (-(1 : ℝ) / d))
        (𝔈 ^ ((1 : ℝ) / max 2 ((d : ℝ) - S.s)) + (N : ℝ) ^ (-(1 : ℝ) / d))
      let Ξ := law P (flucPath S.γ S.T σ X (S.ρ N))
      let YN := law P (toPath S.γ S.T Y)
      wassersteinE 1 Ξ YN ≤ ENNReal.ofReal
          (C * (A * S.initialError P N 1 X₀ η₀ + σ * 𝔈 + cov)) ∧
      (S.EnergyMoment2Finite P N X →
        Integrable (fun ω => ‖flucPath S.γ S.T σ X (S.ρ N) ω‖ ^ 2) P →
        S.InitialErrorFinite P N 2 X₀ η₀ →
        wassersteinE 2 Ξ YN ≤ ENNReal.ofReal
          (C * (A * S.initialError P N 2 X₀ η₀ + σ * S.energyMoment2 P N X + cov))) := by
  sorry

/-- The adjoint input `H:eq:matrix-adjoint-input` (lines 609-616) for a general constant
matrix `M`, with bound `K`: uniformly for `0 ≤ r ≤ t ≤ T` and every `N`, the adjoint
evolution exists on `H^γ ∩ C²` (so that `propagator` is the genuine `U^{r,t}`) and
`‖U^{r,t}‖_{H^γ→H^γ} + ‖U^{r,t}‖_{H^{γ+2}→H^{γ+2}} + ‖𝓛_r‖_{H^{γ+2}→H^γ} ≤ K`.
Statement repair 2026-10-16 (ISSUES "ADJIN"): the TeX bounds operator norms of *the* adjoint evolution, which
presupposes that `U^{r,t}` is a well-defined (unique) operator mapping `H^γ` and `H^{γ+2}` into themselves; the
`MemSobolev` conjuncts and the uniqueness clause make this explicit (without them `sobolevNorm` of a non-member is a
junk value and `propagator`, a `choose`, need not satisfy the cocycle identity). -/
def AdjointInput (M : Matrix (Fin d) (Fin d) ℝ) (K : ℝ) : Prop :=
  (∀ N, ∀ t : ℝ, 0 ≤ t → t ≤ S.T → ∀ φ : Torus d → ℝ, ∀ f g : ℝ → Torus d → ℝ,
    IsClassicalAdjointSolution (S.dynM M N) (S.ρ N) t φ f →
    IsClassicalAdjointSolution (S.dynM M N) (S.ρ N) t φ g → ∀ r ∈ Set.Icc 0 t, f r = g r) ∧
  ∀ N, ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ S.T →
    (∀ φ : Torus d → ℝ, Torus.IsCk 2 φ → MemSobolev (S.γ : ℝ) φ →
      (∃ f, IsClassicalAdjointSolution (S.dynM M N) (S.ρ N) t φ f) ∧
      MemSobolev (S.γ : ℝ) (propagator (S.dynM M N) (S.ρ N) r t φ) ∧
      sobolevNorm (S.γ : ℝ) (propagator (S.dynM M N) (S.ρ N) r t φ) ≤
        K * sobolevNorm (S.γ : ℝ) φ) ∧
    (∀ φ : Torus d → ℝ, Torus.IsCk 2 φ → MemSobolev ((S.γ : ℝ) + 2) φ →
      MemSobolev ((S.γ : ℝ) + 2) (propagator (S.dynM M N) (S.ρ N) r t φ) ∧
      sobolevNorm ((S.γ : ℝ) + 2) (propagator (S.dynM M N) (S.ρ N) r t φ) ≤
        K * sobolevNorm ((S.γ : ℝ) + 2) φ ∧
      sobolevNorm (S.γ : ℝ) (backwardGenerator (S.dynM M N) (S.ρ N r) φ) ≤
        K * sobolevNorm ((S.γ : ℝ) + 2) φ)

/-- Theorem 2.1, general-matrix clause (lines 609-619): for a constant matrix `M` with
`Sym M ≤ 0`, under the adjoint input `AdjointInput M K` (uniformly in `0 ≤ r ≤ t ≤ T`), the
three estimates hold on `𝒳_{γ+2,T}` with the same energy and initial-law inputs (initial
errors in `E_γ`, paths compared in `E_{γ+2}` through `NegSobolev.embed`; the linear solution
is taken in `E_{γ+2}`).  No positive density bound is required (the transport improvement
with the positive density bound is `general_fluctuation_transport`, gradient case).

Statement repair (ISSUES.md, entries "5.14 `criterion_comparison`…" and "N:thm:dynamic …"; final entry "Filtered strong solutions …"): its proof (U-section, `U:eq:quantitative-mild`) rests on the exact empirical-adjoint identity `B:prop:duality-identity` (Lemma 3.7), whose Itô calculus needs a Brownian filtration, so `X` is assumed a filtered strong solution (`IsFilteredSolution`), the strong-solution adaptedness of A.1 that `IsStrongSolution` (measurability only, ISSUES D1) does not record.

Statement repair 2026-10-16 (ISSUES "SPEC-C0"): the completion constant `C₀` of `o_N` must be taken large enough (TeX M L546-555, L2279-2299 "Increasing its constant once suffices"), so the conclusion is now stated for every `C₀ ≥ C₀min` (with `C₀min` independent of `C₀`) and the setups `Within { b with C₀ := C₀ }`; previously `C₀` was pinned to `b.C₀` with no lower bound. -/
theorem general_fluctuation_matrix (b : GeneralBounds d) (M : Matrix (Fin d) (Fin d) ℝ)
    (hM : Torus.SymNonpos M) (K : ℝ) :
    ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ → ∃ C : ℝ, 0 < C ∧
      ∀ S : GeneralSetup d, S.Within { b with C₀ := C₀ } → S.MFHypM M → S.AdjointInput M K →
      ∀ (N : ℕ) (_ : 2 ≤ N) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P]
      (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (_ : IsVectorBrownian P W)
      (X : ℝ≥0 → Ω → Config d N) (_ : IsStrongSolution P (S.dynM M N) S.T X₀ W X)
      (_ : ∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
        (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X)
      (_ : S.EnergyMomentFinite P N X)
      (η₀ : Ω → NegSobolev d S.γ) (_ : Measurable η₀)
      (_ : ProbabilityTheory.IndepFun (fun ω => (X₀ ω, η₀ ω)) (fun ω => fun t => W t ω) P)
      (_ : S.InitialErrorFinite P N 1 X₀ η₀)
      (Y : ℝ → Ω → NegSobolev d ((S.γ : ℝ) + 2))
      (_ : IsLinearFluctuationSolution P (S.dynM M N) (S.ρ N) ((S.γ : ℝ) + 2)
        (qScale N (S.κ N) (S.invβ N)) S.T
        (fun ω => Ascale N (S.κ N) (S.invβ N) • NegSobolev.embed ((S.γ : ℝ) + 2) (η₀ ω)) Y),
      let σ := sigmaScale N (S.κ N) (S.invβ N)
      let A := Ascale N (S.κ N) (S.invβ N)
      let q := qScale N (S.κ N) (S.invβ N)
      let 𝔈 := S.energyMoment P N X
      let Ξ := law P (flucPath ((S.γ : ℝ) + 2) S.T σ X (S.ρ N))
      let YN := law P (toPath ((S.γ : ℝ) + 2) S.T Y)
      smoothDist 2 Ξ YN ≤
          C * (A * S.initialError P N 1 X₀ η₀ + σ * 𝔈 + q * (Real.sqrt 𝔈 + (N : ℝ) ^ (-(2 : ℝ) / d))) ∧
      wassersteinE 1 Ξ YN ≤ ENNReal.ofReal
          (C * (A * S.initialError P N 1 X₀ η₀ + σ * 𝔈 +
            Real.sqrt q * (𝔈 ^ ((1 : ℝ) / 4) + (N : ℝ) ^ (-(1 : ℝ) / d)))) ∧
      (S.EnergyMoment2Finite P N X →
        Integrable (fun ω => ‖flucPath ((S.γ : ℝ) + 2) S.T σ X (S.ρ N) ω‖ ^ 2) P →
        S.InitialErrorFinite P N 2 X₀ η₀ →
        wassersteinE 2 Ξ YN ≤ ENNReal.ofReal
          (C * (A * S.initialError P N 2 X₀ η₀ + σ * S.energyMoment2 P N X +
            Real.sqrt q * (𝔈 ^ ((1 : ℝ) / 4) + (N : ℝ) ^ (-(1 : ℝ) / d))))) := by
  sorry

end GeneralSetup

end HRS
