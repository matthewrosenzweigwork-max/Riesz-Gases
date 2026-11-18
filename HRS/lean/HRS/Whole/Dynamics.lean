import HRS.Whole.Thermal
import HRS.Dynamics.Setup

/-!
# Whole-space dynamics: particle system, mean-field equation, adjoint propagator, linear
fluctuation processes (definitions used by Sections S4.10-S5.7 and the headline Theorem S2.1)

Source: HRS whole-space supplement (S), with the periodic main paper (M) for the objects the
supplement re-uses.

* Particle system `W:r2:particle-equation` (S lines 200-203),
  `dx_i = -(∇V(x_i) + N⁻¹ ∑_{j≠i} ∇g(x_i - x_j)) dt + √(2/β) dB_i`; its matrix form
  `dx_i = (N⁻¹ ∑_{j≠i} M∇g(x_i-x_j) - ∇V(x_i)) dt + √(2ν) dB_i`, `ν = β⁻¹`
  (M `H:eq:intro-particles`, M lines 170-178); the confined whole-space realization
  (S lines 9698-9724, `S:sec:particle-realization`).
* Mean-field equation and weak form `B:eq:mf-weak` on `ℝ^d` ("interpreted with the physical kernel
  on `ℝ^d`", S lines 9667-9668), force convention `B:eq:nabla-g-convolution` (M lines 10091-10101,
  stated for `𝔻 ∈ {𝕋^d, ℝ^d}`), backward generator `B:eq:adjoint-def` (M line 1590), classical
  adjoint solution on `ℝ^d` (`B:rem:def-adjoint-rd`, S lines 10098-10100).
* Linear fluctuation equation `H:eq:linear-equation`, mild form `H:eq:linear-mild`, noise
  covariance `2q ∫_0^t μ^r(∇U^{r,t}φ·∇U^{r,t}ψ) dr`.

## Representation decisions (see also `HRS/Dynamics/Setup.lean`, which these mirror)

* All definitions mirror their periodic counterparts of `HRS/Dynamics/Setup.lean` with `ℝ^d`
  in place of `𝕋^d`; the particle SDE has additive noise and is therefore written pathwise on
  `ℝ^d` itself (no covering space).
* The adjoint propagator `U^{r,t}φ` is the classical adjoint solution (`C_b²`, bounded `∂_r f`,
  `B:rem:def-adjoint-rd`) when it exists (`propagatorW`; `0` otherwise, existence is an input of
  each statement, never assumed in a definition).
* A generator is described by a `WholeCoeff`: viscosity `ν`, the *full* drift field
  `b_t = M∇g*ρ_t - ∇V` (resp. `-Qx + c_t`), the density `ρ_t`, the matrix `M` and the exponent `s`;
  `generatorW` is `𝓛_t φ = νΔφ + b_t·∇φ - Div g*(ρ_t Mᵀ∇φ)`.  The S5.1/S5.7 operator with a general
  bounded transport `c` is a `WholeCoeff` whose drift is `-Qx + c`.
* The linear Gaussian process is characterised by its (jointly Gaussian) finite-dimensional laws,
  as in the periodic file; the initial field of the linear equation is a *random linear functional*
  `η₀ : Ω → (ℝ^d → ℝ) → ℝ` on test functions (because the adjoint orbit `U^{0,t}φ_j` of a Hermite
  function has an algebraic tail and is not in `Σ^m`, S lines 3181-3184, so `Y⁰(U^{0,t}φ)` cannot
  be a pairing of `Y⁰ ∈ B_m` with an element of `Σ^m`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole

variable {d N : ℕ}

/-! ### Coefficients of the particle system -/

/-- Data of the whole-space dynamics: Riesz exponent `s`, constant interaction matrix `M`,
one-body potential `V` (possibly of linear-gradient growth), and `invβ = β⁻¹ ∈ [0,∞)` (`ν`).
Gradient dynamics is `M = -1` (`-I`).  The standing constraints `0 ≤ s < d`, `0 ≤ invβ` are
hypotheses of each statement. -/
structure WholeDyn (d : ℕ) where
  s : ℝ
  M : Matrix (Fin d) (Fin d) ℝ
  V : Euc d → ℝ
  invβ : ℝ

/-- The affine-quadratic potential `V(x) = xᵀQx/2 + c·x` (S lines 3203, 3828). -/
def quadV (Q : Matrix (Fin d) (Fin d) ℝ) (c : Euc d) (x : Euc d) : ℝ :=
  (1 / 2) * inner ℝ x (Torus.matVec Q x) + inner ℝ c x

/-- The collision set `{X : x_i = x_j for some i ≠ j}` of configurations of `ℝ^d`. -/
def eucCollisionSet (d N : ℕ) : Set (EucConfig d N) := {X | ∃ i j, i ≠ j ∧ X i = X j}

/-- The particle drift `b_i(X) = N⁻¹ ∑_{j≠i} M∇g(x_i - x_j) - ∇V(x_i)` (M line 171; S lines 200-203
with `M = -I`). -/
def particleDriftW (D : WholeDyn d) (X : EucConfig d N) (i : Fin N) : Euc d :=
  (1 / (N : ℝ)) • ∑ j ∈ Finset.univ.erase i,
      Torus.matVec D.M (rieszKernelGrad d D.s (X i - X j)) - gradient D.V (X i)

/-- A collision-free strong solution of the whole-space particle system on `[0,T]` driven by `W`
with initial configuration `X₀`, in integrated (pathwise) form
`X_t = X_0 + ∫_0^t b(X_s) ds + √(2ν)(W_t - W_0)` (additive noise), continuous, adapted
(each `X_t` measurable), with no collisions on `[0,T]` a.s. (the whole-space counterpart of
`B:thm:particle-wp`, S lines 9698-9724). -/
structure IsWholeStrongSolution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (D : WholeDyn d)
    (T : ℝ) (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d))
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
  no_collision : ∀ᵐ ζ ∂P, ∀ t : ℝ≥0, (t : ℝ) ≤ T → X t ζ ∉ eucCollisionSet d N

/-- Filtration bookkeeping for the whole-space process (`HRS.IsFilteredSolution` on `ℝ^d`; moved here from `HRS.Whole.AppendixA` so that the headline statements can use it): `W'` is a Brownian
motion for `ℱ` with `W'(t)(i,j) = W_i^j(t)`, and `X` is `ℱ`-adapted and progressively measurable. -/
structure IsWholeFilteredSolution {Ω : Type*} [mΩ : MeasurableSpace Ω] {N : ℕ} (P : Measure Ω)
    (ℱ : Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (W : ℝ≥0 → Ω → (Fin N → Euc d))
    (X : ℝ≥0 → Ω → EucConfig d N) : Prop where
  brownian : IsBrownianFiltration P ℱ W'
  coords : ∀ᵐ ζ ∂P, ∀ t i j, W' t ζ (i, j) = W t ζ i j
  adapted : ∀ t : ℝ≥0, Measurable[ℱ t] (X t)
  progressive : IsProgressive ℱ (ofNNRealTime X)

/-! ### Mean-field equation, generator, adjoint solutions -/

/-- The force convolution `G * ρ (x)` by the cancellation convention
`B:eq:nabla-g-convolution` (M lines 10091-10101, valid for `𝔻 = ℝ^d`; the subtracted constant
contributes zero by oddness of `G = ∇g`):
`∫ G(x-y)(ρ(y)-ρ(x)) 1_{|x-y|≤1/4} dy + ∫ G(x-y) ρ(y) 1_{|x-y|>1/4} dy`. -/
def convGradConvW (G : Euc d → Euc d) (ρ : Euc d → ℝ) (x : Euc d) : Euc d :=
  ∫ y, (if ‖x - y‖ ≤ 1 / 4 then (ρ y - ρ x) • G (x - y) else ρ y • G (x - y))

/-- The mean-field drift `M ∇g*ρ - ∇V`. -/
def meanFieldDriftW (D : WholeDyn d) (ρ : Euc d → ℝ) (x : Euc d) : Euc d :=
  Torus.matVec D.M (convGradConvW (rieszKernelGrad d D.s) ρ x) - gradient D.V x

/-- The symmetrised interaction pairing `½ ∬_{x≠y} (∇ψ(x)-∇ψ(y))·M∇g(x-y) dν(x) dν'(y)`
(`B:eq:mf-weak`, M line 10104). -/
def interactionPairingW (D : WholeDyn d) (ψ : Euc d → ℝ) (ν ν' : Measure (Euc d)) : ℝ :=
  (1 / 2) * ∫ x, ∫ y, (if x = y then 0 else
    inner ℝ (gradient ψ x - gradient ψ y) (Torus.matVec D.M (rieszKernelGrad d D.s (x - y)))) ∂ν' ∂ν

/-- A weak solution of the whole-space mean-field equation on `[0,T]` (`H:eq:meanfield`,
`B:eq:mf-weak` "interpreted with the physical kernel on `ℝ^d`", S lines 9667-9668): probability
densities with a finite second moment (technical: needed for the integrations by parts, S lines
9668-9670 "the second-moment bound"), and the weak identity for every `ψ ∈ C_b²(ℝ^d)`. -/
structure IsWholeMeanFieldSolution (D : WholeDyn d) (T : ℝ) (ρ : ℝ → Euc d → ℝ) : Prop where
  density : ∀ t ∈ Set.Icc 0 T, IsProbDensity (ρ t)
  second_moment : ∀ t ∈ Set.Icc 0 T, Integrable (fun x => ‖x‖ ^ 2 * ρ t x)
  weak : ∀ ψ : Euc d → ℝ, MemCb 2 ψ → ∀ t ∈ Set.Icc 0 T,
    pair (withDensityReal (ρ t)) ψ - pair (withDensityReal (ρ 0)) ψ =
      ∫ r in Set.Icc 0 t,
        (pair (withDensityReal (ρ r)) (fun x => D.invβ * Laplacian.laplacian ψ x -
            inner ℝ (gradient D.V x) (gradient ψ x)) +
          interactionPairingW D ψ (withDensityReal (ρ r)) (withDensityReal (ρ r)))

/-- Coefficients of a linear (backward) generator on `ℝ^d`: exponent `s` of the kernel,
interaction matrix `M`, viscosity `ν ≥ 0`, the *full* transport field `b_t`, and the density
`ρ_t` of the nonlocal term. -/
structure WholeCoeff (d : ℕ) where
  s : ℝ
  M : Matrix (Fin d) (Fin d) ℝ
  ν : ℝ
  drift : ℝ → Euc d → Euc d
  ρ : ℝ → Euc d → ℝ

/-- The coefficients of the dynamics `D` along a mean-field trajectory `ρ`:
transport `b_t = M∇g*ρ_t - ∇V`. -/
def WholeDyn.coeff (D : WholeDyn d) (ρ : ℝ → Euc d → ℝ) : WholeCoeff d :=
  ⟨D.s, D.M, D.invβ, fun t => meanFieldDriftW D (ρ t), ρ⟩

/-- The backward generator `𝓛_t φ = νΔφ + b_t·∇φ - Div g*(ρ_t Mᵀ∇φ)` (`B:eq:adjoint-def`,
M line 1590; S lines 3213-3215, 3844-3845), with both convolutions by the cancellation
convention. -/
def generatorW (C : WholeCoeff d) (t : ℝ) (φ : Euc d → ℝ) (x : Euc d) : ℝ :=
  C.ν * Laplacian.laplacian φ x + inner ℝ (C.drift t x) (gradient φ x) -
    ∑ j : Fin d, (convGradConvW (rieszKernelGrad d C.s)
      (fun y => C.ρ t y * (Torus.matVec C.M.transpose (gradient φ y)) j) x) j

/-- A classical adjoint solution on `[0,t]` with terminal datum `φ` on `ℝ^d`
(`B:rem:def-adjoint-rd`, S lines 10098-10100): `f`, `∇f`, `∇²f` are bounded and continuous
(local `C²` continuity in time), `f(t) = φ`, and `-∂_r f = 𝓛_r f` pointwise, with `∂_r f`
continuous.
SUSPECTED ISSUE (latent in the TeX): the source (S L10098-10100) asks `∂_r f` to be *bounded*.
For the confining drift `-Qx·∇` (`Q ≠ 0`) this fails already at `r = t` for a bounded smooth datum
such as `φ = sin x_i` (`∂_r f = -𝓛 φ` contains `Qx·∇φ`, which grows linearly), so the literal
notion would make every statement using it vacuous for quadratic `V` (and B:thm:adjoint-rd(a) false
as written).  The repaired notion used here (`bdd_time_deriv`) asks `∂_r f` to be of at most
linear growth, `|∂_r f(r,x)| ≤ B(1+|x|)` uniformly on `[0,t]` (the drift is `O(1+|x|)` by
`B:eq:drift-bounds-rd`, S L10112, and `∇f` is bounded); in the unconfined case (`Q = 0`, bounded
drift) it is implied by the source's boundedness. -/
structure IsClassicalAdjointW (C : WholeCoeff d) (t : ℝ) (φ : Euc d → ℝ)
    (f : ℝ → Euc d → ℝ) : Prop where
  c2 : ∀ r ∈ Set.Icc 0 t, ContDiff ℝ 2 (f r)
  bdd : ∀ j ≤ 2, ∃ B : ℝ, ∀ r ∈ Set.Icc 0 t, ∀ x, ‖iteratedFDeriv ℝ j (f r) x‖ ≤ B
  cont_c2 : ∀ j ≤ 2, Continuous fun p : Set.Icc (0 : ℝ) t × Euc d =>
    iteratedFDeriv ℝ j (f p.1) p.2
  terminal : f t = φ
  time_deriv : ∀ x : Euc d, ∀ r ∈ Set.Ioo 0 t,
    HasDerivAt (fun r' => f r' x) (-(generatorW C r (f r) x)) r
  cont_time_deriv : Continuous fun p : Set.Icc (0 : ℝ) t × Euc d => generatorW C p.1 (f p.1) p.2
  bdd_time_deriv : ∃ B : ℝ, ∀ r ∈ Set.Icc 0 t, ∀ x, |generatorW C r (f r) x| ≤ B * (1 + ‖x‖)

open Classical in
/-- The adjoint propagator `U^{r,t} φ`: the classical adjoint solution at time `r` when one
exists (`0` otherwise; existence is an input of the statements, never assumed here). -/
def propagatorW (C : WholeCoeff d) (r t : ℝ) (φ : Euc d → ℝ) : Euc d → ℝ :=
  if h : ∃ f, IsClassicalAdjointW C t φ f then h.choose r else 0

/-- The noise covariance `2q ∫_0^{t∧t'} ∫ ∇U^{r,t}φ·∇U^{r,t'}ψ ρ^r dx dr` of the linear equation
(`H:eq:linear-mild`, M line 498; `B:eq:surrogate-cov`). -/
def noiseCovW (C : WholeCoeff d) (q t t' : ℝ) (φ ψ : Euc d → ℝ) : ℝ :=
  2 * q * ∫ r in Set.Icc 0 (min t t'), ∫ x, inner ℝ (gradient (propagatorW C r t φ) x)
    (gradient (propagatorW C r t' ψ) x) * C.ρ r x

/-! ### The linear fluctuation equation -/

/-- A smooth test function in the oscillator space `Σ^m` (so that the pairing
`OscDual.eval Y φ` of a field `Y ∈ B_m` with it is the genuine pairing, not a junk `tsum`). -/
def IsOscTest (m : ℝ) (φ : Euc d → ℝ) : Prop := ContDiff ℝ ∞ φ ∧ MemOsc m φ

/-- A solution `Y` of the linear fluctuation equation `H:eq:linear-equation` with noise level
`q ≥ 0` and prescribed random initial functional `η₀` (`Y⁰(f) = η₀(f)`), on `[0,T]`, in mild form
(`H:eq:linear-mild`): `Y` is continuous in `B_m` a.s., and for every finite family of times and
oscillator test functions the vector `(Y^{t_a}(φ_a) - η₀(U^{0,t_a}φ_a))_a` is a centered Gaussian,
independent of `η₀`, with covariance `noiseCovW`. -/
structure IsLinearFluctuationSolutionW {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (C : WholeCoeff d) (m q T : ℝ) (η₀ : Ω → (Euc d → ℝ) → ℝ) (Y : ℝ → Ω → OscDual d m) :
    Prop where
  cont : ∀ᵐ ζ ∂P, ContinuousOn (fun t => Y t ζ) (Set.Icc 0 T)
  meas : ∀ t, Measurable (Y t)
  gaussian_part : ∀ (p : ℕ) (ts : Fin p → ℝ) (φ : Fin p → Euc d → ℝ),
    (∀ a, ts a ∈ Set.Icc 0 T) → (∀ a, IsOscTest m (φ a)) →
    let G : Ω → EuclideanSpace ℝ (Fin p) := fun ζ => WithLp.toLp 2 fun a =>
      OscDual.eval (Y (ts a) ζ) (φ a) - η₀ ζ (propagatorW C 0 (ts a) (φ a))
    ProbabilityTheory.IndepFun G η₀ P ∧
    law P G = ProbabilityTheory.multivariateGaussian 0 (Matrix.of fun a b =>
      noiseCovW C q (ts a) (ts b) (φ a) (φ b))

/-- The linear Gaussian evolution `Z` along `C` with noise level `q` and initial covariance form
`C₀` (a bilinear form on bounded smooth functions), characterised by its finite-dimensional
laws: continuous in `B_m`, jointly centered Gaussian on oscillator test functions with
`Cov(Z^t(φ), Z^{t'}(ψ)) = C₀(U^{0,t}φ, U^{0,t'}ψ) + noiseCovW q t t' φ ψ` (the sum of the
initial covariance transported by the adjoint orbit and the noise covariance, `H:eq:linear-mild`
with an independent centered Gaussian initial field). -/
structure IsLinearGaussianEvolutionW {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (C : WholeCoeff d) (m q T : ℝ) (C₀ : (Euc d → ℝ) → (Euc d → ℝ) → ℝ)
    (Z : ℝ → Ω → OscDual d m) : Prop where
  cont : ∀ᵐ ζ ∂P, ContinuousOn (fun t => Z t ζ) (Set.Icc 0 T)
  meas : ∀ t, Measurable (Z t)
  gaussian : ∀ (p : ℕ) (ts : Fin p → ℝ) (φ : Fin p → Euc d → ℝ),
    (∀ a, ts a ∈ Set.Icc 0 T) → (∀ a, IsOscTest m (φ a)) →
    law P (fun ζ => (WithLp.toLp 2 fun a => OscDual.eval (Z (ts a) ζ) (φ a) :
        EuclideanSpace ℝ (Fin p))) =
      ProbabilityTheory.multivariateGaussian 0 (Matrix.of fun a b =>
        C₀ (propagatorW C 0 (ts a) (φ a)) (propagatorW C 0 (ts b) (φ b)) +
          noiseCovW C q (ts a) (ts b) (φ a) (φ b))

/-- The covariance `Cov(Z^t(φ), Z^{t'}(ψ))` of `IsLinearGaussianEvolutionW`. -/
def linearGaussianCov (C : WholeCoeff d) (q : ℝ) (C₀ : (Euc d → ℝ) → (Euc d → ℝ) → ℝ)
    (t t' : ℝ) (φ ψ : Euc d → ℝ) : ℝ :=
  C₀ (propagatorW C 0 t φ) (propagatorW C 0 t' ψ) + noiseCovW C q t t' φ ψ

/-! ### Window paths in `𝓧_T = C([0,T]; B_m)` -/

open Classical in
/-- The window `t ↦ f(a + t)`, `t ∈ [0,T]`, as an element of `𝓧_T`; the zero path if it is not
continuous (the statements below assert measurability/continuity where relevant). -/
def windowPathOf (m T a : ℝ) (f : ℝ → OscDual d m) : OscPath d m T :=
  if h : Continuous fun t : Set.Icc (0 : ℝ) T => f (a + t) then
    (⟨fun t => f (a + t), h⟩ : C(Set.Icc (0 : ℝ) T, OscDual d m))
  else 0

/-- The mean-field-centered window `η_N^{a+·}` scaled by `σ`: `t ↦ σ(μ_N^{a+t} - μ^{a+t}) ∈ B_m`
(`σ = √N` is `η_N`, S line 212), for the particle path `X` and the mean-field densities `ρ`. -/
def flucPathW {Ω : Type*} (m T a σ : ℝ) (X : ℝ≥0 → Ω → EucConfig d N) (ρ : ℝ → Euc d → ℝ) (ζ : Ω) :
    OscPath d m T :=
  windowPathOf m T a fun t =>
    σ • OscDual.ofMeasureDiff m (empirical (X (Real.toNNReal t) ζ)) (withDensityReal (ρ t))

/-- The exactly centered window `ζ_N^{a+·}`, `ζ_N^t = √N(μ_N^t - m_N^t)` with `m_N^t = E μ_N^t` the
actual first marginal (the law of `X_t` under `P`; S lines 211-213). -/
def zetaPathW {Ω : Type*} [MeasurableSpace Ω] (m T a : ℝ) (P : Measure Ω)
    (X : ℝ≥0 → Ω → EucConfig d N) (ζ : Ω) : OscPath d m T :=
  windowPathOf m T a fun t =>
    zetaB m (P.map (X (Real.toNNReal t))) (X (Real.toNNReal t) ζ)

/-- The window `Z^{a+·}` of a `B_m`-valued process. -/
def processWindow {Ω : Type*} (m T a : ℝ) (Z : ℝ → Ω → OscDual d m) (ζ : Ω) : OscPath d m T :=
  windowPathOf m T a fun t => Z t ζ

end HRS.Whole
