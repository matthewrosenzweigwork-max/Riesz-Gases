import HRS.Whole.Oscillator
import HRS.Energy.Modulated

/-!
# Whole-space foundations III: kernel, modulated energy, Gibbs laws, thermal equilibrium,
rates, smallness class, admissible decaying densities

Source: HRS whole-space supplement (S) and, where the supplement refers to it, the periodic
main paper (M).

* Normalisation (S lines 217-226, `W:r2:normalization`): `d ≥ 2`; `g(x) = |x|^{-s}` for
  `0 < s < d`, `g(x) = -log|x|` for `s = 0`; "no factor `1/s` and no periodic zero-Fourier-mode
  convention"; `F_N^g(X_N,μ) = (2N²)⁻¹ ∑_{i≠j} g(x_i-x_j) - μ_N(g*μ) + ½ μ^{⊗2}(g)`,
  `μ_N = N⁻¹ ∑ δ_{x_i}`; "deleted diagonals are always the particle pair diagonal".
* Section S7 setup (S lines 5268-5300): `S:eq:modulated-energy` (`N⁻² ∑_{i<j}`, the same
  quantity), `S:eq:modulated-law` `dQ_{N,β}(μ) = e^{-βN F_N}/K_{N,β}(μ) dμ^{⊗N}`,
  `m_N = Q^{(1)} = E[μ_N]`; `S:eq:response` `P_μ f = f - μ(f)`, `K_μ f = P_μ[g*(fμ)]`,
  `R_{β,μ} = (I+βK_μ)^{-1}` on `L²_0(μ)`.  The normaliser is the main paper's
  `H:eq:modulated-gibbs` (M lines 446-452): `K_{N,β₀}(μ) = ∫ e^{-β₀ N F_N} dμ^{⊗N}`.
* Centerings (S lines 211-216): `m_N^t = E μ_N^t`, `η_N^t = √N(μ_N^t - μ^t)`,
  `ζ_N^t = √N(μ_N^t - m_N^t)`.
* Centered pair functional `W:eq:euc-D` (S lines 940-944).
* Quadratic confinement `V(x) = a|x|²/2`, `a > 0` (S lines 166, 318); the canonical Gibbs
  ensemble `P_N ∝ exp[-β(∑_i V(x_i) + N⁻¹ ∑_{i<j} g(x_i-x_j))] dX_N` (S lines 1375-1376;
  M `H:eq:canonical`, lines 907-912).
* Thermal equilibrium: free energy `W:eq:euc-free-energy` (S lines 1352-1356), thermal
  equation `W:eq:euc-thermal-bounds` first display (S line 1360; M `H:eq:thermal-equation`,
  lines 915-918).  Existence/uniqueness is `W:prop:euc-thermal` (S3.4, package S-STAT-01).
* Rates `W:r2:rate-summary` (S lines 302-309): `δ_N`, `o_N` coincide literally with the main
  paper's (M lines 551, 720-735), so `HRS.deltaN`, `HRS.oN` are reused;
  `H:eq:whole-general-localization` (S lines 371-374) and
  `H:eq:whole-explicit-localization` (S lines 342-345).
* Smallness class `H:eq:whole-smallness` (S lines 318-336) and `m = 24d + 240` (S line 338).
* Definition S.A.1 `B:def:decaying-density` (S lines 9809-9842); `m_*` is not defined in the
  supplement, it is the main paper's `B:eq:mstar-def` `m_* = ⌊d/2⌋ + 3` (M line 10158).

## Representation decisions

* The kernel `rieszKernel d s` is defined pointwise with the exact normalisation; at `x = 0`
  Lean's `0^(-s) = 0` and `-log 0 = 0` are junk values, never load-bearing (the energy deletes
  the diagonal and integrals are against measures with densities).
* Convolutions, energies and the Gibbs normaliser are Bochner integrals (junk `0` when not
  integrable; integrability is a hypothesis where needed), as on the torus.
* `R_{β,μ}` is represented by the response equation `h + βK_μ h = P_μ ψ`, `μ(h) = 0`
  (`IsResponse`) and `Classical.choose` (`responseInverse`), as on the torus (ISSUES K4).
* The thermal equilibrium is a *predicate* (`IsThermalDensity`: probability density solving
  the thermal equation) and a predicate `IsFreeEnergyMinimizer` (minimiser of
  `W:eq:euc-free-energy` among finite-free-energy probability densities); `thermalDensity`
  picks a solution by choice when one exists (`0` otherwise).  Nothing here assumes
  existence, uniqueness, tails or smoothness: these are the S3.4 targets.
* The smallness class is a `Prop`-structure with exactly the source's conditions
  (`ψ ∈ C_c^∞`, `ψ ≠ 0`, `μ_β(ψ) = 0`, the `C_b^{100d+1001}` norm (project SUM convention,
  `HRS.cbNorm`) plus the `Σ^{102d+1020}` norm of `√ρ_β ψ` at most `ε_*`); `ε = 0` is allowed.
* Definition S.A.1 is an inductive type with the two source choices (A)/(B) as constructors
  carrying exactly the stated parameter constraints; `r_𝔠, p_𝔠, e_N^𝔠, m_𝔠, Γ_𝔠` are functions
  of it, and the three embedding claims of the last sentence are separate sorried theorems.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform

namespace HRS.Whole

variable {d N : ℕ}

/-! ### Configurations, empirical measure, pairings -/

/-- A configuration `X_N = (x_1,…,x_N)` of `N` particles in `ℝ^d`. -/
abbrev EucConfig (d N : ℕ) := Fin N → Euc d

/-- The empirical measure `μ_N = N⁻¹ ∑_i δ_{x_i}` (S line 223). -/
def empirical (X : EucConfig d N) : Measure (Euc d) :=
  ((N : ℝ≥0∞)⁻¹) • ∑ i : Fin N, Measure.dirac (X i)

/-- `μ(φ) = ∫ φ dμ`. -/
def pair (μ : Measure (Euc d)) (φ : Euc d → ℝ) : ℝ := ∫ x, φ x ∂μ

/-- `⟨f, g⟩_{L²(μ)}`. -/
def l2Inner (μ : Measure (Euc d)) (f g : Euc d → ℝ) : ℝ := ∫ x, f x * g x ∂μ

/-- `P_μ f = f - μ(f)` (`S:eq:response`, line 5296; S line 221). -/
def projMean (μ : Measure (Euc d)) (f : Euc d → ℝ) : Euc d → ℝ := fun x => f x - pair μ f

/-- The measure `ρ dx`. -/
def withDensityReal (ρ : Euc d → ℝ) : Measure (Euc d) :=
  volume.withDensity fun x => ENNReal.ofReal (ρ x)

/-- A probability density on `ℝ^d`. -/
structure IsProbDensity (ρ : Euc d → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ ρ x
  measurable : Measurable ρ
  integral_one : ∫ x, ρ x = 1

/-! ### The whole-space Riesz / logarithmic kernel (`W:r2:normalization`, S lines 217-226) -/

/-- `g(x) = |x|^{-s}` for `s ≠ 0`, `g(x) = -log|x|` for `s = 0`: no factor `1/s`, no zero-mode
adjustment.  Junk value at `x = 0`. -/
def rieszKernel (d : ℕ) (s : ℝ) (x : Euc d) : ℝ :=
  if s = 0 then -Real.log ‖x‖ else ‖x‖ ^ (-s)

/-- The force `∇g` (Mathlib's `gradient`; junk at `0`). -/
def rieszKernelGrad (d : ℕ) (s : ℝ) (x : Euc d) : Euc d := gradient (rieszKernel d s) x

/-- `g * μ (x) = ∫ g(x-y) dμ(y)`. -/
def convMeasure (g : Euc d → ℝ) (μ : Measure (Euc d)) (x : Euc d) : ℝ := ∫ y, g (x - y) ∂μ

/-- `g * f (x) = ∫ g(x-y) f(y) dy`. -/
def convFun (g f : Euc d → ℝ) (x : Euc d) : ℝ := ∫ y, g (x - y) * f y

/-- `∬ g(x-y) dν(x) dν'(y)`. -/
def energyPairing (g : Euc d → ℝ) (ν ν' : Measure (Euc d)) : ℝ := ∫ x, ∫ y, g (x - y) ∂ν' ∂ν

/-! ### Modulated energy and modulated Gibbs law -/

/-- The modulated energy `F_N^g(X_N, μ) = (2N²)⁻¹ ∑_{i≠j} g(x_i-x_j) - μ_N(g*μ) + ½ μ^{⊗2}(g)`
(`W:r2:normalization`, S lines 221-226), with the literal deleted particle diagonal and the
factor `½` on the background term. -/
def modulatedEnergy (g : Euc d → ℝ) (X : EucConfig d N) (μ : Measure (Euc d)) : ℝ :=
  (1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, g (X i - X j)
    - (1 / (N : ℝ)) * ∑ i, convMeasure g μ (X i)
    + (1 / 2) * energyPairing g μ μ

/-- `F_N` for the whole-space Riesz/log kernel with parameters `d, s`. -/
def rieszModulatedEnergy (d : ℕ) (s : ℝ) (X : EucConfig d N) (μ : Measure (Euc d)) : ℝ :=
  modulatedEnergy (rieszKernel d s) X μ

/-- The normaliser `K_{N,β}(μ) = ∫ e^{-βN F_N^g} dμ^{⊗N}` (`S:eq:modulated-law`, S lines
5285-5288; M lines 446-452). -/
def gibbsNormalizer (g : Euc d → ℝ) (N : ℕ) (β : ℝ) (μ : Measure (Euc d)) : ℝ :=
  ∫ X : EucConfig d N, Real.exp (-β * N * modulatedEnergy g X μ) ∂(Measure.pi fun _ => μ)

/-- The modulated Gibbs law `Q_{N,β}(μ) = K_{N,β}(μ)⁻¹ e^{-βN F_N^g(X_N,μ)} μ^{⊗N}`
(`S:eq:modulated-law`); `Q_{N,0}(μ) = μ^{⊗N}` (S line 395). -/
def modulatedGibbs (g : Euc d → ℝ) (N : ℕ) (β : ℝ) (μ : Measure (Euc d)) :
    Measure (EucConfig d N) :=
  (ENNReal.ofReal (gibbsNormalizer g N β μ))⁻¹ •
    (Measure.pi fun _ => μ).withDensity
      fun X => ENNReal.ofReal (Real.exp (-β * N * modulatedEnergy g X μ))

/-- The centered pair functional `D_N(h;ν) = N⁻² ∑_{i≠j} h(x_i,x_j) - 2 μ_N(∫ h(·,y) dν(y))
+ ∬ h dν^{⊗2}` of `W:eq:euc-D` (S lines 940-944), "with the original deleted particle
diagonal". -/
def centeredPairFunctional (h : Euc d → Euc d → ℝ) (X : EucConfig d N) (ν : Measure (Euc d)) :
    ℝ :=
  (1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, h (X i) (X j)
    - 2 * ((1 / (N : ℝ)) * ∑ i, ∫ y, h (X i) y ∂ν)
    + ∫ x, ∫ y, h x y ∂ν ∂ν

/-! ### Canonical Gibbs ensemble with quadratic confinement -/

/-- The confinement `V(x) = a|x|²/2` (S lines 166, 318). -/
def confinement (a : ℝ) (x : Euc d) : ℝ := a * ‖x‖ ^ 2 / 2

/-- `H_N(X_N) = ∑_i V(x_i) + N⁻¹ ∑_{i<j} g(x_i-x_j)` (S lines 1375-1376). -/
def canonicalHamiltonian (g V : Euc d → ℝ) (X : EucConfig d N) : ℝ :=
  ∑ i, V (X i) +
    (1 / (N : ℝ)) * ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), g (X i - X j)

/-- `Z_{N,β} = ∫ e^{-β H_N} dX_N` (Lebesgue measure on `(ℝ^d)^N`). -/
def canonicalPartition (g V : Euc d → ℝ) (N : ℕ) (β : ℝ) : ℝ :=
  ∫ X : EucConfig d N, Real.exp (-β * canonicalHamiltonian g V X)

/-- The canonical Gibbs ensemble `P_{N,β} = Z⁻¹ e^{-β H_N} dX_N`. -/
def canonicalGibbs (g V : Euc d → ℝ) (N : ℕ) (β : ℝ) : Measure (EucConfig d N) :=
  (ENNReal.ofReal (canonicalPartition g V N β))⁻¹ •
    (volume : Measure (EucConfig d N)).withDensity
      fun X => ENNReal.ofReal (Real.exp (-β * canonicalHamiltonian g V X))

/-! ### Marginals, centerings, equilibrium operators -/

open Classical in
/-- The first marginal `P^{(1)}` (`0` if `N = 0`). -/
def firstMarginal (P : Measure (EucConfig d N)) : Measure (Euc d) :=
  if h : 0 < N then P.map (fun X => X ⟨0, h⟩) else 0

/-- Exchangeability of a law on `(ℝ^d)^N`. -/
def IsExchangeable (P : Measure (EucConfig d N)) : Prop :=
  ∀ σ : Equiv.Perm (Fin N), P.map (fun X => X ∘ σ) = P

/-- The actual first marginal `m_N = E[μ_N]` (S line 211; `S:eq:modulated-law`). -/
def meanEmpirical (P : Measure (EucConfig d N)) : Measure (Euc d) := P.bind empirical

/-- `μ_N - μ` in `B_m`. -/
def flucB (m : ℝ) (X : EucConfig d N) (μ : Measure (Euc d)) : OscDual d m :=
  OscDual.ofMeasureDiff m (empirical X) μ

/-- Mean-field centering `η_N = √N(μ_N - μ)` in `B_m` (S line 212). -/
def etaB (m : ℝ) (X : EucConfig d N) (μ : Measure (Euc d)) : OscDual d m :=
  Real.sqrt N • flucB m X μ

/-- Exact centering `ζ_N = √N(μ_N - m_N)` in `B_m`, `m_N = E_P[μ_N]` (S line 213). -/
def zetaB (m : ℝ) (P : Measure (EucConfig d N)) (X : EucConfig d N) : OscDual d m :=
  Real.sqrt N • OscDual.ofMeasureDiff m (empirical X) (meanEmpirical P)

/-- `K_μ f = P_μ[g*(fμ)]` (`S:eq:response`, line 5296). -/
def Kop (g : Euc d → ℝ) (μ : Measure (Euc d)) (f : Euc d → ℝ) : Euc d → ℝ :=
  projMean μ fun x => ∫ y, g (x - y) * f y ∂μ

/-- The response equation for `h = R_{β,μ} P_μ ψ = (I+βK_μ)^{-1} P_μ ψ` on `L²_0(μ)`:
`h ∈ L²_0(μ)` and `h + βK_μ h = P_μ ψ` (`S:eq:response`). -/
def IsResponse (g : Euc d → ℝ) (μ : Measure (Euc d)) (β : ℝ) (ψ h : Euc d → ℝ) : Prop :=
  MemL2Zero μ h ∧ ∀ᵐ x ∂μ, h x + β * Kop g μ h x = projMean μ ψ x

open Classical in
/-- `R_{β,μ} P_μ ψ`: the solution of the response equation (`0` if none exists). -/
def responseInverse (g : Euc d → ℝ) (μ : Measure (Euc d)) (β : ℝ) (ψ : Euc d → ℝ) :
    Euc d → ℝ :=
  if h : ∃ h, IsResponse g μ β ψ h then h.choose else 0

/-- The susceptibility covariance form `C_{β,μ}(φ,ψ) = ⟨P_μ φ, R_{β,μ} P_μ ψ⟩_{L²(μ)}`
(S line 174 refers to the main paper's `H:eq:susceptibility`). -/
def susceptibilityCov (g : Euc d → ℝ) (μ : Measure (Euc d)) (β : ℝ) (φ ψ : Euc d → ℝ) : ℝ :=
  l2Inner μ (projMean μ φ) (responseInverse g μ β ψ)

/-! ### Thermal equilibrium (S3.4, `W:prop:euc-thermal`, S lines 1348-1384) -/

/-- The mean-field free energy
`𝓕(ν) = β⁻¹ ∫ ρ log ρ dx + ∫ V dν + ½ ∬ g(x-y) dν(x) dν(y)`, `ν = ρ dx`
(`W:eq:euc-free-energy`, S lines 1352-1356). -/
def freeEnergy (g V : Euc d → ℝ) (β : ℝ) (ρ : Euc d → ℝ) : ℝ :=
  β⁻¹ * (∫ x, ρ x * Real.log (ρ x)) + (∫ x, V x * ρ x) +
    (1 / 2) * (∫ x, ∫ y, g (x - y) * ρ x * ρ y)

/-- Finiteness of the three terms of the free energy (so that the Bochner integrals in
`freeEnergy` are the source's integrals). -/
def HasFiniteFreeEnergy (g V : Euc d → ℝ) (ρ : Euc d → ℝ) : Prop :=
  Integrable (fun x => ρ x * Real.log (ρ x)) ∧ Integrable (fun x => V x * ρ x) ∧
    Integrable (fun p : Euc d × Euc d => g (p.1 - p.2) * ρ p.1 * ρ p.2)
      ((volume : Measure (Euc d)).prod volume)

/-- `ρ` is a minimiser of the free energy among probability densities with finite free
energy (`W:prop:euc-thermal`: "has a unique minimizer `μ_β`"). -/
def IsFreeEnergyMinimizer (g V : Euc d → ℝ) (β : ℝ) (ρ : Euc d → ℝ) : Prop :=
  IsProbDensity ρ ∧ HasFiniteFreeEnergy g V ρ ∧
    ∀ ρ' : Euc d → ℝ, IsProbDensity ρ' → HasFiniteFreeEnergy g V ρ' →
      freeEnergy g V β ρ ≤ freeEnergy g V β ρ'

/-- The thermal equation `ρ_β(x) = Z⁻¹ e^{-β(V(x) + g*μ_β(x))}`, `μ_β = ρ_β dx`
(`W:eq:euc-thermal-bounds` first display, S line 1360; M `H:eq:thermal-equation`). -/
def IsThermalDensity (g V : Euc d → ℝ) (β : ℝ) (ρ : Euc d → ℝ) : Prop :=
  IsProbDensity ρ ∧
    ∀ x, ρ x = Real.exp (-β * (V x + convMeasure g (withDensityReal ρ) x)) /
      ∫ y, Real.exp (-β * (V y + convMeasure g (withDensityReal ρ) y))

/-- "The actual interacting thermal equilibrium measure" of the quadratic confinement
`V = a|x|²/2` at inverse temperature `β` (S lines 318-320): the minimiser of the mean-field
free energy, which solves the thermal equation for the whole-space kernel
(`W:prop:euc-thermal`, S lines 1357-1360).  Both clauses are what the source *proves* about
`μ_β`; neither existence nor uniqueness is assumed here. -/
def IsThermalEquilibrium (d : ℕ) (s a β : ℝ) (ρ : Euc d → ℝ) : Prop :=
  IsFreeEnergyMinimizer (rieszKernel d s) (confinement a) β ρ ∧
    IsThermalDensity (rieszKernel d s) (confinement a) β ρ

open Classical in
/-- A thermal equilibrium density chosen by `Classical.choose` when one exists (`0`
otherwise).  Existence and uniqueness are the S3.4 target `thermalDensity_spec`, not
assumed here. -/
def thermalDensity (d : ℕ) (s a β : ℝ) : Euc d → ℝ :=
  if h : ∃ ρ, IsThermalEquilibrium d s a β ρ then h.choose else 0

/-- `μ_β = ρ_β dx`. -/
def thermalMeasure (d : ℕ) (s a β : ℝ) : Measure (Euc d) :=
  withDensityReal (thermalDensity d s a β)

/-- The Gaussian comparison density `γ_{βa}(x) = (βa/2π)^{d/2} e^{-βa|x|²/2}`
(`W:eq:euc-thermal-bounds`, S lines 1362-1363). -/
def gaussianComparison (d : ℕ) (a β : ℝ) (x : Euc d) : ℝ :=
  (β * a / (2 * Real.pi)) ^ ((d : ℝ) / 2) * Real.exp (-β * a * ‖x‖ ^ 2 / 2)

/-! ### Rates and localisation costs -/

/-- `δ_N` and `o_N` of `W:r2:rate-summary` (S lines 302-309) coincide literally with the main
paper's (M lines 551, 720-735): `δ_N = N⁻¹` (`0 ≤ s < d/2`), `N⁻¹ log(eN)` (`s = d/2`),
`N^{1-d/s}` (`d/2 < s < d`); `o_N = C₀ N^{s/d-1} + 1_{s=0} log N/(2dN)`.  They are
`HRS.deltaN d s N` and `HRS.oN d s C₀ N`, reused without redefinition. -/
theorem deltaN_eq (d : ℕ) (s : ℝ) (N : ℕ) :
    deltaN d s N =
      if s < (d : ℝ) / 2 then (N : ℝ)⁻¹
      else if s = (d : ℝ) / 2 then (N : ℝ)⁻¹ * Real.log (Real.exp 1 * N)
      else (N : ℝ) ^ (1 - (d : ℝ) / s) := by
  rfl

/-- The explicit localisation rate `w_N = (N^{-1/d} + √o_N)^{4/(d+4)}` of the concrete
quadratic family (`H:eq:whole-explicit-localization`, S lines 342-345). -/
def localizationRate (d : ℕ) (s C₀ : ℝ) (N : ℕ) : ℝ :=
  ((N : ℝ) ^ (-(1 / (d : ℝ))) + Real.sqrt (oN d s C₀ N)) ^ (4 / ((d : ℝ) + 4))

/-- The general covariance localisation cost
`w_N = inf_{R ≥ 1} { R^{d/2}(N^{-1/d} + √𝔈_N) + (1+M₂) R^{-2} }`
(`H:eq:whole-general-localization`, S lines 371-374), with `𝔈_N` the energy error and `M₂`
the second-moment bound. -/
def generalLocalizationRate (d : ℕ) (energyError M₂ : ℝ) (N : ℕ) : ℝ :=
  ⨅ R : {R : ℝ // 1 ≤ R},
    R.1 ^ ((d : ℝ) / 2) * ((N : ℝ) ^ (-(1 / (d : ℝ))) + Real.sqrt energyError) +
      (1 + M₂) * R.1 ^ (-(2 : ℝ))

/-- The spatial index `m = 24d + 240` of Theorem `H:thm:whole-space` (S line 338). -/
def wholeSpaceIndex (d : ℕ) : ℕ := 24 * d + 240

/-! ### The smallness class `H:eq:whole-smallness` (S lines 318-336) -/

/-- The perturbed initial density `(1 + εψ) ρ_β` (S line 324). -/
def perturbedDensity (ρβ : Euc d → ℝ) (ε : ℝ) (ψ : Euc d → ℝ) (x : Euc d) : ℝ :=
  (1 + ε * ψ x) * ρβ x

/-- The nonlinear preparation class of S lines 322-336: `ψ ∈ C_c^∞(ℝ^d)` nonzero with
`μ_β(ψ) = 0`, and the smallness
`‖εψ‖_{C_b^{100d+1001}} + ‖ε√ρ_β ψ‖_{Σ^{102d+1020}} ≤ ε_*` (`H:eq:whole-smallness`).
The `C_b^k` norm is the project's SUM convention (`HRS.cbNorm`, M line 510 / S line 295).
`ε = 0` is included (S line 335). -/
structure IsAdmissiblePerturbation (ρβ : Euc d → ℝ) (εstar ε : ℝ) (ψ : Euc d → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ ψ
  compactSupport : HasCompactSupport ψ
  nonzero : ψ ≠ 0
  meanZero : ∫ x, ψ x * ρβ x = 0
  small : cbNorm (100 * d + 1001) (fun x => ε * ψ x) +
    oscNorm (102 * (d : ℝ) + 1020) (fun x => ε * Real.sqrt (ρβ x) * ψ x) ≤ εstar

/-! ### Definition S.A.1: admissible decaying commutator densities
(`B:def:decaying-density`, S lines 9809-9842) -/

/-- `m_* = ⌊d/2⌋ + 3` (main paper `B:eq:mstar-def`, M line 10158; the supplement uses `m_*`
without redefining it). -/
def mStar (d : ℕ) : ℕ := d / 2 + 3

/-- Definition S.A.1: a choice of commutator regularity and error, `𝔠 = (r_𝔠, p_𝔠, e_N^𝔠)`,
is one of two choices.  Standing assumptions of the definition: `0 ≤ s < d - 2` (carried by
the theorems that use it).
* (A) sharp-rate density: `d < a < min{d+2, 2s+4}`, `r = a/2`, `p = 2d/(a-2)`, `e_N = 0`;
* (B) lower-regularity, slower-rate density: `s > (d-4)/3`, `r = (d-s)/2`,
  `p = 2d/(d-s-2)`, `e_N = (1 + 1_{s=0} log N) N^{-2/((s+1)(s+2))}`. -/
inductive DecayingDensity (d : ℕ) (s : ℝ) : Type
  | sharp (a : ℝ) (ha : (d : ℝ) < a ∧ a < min ((d : ℝ) + 2) (2 * s + 4)) : DecayingDensity d s
  | lower (hs : ((d : ℝ) - 4) / 3 < s) : DecayingDensity d s

namespace DecayingDensity

variable {s : ℝ}

/-- `r_𝔠`. -/
def regularity : DecayingDensity d s → ℝ
  | sharp a _ => a / 2
  | lower _ => ((d : ℝ) - s) / 2

/-- `p_𝔠`. -/
def integrability : DecayingDensity d s → ℝ
  | sharp a _ => 2 * (d : ℝ) / (a - 2)
  | lower _ => 2 * (d : ℝ) / ((d : ℝ) - s - 2)

/-- `e_N^𝔠`. -/
def errorRate : DecayingDensity d s → ℕ → ℝ
  | sharp _ _ => fun _ => 0
  | lower _ => fun N =>
      (1 + (if s = 0 then Real.log N else 0)) * (N : ℝ) ^ (-(2 / ((s + 1) * (s + 2))))

/-- `m_𝔠 = m_* + ⌊d/p_𝔠⌋ + 1`. -/
def sobolevIndex (c : DecayingDensity d s) : ℕ :=
  mStar d + ⌊(d : ℝ) / c.integrability⌋₊ + 1

/-- `Γ_𝔠 = m_𝔠 + 2 + ⌊d(1/2 - 1/p_𝔠)⌋ + 1` (`B:eq:gamma-density`). -/
def gammaIndex (c : DecayingDensity d s) : ℕ :=
  c.sobolevIndex + 2 + ⌊(d : ℝ) * (1 / 2 - 1 / c.integrability)⌋₊ + 1

end DecayingDensity

/-- The fractional derivative `|∇|^r v = 𝓕⁻¹[(2π|ξ|)^r 𝓕v]` (Mathlib's `𝓕` has the `2π` in
the phase), real part taken.  WARNING: junk value `0` if `v ∉ L¹` (and for a non-integrable product); use `IsFracDerivRep`
(`HRS/Whole/Adjoint.lean`) in statements. -/
def fracGradPow (r : ℝ) (v : Euc d → ℝ) (x : Euc d) : ℝ :=
  (𝓕⁻ (fun ξ : Euc d => ((2 * Real.pi * ‖ξ‖) ^ r : ℝ) * 𝓕 (fun y : Euc d => (v y : ℂ)) ξ) x).re

/-- `‖f‖_{L^p}` of a real function (Bochner form `(∫ |f|^p)^{1/p}`). -/
def lpNorm (p : ℝ) (f : Euc d → ℝ) : ℝ := (∫ x, |f x| ^ p) ^ (1 / p)

/-- The commutator norm `‖v‖_𝔠 = ‖∇v‖_{L^∞} + ‖ |∇|^{r_𝔠} v ‖_{L^{p_𝔠}}` of a vector field
(S lines 9829-9831), with `|∇|^r` applied componentwise.  WARNING: junk value `0` for the `L^p` term when `v ∉ L¹` (Mathlib's `𝓕` of a
non-integrable function is `0`) and `0` for an unbounded sup: do NOT use in statements; use `HasFracTransportBound`
(`HRS/Whole/AppendixBEnergy.lean`) instead. -/
def commutatorNorm {s : ℝ} (c : DecayingDensity d s) (v : Euc d → Euc d) : ℝ :=
  (⨆ x, ‖fderiv ℝ v x‖) +
    (∫ x, (∑ i, fracGradPow c.regularity (fun y => v y i) x ^ 2) ^ (c.integrability / 2)) ^
      (1 / c.integrability)

/-- The `W^{m,p}(ℝ^d)` norm `∑_{j ≤ m} ‖D^j f‖_{L^p}` (multilinear operator norms). -/
def sobolevWNorm (m : ℕ) (p : ℝ) (f : Euc d → ℝ) : ℝ :=
  ∑ j ∈ Finset.range (m + 1), (∫ x, ‖iteratedFDeriv ℝ j f x‖ ^ p) ^ (1 / p)

/-! ### Facts (work package SFOUND-01 unless marked) -/

section Facts

variable {s : ℝ}

/-! #### Helper lemmas (not part of the specification) -/

theorem modulatedEnergy_perm (g : Euc d → ℝ) (X : EucConfig d N) (μ : Measure (Euc d))
    (σ : Equiv.Perm (Fin N)) :
    modulatedEnergy g (X ∘ σ) μ = modulatedEnergy g X μ := by
  unfold modulatedEnergy
  have h1 : ∑ i, ∑ j ∈ Finset.univ.erase i, g ((X ∘ σ) i - (X ∘ σ) j) =
      ∑ i, ∑ j ∈ Finset.univ.erase i, g (X i - X j) := by
    simp_rw [← Finset.filter_ne', Finset.sum_filter]
    let F : Fin N → Fin N → ℝ := fun a b => if b ≠ a then g (X a - X b) else 0
    have : ∀ i j, (if j ≠ i then g ((X ∘ σ) i - (X ∘ σ) j) else 0) = F (σ i) (σ j) := by
      intro i j
      simp only [F, Function.comp, ne_eq, σ.apply_eq_iff_eq]
    simp_rw [this]
    rw [Equiv.sum_comp σ (fun a => ∑ j, F a (σ j))]
    exact Finset.sum_congr rfl fun a _ => Equiv.sum_comp σ (fun b => F a b)
  have h2 : ∑ i, convMeasure g μ ((X ∘ σ) i) = ∑ i, convMeasure g μ (X i) :=
    Equiv.sum_comp σ (fun i => convMeasure g μ (X i))
  rw [h1, h2]


theorem map_withDensity_of_invariant {α : Type*} [MeasurableSpace α] (ν : Measure α)
    (T : α ≃ᵐ α) (hν : ν.map T = ν) (f : α → ℝ≥0∞) (hf : ∀ x, f (T x) = f x) :
    (ν.withDensity f).map T = ν.withDensity f := by
  ext A hA
  rw [Measure.map_apply T.measurable hA, withDensity_apply _ (T.measurable hA),
    withDensity_apply _ hA, ← lintegral_indicator (T.measurable hA),
    ← lintegral_indicator hA]
  have h1 : ∀ x, (T ⁻¹' A).indicator f x = A.indicator f (T x) := by
    intro x
    by_cases hx : T x ∈ A
    · simp [Set.indicator_of_mem, hx, hf]
    · simp [Set.indicator_of_notMem, hx]
  simp_rw [h1]
  conv_rhs => rw [← hν]
  exact (T.measurableEmbedding.lintegral_map (A.indicator f)).symm


theorem pi_outer_perm_le {E : Type*} [MeasurableSpace E] (μ : Measure E) (σ : Equiv.Perm (Fin N))
    (A : Set (Fin N → E)) :
    OuterMeasure.pi (fun _ : Fin N => μ.toOuterMeasure) ((fun X : Fin N → E => X ∘ σ) ⁻¹' A) ≤
      OuterMeasure.pi (fun _ : Fin N => μ.toOuterMeasure) A := by
  have h : OuterMeasure.map (fun X : Fin N → E => X ∘ σ)
      (OuterMeasure.pi (fun _ : Fin N => μ.toOuterMeasure)) ≤
      OuterMeasure.pi (fun _ : Fin N => μ.toOuterMeasure) := by
    rw [OuterMeasure.le_pi]
    intro t _
    rw [OuterMeasure.map_apply]
    have : (fun X : Fin N → E => X ∘ σ) ⁻¹' (Set.pi Set.univ t) =
        Set.pi Set.univ (fun j => t (σ.symm j)) := by
      ext X
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, Function.comp]
      constructor
      · intro hX j; simpa using hX (σ.symm j)
      · intro hX i; simpa using hX (σ i)
    rw [this]
    refine (OuterMeasure.pi_pi_le _ _).trans ?_
    exact le_of_eq (Equiv.prod_comp σ.symm (fun i => μ.toOuterMeasure (t i)))
  have := h A
  rwa [OuterMeasure.map_apply] at this

theorem pi_map_perm {E : Type*} [MeasurableSpace E] (μ : Measure E) (σ : Equiv.Perm (Fin N)) :
    (Measure.pi fun _ : Fin N => μ).map (fun X : Fin N → E => X ∘ σ) =
      Measure.pi fun _ : Fin N => μ := by
  have hT : ∀ τ : Equiv.Perm (Fin N), Measurable (fun X : Fin N → E => X ∘ τ) :=
    fun τ => measurable_pi_iff.2 fun i => measurable_pi_apply (τ i)
  ext A hA
  rw [Measure.map_apply (hT σ) hA]
  have e : ∀ B : Set (Fin N → E), MeasurableSet B →
      Measure.pi (fun _ : Fin N => μ) B =
        OuterMeasure.pi (fun _ : Fin N => μ.toOuterMeasure) B := by
    intro B hB
    rw [Measure.pi_def, toMeasure_apply _ _ hB]
  rw [e _ ((hT σ) hA), e _ hA]
  refine le_antisymm (pi_outer_perm_le μ σ A) ?_
  have := pi_outer_perm_le μ σ⁻¹ ((fun X : Fin N → E => X ∘ σ) ⁻¹' A)
  convert this using 2
  ext X
  simp [Function.comp_def]


def permEquiv {E : Type*} [MeasurableSpace E] (σ : Equiv.Perm (Fin N)) :
    (Fin N → E) ≃ᵐ (Fin N → E) where
  toFun X := X ∘ σ
  invFun X := X ∘ σ.symm
  left_inv X := by ext i; simp
  right_inv X := by ext i; simp
  measurable_toFun := measurable_pi_iff.2 fun i => measurable_pi_apply (σ i)
  measurable_invFun := measurable_pi_iff.2 fun i => measurable_pi_apply (σ.symm i)

theorem measurable_empirical : Measurable (empirical : EucConfig d N → Measure (Euc d)) := by
  refine Measure.measurable_of_measurable_coe _ fun A hA => ?_
  have : ∀ X : EucConfig d N, empirical X A = (N : ℝ≥0∞)⁻¹ * ∑ i, A.indicator 1 (X i) := by
    intro X
    simp [empirical, Measure.dirac_apply' _ hA]
  simp_rw [this]
  refine Measurable.const_mul (Finset.measurable_sum _ fun i _ => ?_) _
  exact (measurable_one.indicator hA).comp (measurable_pi_apply i)

theorem meanEmpirical_apply (P : Measure (EucConfig d N)) {A : Set (Euc d)} (hA : MeasurableSet A) :
    meanEmpirical P A = (N : ℝ≥0∞)⁻¹ * ∑ i : Fin N, P {X | X i ∈ A} := by
  unfold meanEmpirical
  rw [Measure.bind_apply hA measurable_empirical.aemeasurable]
  have : ∀ X : EucConfig d N, empirical X A = (N : ℝ≥0∞)⁻¹ * ∑ i, A.indicator 1 (X i) := by
    intro X
    simp [empirical, Measure.dirac_apply' _ hA]
  simp_rw [this]
  have hm : Measurable fun X : EucConfig d N => ∑ i, A.indicator (1 : Euc d → ℝ≥0∞) (X i) :=
    Finset.measurable_sum _ fun i _ => (measurable_one.indicator hA).comp (measurable_pi_apply i)
  rw [lintegral_const_mul _ hm]
  rw [lintegral_finsetSum Finset.univ (f := fun (i : Fin N) (X : EucConfig d N) =>
    A.indicator (1 : Euc d → ℝ≥0∞) (X i))
    (fun i _ => (measurable_one.indicator hA).comp (measurable_pi_apply i))]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have : ∀ X : EucConfig d N, A.indicator (1 : Euc d → ℝ≥0∞) (X i) = ({X | X i ∈ A}).indicator 1 X := by
    intro X; by_cases h : X i ∈ A <;> simp [h]
  simp_rw [this]
  rw [lintegral_indicator_one]
  exact (measurable_pi_apply i) hA


theorem meanEmpirical_isProbabilityMeasure (P : Measure (EucConfig d N)) [IsProbabilityMeasure P]
    (hN : 1 ≤ N) : IsProbabilityMeasure (meanEmpirical P) := by
  constructor
  have := meanEmpirical_apply P (MeasurableSet.univ : MeasurableSet (Set.univ : Set (Euc d)))
  rw [this]
  simp only [Set.mem_univ, Set.setOf_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, measure_univ, mul_one]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast (show N ≠ 0 by omega)) (by simp)

theorem tendsto_natCast_rpow_zero_iff (e : ℝ) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ e) atTop (𝓝 0) ↔ e < 0 := by
  constructor
  · intro h
    by_contra hnot
    rw [not_lt] at hnot
    have h1 : ∀ᶠ N : ℕ in atTop, (1 : ℝ) ≤ (N : ℝ) ^ e := by
      filter_upwards [eventually_ge_atTop 1] with N hN
      exact Real.one_le_rpow (by exact_mod_cast hN) hnot
    have := ge_of_tendsto h h1
    linarith
  · intro he
    exact (tendsto_rpow_neg_atTop (by linarith : 0 < -e)).comp tendsto_natCast_atTop_atTop |>.congr
      (fun N => by simp)

theorem tendsto_sqrt_mul_inv : Tendsto (fun N : ℕ => Real.sqrt N * (N : ℝ)⁻¹) atTop (𝓝 0) := by
  have := (tendsto_natCast_rpow_zero_iff (-(1/2))).2 (by norm_num)
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_one, ← Real.rpow_add hN']
  norm_num

theorem tendsto_sqrt_mul_inv_log : Tendsto (fun N : ℕ => Real.sqrt N * ((N : ℝ)⁻¹ * Real.log (Real.exp 1 * N))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => Real.log x / x ^ (1/2 : ℝ)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ) < 1/2)).tendsto_div_nhds_zero
  have h2 : Tendsto (fun x : ℝ => x ^ (-(1/2) : ℝ)) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by norm_num)
  have h3 := (h1.add h2).comp tendsto_natCast_atTop_atTop
  simp only [add_zero] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  simp only [Function.comp]
  rw [Real.log_mul (Real.exp_pos 1).ne' hN'.ne', Real.log_exp, Real.sqrt_eq_rpow]
  have e1 : (N : ℝ) ^ (-(1/2) : ℝ) = ((N : ℝ) ^ (1/2 : ℝ))⁻¹ := Real.rpow_neg hN'.le _
  have e2 : (N : ℝ) = (N : ℝ) ^ (1/2 : ℝ) * (N : ℝ) ^ (1/2 : ℝ) := by
    rw [← Real.rpow_add hN']; norm_num
  have hp : 0 < (N : ℝ) ^ (1/2 : ℝ) := Real.rpow_pos_of_pos hN' _
  rw [e1]
  field_simp
  have e3 : ((N : ℝ) ^ (1/2 : ℝ)) ^ 2 = N := by rw [sq, ← e2]
  rw [e3]; ring

theorem cbNorm_const_mul (k : ℕ) (ε : ℝ) (ψ : Euc d → ℝ) (hψ : ContDiff ℝ ∞ ψ) :
    cbNorm k (fun x => ε * ψ x) = |ε| * cbNorm k ψ := by
  unfold cbNorm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : ∀ x, iteratedFDeriv ℝ j (fun y => ε * ψ y) x = ε • iteratedFDeriv ℝ j ψ x := by
    intro x
    have := iteratedFDeriv_const_smul_apply (𝕜 := ℝ) (a := ε) (f := ψ) (x := x) (i := j)
      (hψ.contDiffAt.of_le (by exact_mod_cast le_top))
    simpa [Pi.smul_def] using this
  simp_rw [h1, norm_smul, Real.norm_eq_abs]
  rw [Real.mul_iSup_of_nonneg (abs_nonneg ε)]

/-- `g` is even. -/
theorem rieszKernel_neg (x : Euc d) : rieszKernel d s (-x) = rieszKernel d s x := by
  unfold rieszKernel; simp [norm_neg]

/-- `g` is smooth away from the origin. -/
theorem rieszKernel_contDiffOn : ContDiffOn ℝ ∞ (rieszKernel d s) {x | x ≠ 0} := by
  intro x hx
  have hx' : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  have hn : ContDiffAt ℝ ∞ (fun y : Euc d => ‖y‖) x := contDiffAt_norm ℝ hx
  unfold rieszKernel
  by_cases h : s = 0
  · simp only [h, if_true]
    exact (hn.log hx').neg.contDiffWithinAt
  · simp only [h, if_false]
    exact (hn.rpow_const_of_ne hx').contDiffWithinAt

/-- `g` is locally integrable for `s < d`. -/
theorem rieszKernel_locallyIntegrable (hs0 : 0 ≤ s) (hsd : s < d) :
    LocallyIntegrable (rieszKernel d s) (volume : Measure (Euc d)) := by
  have hd : 0 < d := by
    have : (0 : ℝ) < d := lt_of_le_of_lt hs0 hsd
    exact_mod_cast this
  have : Nontrivial (Euc d) := by
    rw [← Module.finrank_pos_iff (R := ℝ)]; simpa using hd
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_ball (0 : Euc d)
  refine IntegrableOn.mono_set ?_ hR
  let F : ℝ → ℝ := fun r => if s = 0 then -Real.log r else r ^ (-s)
  have hF : rieszKernel d s = fun x => F ‖x‖ := rfl
  rw [hF, integrableOn_fun_norm_addHaar volume]
  simp only [finrank_euclideanSpace_fin]
  rcases le_or_gt R 0 with hR0 | hR0
  · rw [Set.Ioo_eq_empty (by linarith)]; exact integrableOn_empty
  by_cases h : s = 0
  · simp only [F, h, if_true]
    have h1 : IntervalIntegrable (fun y : ℝ => y ^ (d - 1) * -Real.log y) volume 0 R :=
      (intervalIntegral.intervalIntegrable_log'.neg).continuousOn_mul (by fun_prop)
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hR0.le] at h1
    simpa [smul_eq_mul] using h1
  · simp only [F, h, if_false]
    have h1 : IntervalIntegrable (fun y : ℝ => y ^ ((d : ℝ) - 1 - s)) volume 0 R :=
      intervalIntegral.intervalIntegrable_rpow' (by linarith)
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hR0.le] at h1
    refine h1.congr_fun (fun y hy => ?_) measurableSet_Ioo
    have hy0 : 0 < y := hy.1
    show y ^ ((d : ℝ) - 1 - s) = y ^ (d - 1) • y ^ (-s)
    rw [smul_eq_mul, show (d : ℝ) - 1 - s = ((d - 1 : ℕ) : ℝ) + (-s) by
      rw [Nat.cast_sub hd]; push_cast; ring, Real.rpow_add hy0, Real.rpow_natCast]

/-- `g(x) > 0` for `s > 0`, `x ≠ 0`. -/
theorem rieszKernel_pos (hs : 0 < s) (x : Euc d) (hx : x ≠ 0) : 0 < rieszKernel d s x := by
  unfold rieszKernel
  rw [if_neg hs.ne']
  exact Real.rpow_pos_of_pos (norm_pos_iff.2 hx) _

/-- `S:eq:modulated-energy` (S lines 5279-5283) writes `N⁻² ∑_{i<j}`; it is the same
quantity as `(2N²)⁻¹ ∑_{i≠j}` of `W:r2:normalization`. -/
theorem modulatedEnergy_eq_sum_lt (g : Euc d → ℝ) (hg : ∀ x, g (-x) = g x) (X : EucConfig d N)
    (μ : Measure (Euc d)) :
    modulatedEnergy g X μ =
      (1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), g (X i - X j)
        - (1 / (N : ℝ)) * ∑ i, convMeasure g μ (X i) + (1 / 2) * energyPairing g μ μ := by
  unfold modulatedEnergy
  have h1 : ∀ i : Fin N, ∑ j ∈ Finset.univ.erase i, g (X i - X j) =
      ∑ j, (if i < j then g (X i - X j) else 0) + ∑ j, (if j < i then g (X i - X j) else 0) := by
    intro i
    rw [← Finset.sum_add_distrib, ← Finset.filter_ne', Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    rcases lt_trichotomy i j with h | h | h
    · simp [h, h.ne', not_lt_of_gt h]
    · simp [h]
    · simp [h, h.ne, not_lt_of_gt h]
  have h2 : ∑ i, ∑ j, (if j < i then g (X i - X j) else 0) =
      ∑ i, ∑ j, (if i < j then g (X i - X j) else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs
    · rw [← hg (X j - X i), neg_sub]
    · rfl
  have h3 : ∑ i, ∑ j ∈ Finset.univ.erase i, g (X i - X j) =
      2 * ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), g (X i - X j) := by
    simp_rw [h1, Finset.sum_add_distrib, h2, Finset.sum_filter]
    ring
  rw [h3]
  by_cases hN : (N : ℝ) = 0
  · simp [hN]
  · field_simp

/-- `μ_N(φ) = N⁻¹ ∑_i φ(x_i)`. -/
theorem pair_empirical (hN : 0 < N) (X : EucConfig d N) (φ : Euc d → ℝ) :
    pair (empirical X) φ = (N : ℝ)⁻¹ * ∑ i, φ (X i) := by
  unfold pair empirical
  rw [integral_smul_measure, integral_finsetSum_measure]
  · simp [integral_dirac, Finset.mul_sum]
  · intro i _
    exact integrable_dirac (by simp)

theorem empirical_isProbabilityMeasure (hN : 0 < N) (X : EucConfig d N) :
    IsProbabilityMeasure (empirical X) := by
  constructor
  simp only [empirical, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, measure_univ,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast hN.ne') (by simp)

/-- `Q_{N,0}(μ) = μ^{⊗N}` (S line 395). -/
theorem modulatedGibbs_zero (g : Euc d → ℝ) (μ : Measure (Euc d)) [IsProbabilityMeasure μ] :
    modulatedGibbs g N 0 μ = Measure.pi fun _ : Fin N => μ := by
  unfold modulatedGibbs gibbsNormalizer
  simp

/-- The modulated Gibbs law is exchangeable. -/
theorem modulatedGibbs_isExchangeable (g : Euc d → ℝ) (β : ℝ) (μ : Measure (Euc d))
    (hg : ∀ x, g (-x) = g x) : IsExchangeable (modulatedGibbs g N β μ) := by
  intro σ
  unfold modulatedGibbs
  have h1 : (fun X : EucConfig d N => X ∘ σ) = ⇑(permEquiv (E := Euc d) σ) := rfl
  have key := map_withDensity_of_invariant (Measure.pi fun _ : Fin N => μ) (permEquiv σ)
    (pi_map_perm μ σ)
    (fun X : EucConfig d N => ENNReal.ofReal (Real.exp (-β * N * modulatedEnergy g X μ)))
    (fun X => by
      show ENNReal.ofReal (Real.exp (-β * N * modulatedEnergy g (X ∘ σ) μ)) = _
      rw [modulatedEnergy_perm])
  rw [h1, Measure.map_smul, key]
  exact (permEquiv σ).measurable.aemeasurable

/-- For exchangeable laws `m_N` is the first marginal (`S:eq:modulated-law`,
`m_N = Q^{(1)} = E[μ_N]`). -/
theorem meanEmpirical_eq_firstMarginal (P : Measure (EucConfig d N)) [IsProbabilityMeasure P]
    (hP : IsExchangeable P) (hN : 1 ≤ N) : meanEmpirical P = firstMarginal P := by
  have hN' : 0 < N := hN
  ext A hA
  have hT : ∀ τ : Equiv.Perm (Fin N), Measurable (fun X : EucConfig d N => X ∘ τ) :=
    fun τ => measurable_pi_iff.2 fun i => measurable_pi_apply (τ i)
  have key : ∀ i : Fin N, P {X | X i ∈ A} = P {X | X ⟨0, hN'⟩ ∈ A} := by
    intro i
    have h := hP (Equiv.swap i ⟨0, hN'⟩)
    have hm : MeasurableSet {X : EucConfig d N | X i ∈ A} := measurable_pi_apply i hA
    calc P {X | X i ∈ A} = (P.map (fun X : EucConfig d N => X ∘ (Equiv.swap i ⟨0, hN'⟩))) {X | X i ∈ A} := by rw [h]
      _ = P {X | X ⟨0, hN'⟩ ∈ A} := by
        rw [Measure.map_apply (hT _) hm]
        congr 1
        ext X
        simp
  rw [meanEmpirical_apply P hA]
  unfold firstMarginal
  rw [dif_pos hN', Measure.map_apply (measurable_pi_apply (⟨0, hN'⟩ : Fin N)) hA]
  simp_rw [key]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact ENNReal.inv_mul_cancel_left (by exact_mod_cast hN'.ne') (by simp)

/-- `η_N = ζ_N + √N(m_N - μ)` in `B_m` for `m > d` (M `H:eq:centering-decomposition`, used
with whole-space centerings at S lines 211-216). -/
theorem eta_eq_zeta_add (m : ℝ) (hm : (d : ℝ) < m) (P : Measure (EucConfig d N))
    [IsProbabilityMeasure P] (μ : Measure (Euc d)) [IsProbabilityMeasure μ] (X : EucConfig d N)
    (hN : 1 ≤ N) :
    etaB m X μ = zetaB m P X + Real.sqrt N • OscDual.ofMeasureDiff m (meanEmpirical P) μ := by
  haveI : IsProbabilityMeasure (empirical X) := empirical_isProbabilityMeasure hN X
  haveI : IsProbabilityMeasure (meanEmpirical P) := meanEmpirical_isProbabilityMeasure P hN
  unfold etaB zetaB flucB
  rw [← smul_add]
  congr 1
  refine OscDual.ext_hermiteCoeff fun α => ?_
  rw [OscDual.hermiteCoeff_add, OscDual.hermiteCoeff_ofMeasureDiff hm,
    OscDual.hermiteCoeff_ofMeasureDiff hm, OscDual.hermiteCoeff_ofMeasureDiff hm]
  ring

/-- `η_N`, `ζ_N` have zero mass in the sense of `OscDual.HasZeroMass` (S lines 217-218), for
`m > d`. -/
theorem etaB_hasZeroMass (m : ℝ) (hm : (d : ℝ) < m) (hN : 0 < N) (X : EucConfig d N)
    (μ : Measure (Euc d)) [IsProbabilityMeasure μ] : OscDual.HasZeroMass (etaB m X μ) := by
  haveI : IsProbabilityMeasure (empirical X) := empirical_isProbabilityMeasure hN X
  unfold etaB flucB OscDual.HasZeroMass
  have h : OscDual.HasMass (OscDual.ofMeasureDiff m (empirical X) μ) 0 :=
    OscDual.hasZeroMass_ofMeasureDiff hm (empirical X) μ
  have h2 := OscDual.HasMass.smul h (Real.sqrt N)
  rw [mul_zero] at h2
  exact h2

/-- `P_{N,β} = Q_{N,β}(μ_β)` exactly for the thermal equilibrium density (S lines 1375-1378;
package S-STAT-01). -/
theorem canonicalGibbs_eq_modulatedGibbs (g V : Euc d → ℝ) (β : ℝ) (ρ : Euc d → ℝ)
    (hρ : IsThermalDensity g V β ρ) (hg : ∀ x, g (-x) = g x)
    (hint : ∀ x, Integrable (fun y => g (x - y)) (withDensityReal ρ)) :
    canonicalGibbs g V N β = modulatedGibbs g N β (withDensityReal ρ) := by
  sorry

/-- `W:prop:euc-thermal` (S lines 1348-1360), existence/uniqueness part: for `a > 0`,
`β > 0`, `0 < s < d`, the free energy has a unique minimiser, it is a (bounded) thermal
density, and the thermal equation determines it; hence `thermalDensity` is that minimiser.
(Target of package S-STAT-01; recorded here because it is what makes `thermalDensity`
meaningful.  `d ≥ 2` is the supplement's standing assumption, S line 217.) -/
theorem thermalDensity_spec (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) (a β : ℝ) (ha : 0 < a)
    (hβ : 0 < β) :
    (∃ ρ : Euc d → ℝ, IsThermalEquilibrium d s a β ρ ∧ ∃ C, ∀ x, ρ x ≤ C) ∧
      (∀ ρ ρ' : Euc d → ℝ, IsFreeEnergyMinimizer (rieszKernel d s) (confinement a) β ρ →
        IsFreeEnergyMinimizer (rieszKernel d s) (confinement a) β ρ' → ρ =ᵐ[volume] ρ') ∧
      (∀ ρ : Euc d → ℝ, IsFreeEnergyMinimizer (rieszKernel d s) (confinement a) β ρ →
        ρ =ᵐ[volume] thermalDensity d s a β) := by
  sorry

/-- `o_N` and `δ_N` of `W:r2:rate-summary` are the main paper's (S lines 302-309 vs
M line 551): `o_N = C₀ N^{s/d-1} + 1_{s=0} log N/(2dN)`. -/
theorem oN_eq (C₀ : ℝ) : oN d s C₀ N =
    C₀ * (N : ℝ) ^ (s / d - 1) + (if s = 0 then Real.log N / (2 * d * N) else 0) := by
  rfl

/-- "The pressure remainder `√N δ_N` vanishes precisely in `s < 2d/3`" (S lines 311-312),
for `0 ≤ s < d`. -/
theorem sqrt_mul_deltaN_tendsto_zero_iff (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    Tendsto (fun N : ℕ => Real.sqrt N * deltaN d s N) atTop (𝓝 0) ↔ s < 2 * (d : ℝ) / 3 := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  by_cases h1 : s < (d : ℝ) / 2
  · have : s < 2 * (d : ℝ) / 3 := by linarith
    simp only [deltaN, h1, if_true]
    exact ⟨fun _ => this, fun _ => tendsto_sqrt_mul_inv⟩
  by_cases h2 : s = (d : ℝ) / 2
  · have : s < 2 * (d : ℝ) / 3 := by linarith
    simp only [deltaN, h1, h2, lt_self_iff_false, if_false, if_true]
    exact ⟨fun _ => by linarith, fun _ => tendsto_sqrt_mul_inv_log⟩
  · have hs : (d : ℝ) / 2 < s := lt_of_le_of_ne (not_lt.1 h1) (Ne.symm h2)
    have hspos : 0 < s := by linarith
    have hfun : ∀ N : ℕ, 1 ≤ N → Real.sqrt N * deltaN d s N = (N : ℝ) ^ ((3 : ℝ) / 2 - d / s) := by
      intro N hN
      have hN' : (0 : ℝ) < N := by exact_mod_cast hN
      simp only [deltaN, h1, h2, if_false]
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hN']
      congr 1; ring
    have hiff : ((3 : ℝ) / 2 - d / s < 0) ↔ s < 2 * (d : ℝ) / 3 := by
      rw [sub_neg, lt_div_iff₀ hspos]
      constructor <;> intro h <;> linarith
    rw [← hiff, ← tendsto_natCast_rpow_zero_iff]
    refine tendsto_congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact hfun N hN

/-- Every fixed `ψ ∈ C_c^∞`, nonzero with `μ_β(ψ) = 0`, enters the smallness class for
`|ε|` small (S lines 334-335), provided `√ρ_β ψ ∈ Σ^{102d+1020}`. -/
theorem isAdmissiblePerturbation_of_small (ρβ : Euc d → ℝ) (εstar : ℝ) (hε : 0 < εstar)
    (ψ : Euc d → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (h0 : ψ ≠ 0)
    (hmean : ∫ x, ψ x * ρβ x = 0)
    (hosc : MemOsc (102 * (d : ℝ) + 1020) fun x => Real.sqrt (ρβ x) * ψ x) :
    ∃ ε₀ > 0, ∀ ε : ℝ, |ε| ≤ ε₀ → IsAdmissiblePerturbation ρβ εstar ε ψ := by
  set A := cbNorm (100 * d + 1001) ψ with hA
  set B := oscNorm (102 * (d : ℝ) + 1020) fun x => Real.sqrt (ρβ x) * ψ x with hB
  have hA0 : 0 ≤ A := by
    refine Finset.sum_nonneg fun j _ => Real.iSup_nonneg fun x => norm_nonneg _
  have hB0 : 0 ≤ B := Real.sqrt_nonneg _
  refine ⟨εstar / (A + B + 1), div_pos hε (by linarith), fun ε hε' => ?_⟩
  refine ⟨hψ, hc, h0, hmean, ?_⟩
  have e1 : (fun x => ε * Real.sqrt (ρβ x) * ψ x) = fun x => ε * (Real.sqrt (ρβ x) * ψ x) := by
    funext x; ring
  rw [cbNorm_const_mul _ _ _ hψ, e1, oscNorm_const_mul]
  have hpos : 0 < A + B + 1 := by linarith
  calc |ε| * A + |ε| * B = |ε| * (A + B) := by ring
    _ ≤ (εstar / (A + B + 1)) * (A + B) := mul_le_mul_of_nonneg_right hε' (by linarith)
    _ ≤ εstar := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
      nlinarith

/-- The source's statement (S lines 334-335) for the actual thermal density: every fixed
nonzero `ψ ∈ C_c^∞` with `μ_β(ψ) = 0` enters the class for `|ε|` small (uses the smoothness
and Gaussian bounds of `ρ_β` from `W:prop:euc-thermal`; package S-STAT-01). -/
theorem isAdmissiblePerturbation_thermal (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) (a β : ℝ)
    (ha : 0 < a) (hβ : 0 < β) (εstar : ℝ) (hε : 0 < εstar) (ψ : Euc d → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) (h0 : ψ ≠ 0) (hmean : ∫ x, ψ x * thermalDensity d s a β x = 0) :
    ∃ ε₀ > 0, ∀ ε : ℝ, |ε| ≤ ε₀ → IsAdmissiblePerturbation (thermalDensity d s a β) εstar ε ψ := by
  sorry

namespace DecayingDensity

/-- "In both cases `p_𝔠 (s+1) > d`" (S line 9828), under the standing `0 ≤ s < d - 2`. -/
theorem integrability_mul_gt (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (c : DecayingDensity d s) :
    (d : ℝ) < c.integrability * (s + 1) := by
  have hd : (2 : ℝ) < d := by linarith
  cases c with
  | sharp a ha =>
    obtain ⟨h1, h2⟩ := ha
    have h2a := lt_min_iff.1 h2
    have ha2 : 0 < a - 2 := by linarith
    simp only [DecayingDensity.integrability]
    rw [div_mul_eq_mul_div, lt_div_iff₀ ha2]
    nlinarith [h2a.2]
  | lower hs =>
    have hp : 0 < (d : ℝ) - s - 2 := by linarith
    simp only [DecayingDensity.integrability]
    rw [div_mul_eq_mul_div, lt_div_iff₀ hp]
    nlinarith

/-- "This density exists exactly when `s > (d-4)/2`" (S line 9820). -/
theorem sharp_exists_iff (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    (∃ a : ℝ, (d : ℝ) < a ∧ a < min ((d : ℝ) + 2) (2 * s + 4)) ↔ ((d : ℝ) - 4) / 2 < s := by
  constructor
  · rintro ⟨a, h1, h2⟩
    have := lt_min_iff.1 h2
    linarith [this.2]
  · intro h
    refine exists_between (lt_min (by linarith) (by linarith))

/-- `p_𝔠 > 2` (needed for `Γ_𝔠` to be the source's integer). -/
theorem two_lt_integrability (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (c : DecayingDensity d s) :
    2 < c.integrability := by
  have hd : (2 : ℝ) < d := by linarith
  cases c with
  | sharp a ha =>
    obtain ⟨h1, h2⟩ := ha
    have h2a := lt_min_iff.1 h2
    have ha2 : 0 < a - 2 := by linarith
    simp only [DecayingDensity.integrability]
    rw [lt_div_iff₀ ha2]
    linarith [h2a.1]
  | lower hs =>
    have hp : 0 < (d : ℝ) - s - 2 := by linarith
    simp only [DecayingDensity.integrability]
    rw [lt_div_iff₀ hp]
    linarith

/-- Last sentence of Definition S.A.1, claim 1: `W^{m_𝔠,p_𝔠} ↪ C_b^{m_*}` (stated for smooth
functions with finite `W^{m_𝔠,p_𝔠}` norm, encoded as integrability of `|D^j f|^{p_𝔠}`, `j ≤ m_𝔠`;
without it the Bochner integrals in `sobolevWNorm` take the junk value `0`, e.g. for `f ≡ 1`). -/
theorem sobolev_embeds_cb (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (c : DecayingDensity d s) :
    ∃ C : ℝ, ∀ f : Euc d → ℝ, ContDiff ℝ ∞ f →
      (∀ j ≤ c.sobolevIndex, Integrable (fun x => ‖iteratedFDeriv ℝ j f x‖ ^ c.integrability)) →
      cbNorm (mStar d) f ≤ C * sobolevWNorm c.sobolevIndex c.integrability f := by
  sorry

/- Claim 2 (`‖𝖬^*∇f‖_𝔠 ≤ C ‖f‖_{W^{m_𝔠,p_𝔠}}`) is `HRS.Whole.DecayingDensity.commutatorNorm_le` in
`HRS/Whole/AppendixBEnergy.lean` (repair P10, 2026-10-20: it is stated with the distributional transport bound
`HasFracTransportBound`, defined there, because the Bochner-integral `commutatorNorm`/`fracGradPow` have the junk value `0` for
non-`L¹` input and must not be used in statements). -/

/-- Claim 3: `H^{Γ_𝔠} ↪ W^{m_𝔠+2,p_𝔠}`. -/
theorem h_embeds_sobolev (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (c : DecayingDensity d s) :
    ∃ C : ℝ, ∀ f : Euc d → ℝ, ContDiff ℝ ∞ f →
      (∀ j ≤ c.gammaIndex, Integrable (fun x => ‖iteratedFDeriv ℝ j f x‖ ^ (2 : ℝ))) →
      sobolevWNorm (c.sobolevIndex + 2) c.integrability f ≤ C * sobolevWNorm c.gammaIndex 2 f := by
  sorry

end DecayingDensity

end Facts

end HRS.Whole
