/-
# HRS.Equilibrium.RepulsiveDefs — objects for the repulsive logarithmic preparation bound

Package REP-00 of `docs/REPULSIVE_PLAN.md`: the definitions shared by the packages REP-01 … REP-07,
which together prove `HRS.log_prep_repulsive` (Proposition 4.25 `M:O:prop:log-prep`, source lines
5588-5610, repulsive half `0 ≤ γ ≤ B₀`): the torus version of Delgadino-Gvalani-Rosenzweig,
Theorem 2.2(i) (`thm:partitionFunctionBound`, DGR TeX line 504) for the periodic logarithm.

## Mathematical set-up (see the plan, §1)

With `g = periodicRiesz d 0`, `μ = ρ dx` (`0 ≤ ρ ≤ Λ`, `∫ ρ = 1`) and the Hoeffding centering
`g̃(x,y) = g(x-y) - g*μ(x) - g*μ(y) + ∬ g dμ dμ` (`HRS.centeredKernel`), the exponent of the
partition function is

  `-β N F_N(X_N, μ) = -(β/2N) ∑_{i≠j} g̃(x_i,x_j) + (β/N) ∑_i g*μ(x_i) - (β/2) ∬ g dμ dμ`

(`REP-01`, `exponent_eq`).  On the torus `g*μ` is bounded (`HRS.convMeasure_bounded`), so only
the centred two-body statistic has to be controlled.  Following DGR §5.1.2 in the form of the
author's Euclidean Lean proof (`DGRHS.Gaussian.gaussianLogSourceMasterData`), the kernel is split
in the **heat-time** variable of the subordination formula `KernelAux.periodicRiesz_eq_integral`

  `g(x) = subA d 0 ∫_0^∞ t^{d/2-1} Ψ(x,t) dt`,  `Ψ(x,t) = psiFn x t = ∑_{k≠0} e^{-t|k|²} cos(2πk·x)`,

into a near field `(0, α²]` (positive after adding back the zero mode; its one-body potential is
`O(Λ α^d)`), a band `(α², δ²]` (bounded, positive definite, small in `L²`) and a tail `(δ², ∞)`
(bounded, positive definite).  The band, scaled by `2β` and centred, is the kernel fed to the
generic master layer-cake estimate `DGRHS.Concentration.master_uniform_sublinear_exponential_envelope`
(vendored, `external/dgrhs`), with the adaptive near-field scale `adaptiveScale` of
`DGRHS.Gaussian.gaussianLogAdaptiveScale`.

No infrared cutoff `T`, no Fatou limit and no pairing of the one-body term with the low modes is
needed on the torus: the zero Fourier mode is absent from `g` and all nonzero lattice frequencies
have `|k| ≥ 1`, so the tail `(δ², ∞)` is a bounded kernel (`psi_large`).

## Conventions

* `heatWeight d t = t^{d/2-1}` is the Mellin weight of the logarithm (`s = 0`).
* Band kernels are `0` at `x = 0` only when the integral diverges (Bochner junk); every statement
  that uses the value at the origin assumes `0 < a` (absolutely convergent Fourier series).
* `pairKernel f μ (x, y) = centeredKernel f μ x y` is the DGRHS-style kernel on `Torus d × Torus d`.
* `masterKernel d α δ β μ = 2β · (heatBand d α² δ²)~`, `masterCap d α δ β = 1 + 8β C_d log(δ/α)`,
  `exponent d β N μ X = -β N F_N(X, μ)` is literally the integrand of `modNormalizerE`.
-/
import HRS.Equilibrium.PreparationAux
import DGRHS.Concentration.MasterGrowth
import DGRHS.Gaussian.HoeffdingRowL2
import DGRHS.Kernel.Operator
import DGRHS.CLT.SourceExponentCLT

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

namespace Repulsive

/-- The Mellin weight of the periodic logarithm: `t^{d/2 - 1}` (`s = 0` in
`KernelAux.periodicRiesz_eq_integral`). -/
def heatWeight (d : ℕ) (t : ℝ) : ℝ := t ^ ((d : ℝ) / 2 - 1)

/-- Heat-time band `(a, b]` of the periodic logarithm:
`heatBand d a b x = subA d 0 ∫_a^b t^{d/2-1} Ψ(x, t) dt`, with `Ψ = psiFn` the centred heat kernel
(zero mode removed).  For `a = 0` this is the near field; for `0 < a` it is a bounded continuous
positive-definite kernel. -/
def heatBand (d : ℕ) (a b : ℝ) (x : Torus d) : ℝ :=
  KernelAux.subA d 0 * ∫ t in Set.Ioc a b, heatWeight d t * psiFn x t

/-- Heat-time tail `(b, ∞)` of the periodic logarithm (the "low-frequency block"; bounded for
`0 < b` because every nonzero lattice frequency has `|k| ≥ 1`). -/
def heatTail (d : ℕ) (b : ℝ) (x : Torus d) : ℝ :=
  KernelAux.subA d 0 * ∫ t in Set.Ioi b, heatWeight d t * psiFn x t

/-- The near field with the zero mode added back: `subA d 0 ∫_0^a t^{d/2-1} (1 + Ψ(x, t)) dt ≥ 0`
(`1 + Ψ` is the full periodised heat kernel, positive by Poisson summation `theta_images`).
It differs from `heatBand d 0 a` by the constant `heatPosMass d a`. -/
def heatPos (d : ℕ) (a : ℝ) (x : Torus d) : ℝ :=
  KernelAux.subA d 0 * ∫ t in Set.Ioc 0 a, heatWeight d t * (1 + psiFn x t)

/-- Haar mass of `heatPos d a`: `subA d 0 · (2/d) · a^{d/2}`. -/
def heatPosMass (d : ℕ) (a : ℝ) : ℝ := KernelAux.subA d 0 * (2 / (d : ℝ)) * a ^ ((d : ℝ) / 2)

/-- Fourier coefficients of `heatBand d a b`: `0` at `k = 0`, else
`subA d 0 ∫_a^b t^{d/2-1} e^{-t|k|²} dt ≥ 0`. -/
def bandCoeff (d : ℕ) (a b : ℝ) (k : Lattice d) : ℝ :=
  if k = 0 then 0 else
    KernelAux.subA d 0 * ∫ t in Set.Ioc a b, heatWeight d t * Real.exp (-t * Lattice.enorm k ^ 2)

/-- Fourier coefficients of `heatTail d b`. -/
def tailCoeff (d : ℕ) (b : ℝ) (k : Lattice d) : ℝ :=
  if k = 0 then 0 else
    KernelAux.subA d 0 * ∫ t in Set.Ioi b, heatWeight d t * Real.exp (-t * Lattice.enorm k ^ 2)

/-- The lattice theta constant `Θ_d = ∑_{m ∈ ℤ^d} e^{-π²|m|²}` (Poisson summation at `t ≤ 1`). -/
def thetaConst (d : ℕ) : ℝ := ∑' m : Lattice d, Real.exp (-(Real.pi ^ 2 * Lattice.enorm m ^ 2))

/-- Constant of the sup bound of a band: `|heatBand d a b x| ≤ bandSupConst d · log(b/a)` for
`0 < a ≤ b ≤ 1`; `bandSupConst d = subA d 0 · π^{d/2} · Θ_d` (from `Ψ(0,t) ≤ (π/t)^{d/2} Θ_d`). -/
def bandSupConst (d : ℕ) : ℝ := KernelAux.subA d 0 * Real.pi ^ ((d : ℝ) / 2) * thetaConst d

/-- Constant of the `L²(𝕋^d)` bound of a band: `∫ heatBand d a b ² ≤ l2Const d · b^{d/2}` for
`0 < a ≤ b ≤ 1/2`.  It comes from the weighted Cauchy-Schwarz inequality
`c_k² ≤ A² (∫_0^b t^{d/4-1}) (∫_0^b t^{3d/4-1} e^{-2t|k|²})`, the heat-trace bound
`∑_{k≠0} e^{-2t|k|²} ≤ (π/2t)^{d/2} Θ_d` (`2t ≤ 1`) and `∫_0^b t^{d/4-1} dt = (4/d) b^{d/4}`:
`l2Const d = A² (4/d)² (π/2)^{d/2} Θ_d`. -/
def l2Const (d : ℕ) : ℝ :=
  KernelAux.subA d 0 ^ 2 * (4 / (d : ℝ)) ^ 2 * (Real.pi / 2) ^ ((d : ℝ) / 2) * thetaConst d

/-- Row control of the band `(α², δ²]` against a density bounded by `Λ`, uniform in `α`:
`Λ · l2Const d · (δ²)^{d/2}` (analogue of `DGRHS.Gaussian.gaussianLogBandRowControl`). -/
def bandRowControl (d : ℕ) (Λ δ : ℝ) : ℝ := Λ * l2Const d * (δ ^ 2) ^ ((d : ℝ) / 2)

/-- Near-field constant: `Λ · heatPosMass d (α²) = nearConst d Λ · α^d`
(analogue of `DGRHS.Gaussian.gaussianLogShortConstant`). -/
def nearConst (d : ℕ) (Λ : ℝ) : ℝ := Λ * KernelAux.subA d 0 * (2 / (d : ℝ))

/-- The adaptive near-field length scale `min{δ, (u/(A(1+βn)))^{1/d}}`; identical to
`DGRHS.Gaussian.gaussianLogAdaptiveScale` (not vendored), restated here. -/
def adaptiveScale (δ A β n u dr : ℝ) : ℝ := min δ ((u / (A * (1 + β * n))) ^ (1 / dr))

/-- The centred kernel of `f` as a function on pairs (DGRHS convention). -/
def pairKernel {d : ℕ} (f : Torus d → ℝ) (μ : Measure (Torus d)) : Torus d × Torus d → ℝ :=
  fun p => centeredKernel f μ p.1 p.2

/-- The master kernel `q_{N,u} = 2β · (heatBand d α² δ²)~` of DGR eq:logEtaNu, with `α` the
adaptive scale and `δ` the fixed band scale. -/
def masterKernel (d : ℕ) (α δ β : ℝ) (μ : Measure (Torus d)) : Torus d × Torus d → ℝ :=
  fun p => 2 * β * centeredKernel (heatBand d (α ^ 2) (δ ^ 2)) μ p.1 p.2

/-- The deterministic cap `m_{N,u} = 1 + 8β · bandSupConst d · log(δ/α)` of DGR eq:logEtaNu. -/
def masterCap (d : ℕ) (α δ β : ℝ) : ℝ := 1 + 8 * β * bandSupConst d * Real.log (δ / α)

/-- The exponent `X_N = -β N F_N(X_N, μ)`: literally the integrand of `modNormalizerE`
(`PreparationAux.KE`). -/
def exponent (d : ℕ) (β : ℝ) (N : ℕ) (μ : Measure (Torus d)) (X : Config d N) : ℝ :=
  -β * N * modulatedEnergyKernel (periodicRiesz d 0) X μ

/-- The deterministic offset absorbed into the threshold `U₀` (DGR eq:UbetaLogDef):
`β · (2 · heatTail d δ² 0 + ‖g*μ‖_∞ + |∬ g dμ dμ|/2)`, where `2 · heatTail d δ² 0` bounds the
negative statistic of the centred tail (positive definiteness) and `Ch`, `E` are the one-body
bound and the pair energy. -/
def lowConst (d : ℕ) (β δ Ch E : ℝ) : ℝ := β * (2 * heatTail d (δ ^ 2) 0 + Ch + |E| / 2)

end Repulsive

end HRS

end
