import HRS.Energy.Coercivity

/-!
# Commutator estimate: common definitions (packet CM-00)

Skeleton of the proof of `HRS.commutator_estimate` (Proposition 3.32 of the main manuscript), see
`docs/external/commutator-packets.md` for the packet decomposition.

**Import cycle.**  `HRS.Energy.Coercivity` contains both the *definitions* used in the statement of
`commutator_estimate` (lines 1-165: `oNΛ`, `smearScale`, `IsLipschitzVF`, `IsFracDeriv`,
`HasTransportBound`, `commKernel`, `offDiagPairing`, `commQuantity`, `OffDiagIntegrable`) and the
consumer theorems after it, so the final hookup `commutator_estimate := commutator_estimate_of_packets`
requires the orchestrator to split `Coercivity.lean` (see the plan, §8): lines 1-165 go to
`HRS/Energy/CoercivityDefs.lean`, the helper sections of `namespace CoercAux` to
`HRS/Energy/CoercivityAux.lean`, and the *only* line of this directory that mentions
`HRS.Energy.Coercivity` (the import below) is replaced by those two imports.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Commutator

variable {d N : ℕ}

/-- The exponent `β = (d-s)/2` of the Fourier symbol `|ξ|^{-2β}` of the Riesz kernel
(`ĝ(k) = c_{d,s} (2π|k|)^{-(d-s)}`). -/
def bexp (d : ℕ) (s : ℝ) : ℝ := ((d : ℝ) - s) / 2

/-- The scale-free profile of the Riesz kernel at distance `r`: `r^{-s}` for `s ≠ 0` and `-log r`
for `s = 0` (so that `periodicRiesz d s x = selfScale d s ‖x‖ + (smooth)` near `0`,
`periodicRiesz_local_singularity`, `periodicLog_local_singularity`). -/
def selfScale (d : ℕ) (s : ℝ) (r : ℝ) : ℝ := if s = 0 then -Real.log r else r ^ (-s)

/-- Nearest-neighbour distance `min_{j ≠ i} |x_i - x_j|` for the torus distance (`0` if `N ≤ 1`). -/
def nnDist (X : Config d N) (i : Fin N) : ℝ :=
  ⨅ j : {j : Fin N // j ≠ i}, KernelGrad.tdist (X i) (X j)

/-- The cap constant of the smearing radii: `r_i = min(nn_i / 4, θ_* λ)`, `θ_* = 1/8`. -/
def thetaStar : ℝ := 1 / 8

/-- The smearing radii `r_i = min (¼ min_{j≠i} |x_i - x_j|, θ_* λ)`, `λ = (NΛ)^{-1/d}`
(`[RS] (2.17)`, `[HCRS] Cor. 2.14`, with the cap `θ_* λ` instead of `λ` so that the balls fit
into a fundamental box and the radius-dependent constants stay uniform). -/
def smearRadius (Λ : ℝ) (X : Config d N) (i : Fin N) : ℝ :=
  min (nnDist X i / 4) (thetaStar * smearScale d N Λ)

/-- The hypothesis of `‖v‖_*` on the fractional part: `‖|∇|^{(d+1)/2} v‖_{L^{2d/(d-1)}} ≤ F`. -/
def HasFracBound (d : ℕ) (v : Torus d → Euc d) (F : ℝ) : Prop :=
  ∃ w : Torus d → Euc d, IsFracDeriv (((d : ℝ) + 1) / 2) v w ∧
    eLpNorm w (ENNReal.ofReal (2 * d / ((d : ℝ) - 1))) volume ≤ ENNReal.ofReal F

/-- The logarithmic part `1_{s=0} log(NΛ)/(2dN)` of `o_N(Λ)`. -/
def logPart (d : ℕ) (s : ℝ) (Λ : ℝ) (N : ℕ) : ℝ :=
  if s = 0 then Real.log (N * Λ) / (2 * d * N) else 0

/-- The *excess* self-energy of a smeared charge of radius `r`: `r^{-s}` for `s ≠ 0`, and
`log(λ/r) ≥ 0` for `s = 0` (`λ = (NΛ)^{-1/d}`), i.e. the self energy `g(r)` of `[RS] (2.19)` after
subtraction of its value `g(λ) = (1/d) log(NΛ)` at the microscale, which is the `s = 0` part of `o_N`
(`[HCRS] Cor. 2.14`, (2.50): `g(4 r_i/η)` with `η = λ`). -/
def selfExcess (d : ℕ) (s : ℝ) (Λ : ℝ) (N : ℕ) (r : ℝ) : ℝ :=
  if s = 0 then Real.log (smearScale d N Λ / r) else r ^ (-s)

/-! ### Elementary algebra of the correction `o_N` (proved) -/

theorem oNΛ_eq (d : ℕ) (s C₀ Λ : ℝ) (N : ℕ) :
    oNΛ d s C₀ Λ N = logPart d s Λ N + C₀ * aNΛ d s Λ N := by
  unfold oNΛ aNΛ logPart; ring

theorem aNΛ_nonneg (d : ℕ) (s Λ : ℝ) (N : ℕ) (hΛ : 0 ≤ Λ) : 0 ≤ aNΛ d s Λ N := by
  unfold aNΛ; positivity

theorem oNΛ_mono {d : ℕ} {s Λ : ℝ} {N : ℕ} (hΛ : 0 ≤ Λ) {C₀ C₀' : ℝ} (h : C₀ ≤ C₀') :
    oNΛ d s C₀ Λ N ≤ oNΛ d s C₀' Λ N := by
  rw [oNΛ_eq, oNΛ_eq]
  have := aNΛ_nonneg d s Λ N hΛ
  nlinarith

theorem logPart_nonneg {d : ℕ} {s Λ : ℝ} {N : ℕ} (hΛ : 1 ≤ Λ) (hN : 2 ≤ N) :
    0 ≤ logPart d s Λ N := by
  unfold logPart
  split_ifs
  · have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
    have : 1 ≤ (N : ℝ) * Λ := by nlinarith
    exact div_nonneg (Real.log_nonneg this) (by positivity)
  · exact le_rfl

end HRS.Commutator
