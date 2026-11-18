import HRS.Main.Equilibrium29Spec
import HRS.Uniform.Comparison
import HRS.Uniform.Evolution

/-!
# EQ29 vocabulary (chunk D, row 2.9): definitions for the intermediate packets (sorry-free)

Definitions (and elementary, fully proved lemmas) used by the sorried statements of `HRS/MD/EQ29Spec.lean`.
Namespace `HRS.MD.EQ29`.  TeX = `HRS_periodic_main_20261008T010000Z.tex` (M), proof of Theorem 2.9,
L3984-4163 (`P:sec:stationary-proof`).

## Definitions

* `pairKernel d s φ`: the pair kernel `h_φ = h_{∇φ}(x,y) = (∇φ(x) - ∇φ(y)) · ∇g(x-y)` (`commKernel` of the Riesz
  gradient and `∇φ`), TeX L4003.
* `kernelField h ν`: `H_{ν,φ}(x) = ∫ h_φ(x,y) dν(y)`, TeX L4004.
* `statRemainder d s V β ρβ φ X`: the stationary remainder `𝓡^t_{N,stat}(φ)` evaluated at the configuration
  `X = X_N^t`, TeX `P:eq:stationary-R` (L4013-4017):
  `ζ_N(H_{μ,φ} - H_{m_N,φ}) - (√N/2)(D_N(h_φ; m_N)(X) - E_{ℙ_{N,β}}[D_N(h_φ; m_N)])`,
  `ζ_N(ψ) = √N(μ_N(ψ) - m_N(ψ))`, `μ = μ_β = ρβ dx`, `m_N = firstMarginal ℙ_{N,β}`, `D_N(h;ν) = quadStat h ν`
  (`A:eq:D-definition`; `D_N(h;ν) = 2 F_N^h(X_N,ν)`, i.e. `2 * modulatedEnergy`).
* `statForcingCoord`: the `k`-th real coordinate `∫_0^t 𝓡_{stat}^r(U^{r,t} e_k) dr` of the integrated remainder
  `∫_0^t 𝒱^{t,r} 𝓡^r_{stat} dr` (analogue of `evolvingForcingCoord`, `HRS/Sections/Sec5.lean`, with the stationary
  remainder and the frozen coefficient `ρ_β`).
* `coordEnergy M c`: `∑_k ⟨k⟩^{-2M} c_k²` in `ℝ≥0∞` (the squared `E_M`-norm of the sequence of Fourier coordinates;
  `∞` if the series diverges, so no `tsum` junk).
* `bracketBias d s N`: `b_N = N^{-1/2} + δ_N` (TeX L4051-4058; `E|(μ_N^r - μ)(b)| ≤ C b_N ‖b‖_∞`).
* `retVec`, `retTarget`: the finite-dimensional vectors of `ui_comparison` (1) (packet EQ-RET).

## Elementary lemmas (proved)

`bracketBias_le_sqrt_deltaN` (`b_N ≤ 2 ε_N`, `ε_N = √δ_N`) and `sqrt_bracketBias_le` (`√b_N ≤ N^{-1/4} + ε_N`):
the two numerical facts `b_N ≤ Cε_N`, `√b_N ≤ N^{-1/4}+ε_N` used at TeX L4096-4097.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

namespace MD

namespace EQ29

variable {d : ℕ}

/-- The pair kernel `h_φ = h_{∇φ}`, `h_φ(x,y) = (∇φ(x) - ∇φ(y)) · ∇g(x-y)` (zero on the diagonal), for the periodic
Riesz/log kernel `g` with parameter `s` (TeX L4003). -/
def pairKernel (d : ℕ) (s : ℝ) (φ : Torus d → ℝ) : Torus d → Torus d → ℝ :=
  commKernel (periodicRieszGrad d s) (Torus.grad φ)

/-- `H_{ν}(x) = ∫ h(x,y) dν(y)` (TeX L4004, with `h = h_φ`). -/
def kernelField (h : Torus d → Torus d → ℝ) (ν : Measure (Torus d)) (x : Torus d) : ℝ :=
  ∫ y, h x y ∂ν

/-- The stationary remainder `𝓡_{N,stat}(φ)` at the configuration `X` (TeX `P:eq:stationary-R`, L4013-4017):
`ζ_N(H_{μ,φ} - H_{m_N,φ}) - (√N/2)(D_N(h_φ; m_N)(X) - E_{ℙ_{N,β}} D_N(h_φ; m_N))`, with
`ζ_N(ψ) = √N(∫ψ dμ_N - ∫ψ dm_N)` (`μ_N = empirical X`), `μ = ρβ dx`, `m_N = firstMarginal ℙ_{N,β}` and `E_{ℙ_{N,β}}`
the expectation under the canonical Gibbs law (a deterministic constant). -/
def statRemainder (d : ℕ) (s : ℝ) (V : Torus d → ℝ) (β : ℝ) (ρβ : Torus d → ℝ) {N : ℕ}
    (φ : Torus d → ℝ) (X : Config d N) : ℝ :=
  Real.sqrt N *
      (∫ x, (kernelField (pairKernel d s φ) (withDensityReal ρβ) x -
          kernelField (pairKernel d s φ) (firstMarginal (canonicalGibbs (periodicRiesz d s) V N β)) x)
          ∂(empirical X) -
        ∫ x, (kernelField (pairKernel d s φ) (withDensityReal ρβ) x -
          kernelField (pairKernel d s φ) (firstMarginal (canonicalGibbs (periodicRiesz d s) V N β)) x)
          ∂(firstMarginal (canonicalGibbs (periodicRiesz d s) V N β))) -
    (Real.sqrt N / 2) *
      (quadStat (pairKernel d s φ) (firstMarginal (canonicalGibbs (periodicRiesz d s) V N β)) X -
        ∫ Y, quadStat (pairKernel d s φ) (firstMarginal (canonicalGibbs (periodicRiesz d s) V N β)) Y
          ∂(canonicalGibbs (periodicRiesz d s) V N β))

/-- The `k`-th real coordinate `⟨∫_0^t 𝒱^{t,r} 𝓡_{stat}^r dr, e_k⟩ = ∫_0^t 𝓡_{stat}^r(U^{r,t} e_k) dr` of the
integrated stationary remainder, where `U^{r,t} = propagator (mfData ..) (fun _ => ρβ) r t` is the adjoint propagator
of the frozen coefficient `ρ_β` and `X r.toNNReal ω` the configuration at time `r` (cf. `evolvingForcingCoord`). -/
def statForcingCoord (d : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (V : Torus d → ℝ) {β : ℝ} (hβ : 0 < β)
    (ρβ : Torus d → ℝ) {Ω : Type*} {N : ℕ} (X : ℝ≥0 → Ω → Config d N) (k : NonzeroLattice d) (t : ℝ)
    (ω : Ω) : ℝ :=
  ∫ r in (0 : ℝ)..t,
    statRemainder d s V β ρβ (N := N)
      (propagator (PDE.mfData d s hs0 hsd V β hβ) (fun _ => ρβ) r t (Torus.realMode k))
      (X r.toNNReal ω)

/-- `∑_k ⟨k⟩^{-2M} c_k²` in `ℝ≥0∞`: the squared `E_M`-norm of an element with real Fourier coordinates `c`
(`∞` if not in `E_M`; exactly the expression of `adjk_remainder_L1` / TeX `‖·‖²_{E_M}`). -/
def coordEnergy (M : ℝ) (c : NonzeroLattice d → ℝ) : ℝ≥0∞ :=
  ∑' k : NonzeroLattice d, ENNReal.ofReal (Lattice.jp k.1 ^ (-2 * M) * c k ^ 2)

/-- The bracket-bias rate `b_N = N^{-1/2} + δ_N` of TeX `P:eq:stationary-bracket-bias` (L4051-4053):
`(μ_N^r - μ)(b) = N^{-1/2} ζ_N^r(b) + (m_N - μ)(b)`, and `E|(μ_N^r - μ)(b)| ≤ C b_N ‖b‖_∞`. -/
def bracketBias (d : ℕ) (s : ℝ) (N : ℕ) : ℝ := (N : ℝ) ^ (-(1 : ℝ) / 2) + deltaN d s N

/-- The vector `(⟨φ_a, ζ_N^{t_a}⟩)_a` of `ui_comparison` (1), centered at the invariant Gibbs marginal
(`linCoord (firstMarginal ℙ_{N,β}) φ_a` at the configuration `X (t a)`). -/
def retVec (d : ℕ) (s : ℝ) (V : Torus d → ℝ) (β : ℝ) {Ω : Type*} {N : ℕ} {p : ℕ}
    (φ : Fin p → Torus d → ℝ) (X : ℝ≥0 → Ω → Config d N) (t : Fin p → ℝ) (ω : Ω) :
    EuclideanSpace ℝ (Fin p) :=
  WithLp.toLp 2 fun a =>
    linCoord (firstMarginal (canonicalGibbs (periodicRiesz d s) V N β)) (φ a) (X (t a).toNNReal ω)

/-- The target `Ψ_Φ(x) = ∫ Φ((⟨U^{0,t_a}φ_a, ζ°(x)⟩)_a + g) d𝒩(0,Σ)(g)` of `ui_comparison` (1): transported
initial field plus independent Gaussian noise with covariance `noiseCovMatrix` (frozen coefficient `ρβ`, `q = β⁻¹`).
`⟨ψ, ζ°(x)⟩ = linCoord (firstMarginal ℙ_{N,β}) ψ x`. -/
def retTarget (d : ℕ) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (V : Torus d → ℝ) (β : ℝ) (hβ : 0 < β)
    (ρβ : Torus d → ℝ) {N : ℕ} {p : ℕ} (φ : Fin p → Torus d → ℝ) (t : Fin p → ℝ)
    (Φ : EuclideanSpace ℝ (Fin p) → ℝ) (x : Config d N) : ℝ :=
  ∫ g, Φ ((WithLp.toLp 2 fun a =>
      linCoord (firstMarginal (canonicalGibbs (periodicRiesz d s) V N β))
        (propagator (PDE.mfData d s hs0 hsd V β hβ) (fun _ => ρβ) 0 (t a) (φ a)) x :
        EuclideanSpace ℝ (Fin p)) + g)
    ∂(ProbabilityTheory.multivariateGaussian 0
      (noiseCovMatrix (PDE.mfData d s hs0 hsd V β hβ) (fun _ => ρβ) β⁻¹ t φ))

/-- The deterministic shift `√N (m_{N,β}(φ) - μ_β(φ))` between the two centerings of the linear statistic:
`linCoord (withDensityReal ρβ) φ X = linCoord (firstMarginal ℙ_{N,β}) φ X + centerShift d s V β ρβ φ N`
(`√N(μ_N(φ) - μ(φ)) = √N(μ_N(φ) - m_N(φ)) + √N(m_N(φ) - μ(φ))`; TeX L988-991, L3961-3964). -/
def centerShift (d : ℕ) (s : ℝ) (V : Torus d → ℝ) (β : ℝ) (ρβ : Torus d → ℝ) (φ : Torus d → ℝ)
    (N : ℕ) : ℝ :=
  Real.sqrt N * (pair (firstMarginal (canonicalGibbs (periodicRiesz d s) V N β)) φ -
    pair (withDensityReal ρβ) φ)

/-! ### Elementary lemmas (proved) -/

/-- `1 ≤ N δ_N` for `N ≥ 1` and `s ≥ 0` (the three branches of `deltaN`). -/
theorem one_le_mul_deltaN' {s : ℝ} (hs0 : 0 ≤ s) {N : ℕ} (hN : 1 ≤ N) :
    1 ≤ (N : ℝ) * deltaN d s N := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  unfold deltaN
  split_ifs with h1 h2
  · rw [mul_inv_cancel₀ hNpos.ne']
  · rw [← mul_assoc, mul_inv_cancel₀ hNpos.ne', one_mul, Real.log_mul (Real.exp_pos _).ne' hNpos.ne',
      Real.log_exp]
    have : 0 ≤ Real.log N := Real.log_nonneg hN1
    linarith
  · have hs : (d : ℝ) / 2 < s := lt_of_le_of_ne (not_lt.mp h1) (Ne.symm h2)
    have hspos : 0 < s := by
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      linarith
    have hds : (d : ℝ) / s ≤ 2 := by
      rw [div_le_iff₀ hspos]; linarith
    have : (N : ℝ) * (N : ℝ) ^ (1 - (d : ℝ) / s) = (N : ℝ) ^ (2 - (d : ℝ) / s) := by
      rw [show (2 : ℝ) - (d : ℝ) / s = 1 + (1 - (d : ℝ) / s) by ring, Real.rpow_add hNpos,
        Real.rpow_one]
    rw [this]
    exact Real.one_le_rpow hN1 (by linarith)

/-- The two centerings of the linear statistic differ by the deterministic `centerShift` (algebra). -/
theorem linCoord_eq_add_centerShift (s : ℝ) (V : Torus d → ℝ) (β : ℝ) (ρβ φ : Torus d → ℝ) {N : ℕ}
    (X : Config d N) :
    linCoord (withDensityReal ρβ) φ X =
      linCoord (firstMarginal (canonicalGibbs (periodicRiesz d s) V N β)) φ X +
        centerShift d s V β ρβ φ N := by
  unfold linCoord centerShift
  ring

/-- `b_N ≤ 2 ε_N`, `ε_N = √δ_N` (TeX L4096: "`b_N ≤ Cε_N`"). -/
theorem bracketBias_le_sqrt_deltaN (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {N : ℕ}
    (hN : 1 ≤ N) : bracketBias d s N ≤ 2 * Real.sqrt (deltaN d s N) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have h1 := one_le_mul_deltaN' (d := d) hs0 hN
  have hδ0 : 0 ≤ deltaN d s N := by
    unfold deltaN
    split_ifs
    · positivity
    · have : 0 ≤ Real.log (Real.exp 1 * N) := Real.log_nonneg (by
        have := Real.add_one_le_exp (1 : ℝ)
        nlinarith)
      positivity
    · positivity
  have hδ1 : deltaN d s N ≤ 1 := MarginalAux.deltaN_le_one hs0 hsd hd N hN
  -- `N^{-1/2} ≤ √δ_N`
  have hA : (N : ℝ) ^ (-(1 : ℝ) / 2) ≤ Real.sqrt (deltaN d s N) := by
    have hrw : (N : ℝ) ^ (-(1 : ℝ) / 2) = Real.sqrt ((N : ℝ)⁻¹) := by
      rw [Real.sqrt_eq_rpow, Real.inv_rpow hNpos.le, ← Real.rpow_neg hNpos.le]
      congr 1; ring
    rw [hrw]
    apply Real.sqrt_le_sqrt
    rw [inv_le_iff_one_le_mul₀' hNpos]
    exact h1
  have hB : deltaN d s N ≤ Real.sqrt (deltaN d s N) := by
    calc deltaN d s N = Real.sqrt (deltaN d s N) * Real.sqrt (deltaN d s N) :=
          (Real.mul_self_sqrt hδ0).symm
      _ ≤ Real.sqrt (deltaN d s N) * 1 := by
          gcongr
          rw [Real.sqrt_le_one]
          exact hδ1
      _ = Real.sqrt (deltaN d s N) := mul_one _
  unfold bracketBias
  linarith

/-- `√b_N ≤ N^{-1/4} + ε_N` (TeX L4097). -/
theorem sqrt_bracketBias_le {s : ℝ} {N : ℕ} (hN : 1 ≤ N) (hδ : 0 ≤ deltaN d s N) :
    Real.sqrt (bracketBias d s N) ≤ (N : ℝ) ^ (-(1 : ℝ) / 4) + Real.sqrt (deltaN d s N) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hx0 : 0 ≤ (N : ℝ) ^ (-(1 : ℝ) / 4) := Real.rpow_nonneg hNpos.le _
  have hsq : ((N : ℝ) ^ (-(1 : ℝ) / 4)) ^ 2 = (N : ℝ) ^ (-(1 : ℝ) / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
    congr 1; norm_num
  rw [Real.sqrt_le_left (by positivity)]
  have hy := Real.sq_sqrt hδ
  unfold bracketBias
  nlinarith [Real.sqrt_nonneg (deltaN d s N)]

end EQ29

end MD

end HRS
