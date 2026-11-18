import HRS.Sections.Sec5
import HRS.Energy.Coercivity
import HRS.Sections.ScrnAux1

/-!
# HRS.Sections.Sec6 — Section 6 (mesoscopic observations and screening): statement drafts

Statement drafts (all proofs are `sorry`) for the rows

* `M:O:prop:screening` (Proposition 6.1, TeX M L7613-7642);
* `M:@remark:L7716` (Remark "Formation at low frequency", TeX M L7716-7718).

## Representation decisions (to be recorded in `docs/ISSUES.md`)

* The periodic gradient diffusion `O:eq:screen-particles` (M L7566-7569) is the gradient dynamics with
  `V = 0` at inverse temperature `β_N` (`PDE.mfData`, `M = -I`, `invβ = β_N⁻¹`), started from independent
  uniform (Haar) positions, with global collision-free strong solutions driven by independent Brownian
  motions independent of the initial positions (`IsVectorBrownian`, `IndepFun`).
* The mesoscopic test `φ_ℓ(x) = ℓ^{-d/2} ∑_z φ((x - x₀ + z)/ℓ)` (`O:eq:meso-test`) is `mesoTest` (the
  sum over `ℤ^d` is a finite sum for compactly supported `φ`, `x₀ ∈ ℝ^d`); `Z_{N,ℓ}^t(φ) =
  √N(μ_N^t - dx)(φ_ℓ)` is `linCoord volume (mesoTest ..) (X t)`.
* The limiting Gaussian evolution `Z` (`O:eq:meso-limit-cov`) is the centered Gaussian family with
  covariance `mesoCovMatrix` (`E[Z^t(φ)Z^u(ψ)] = ∫ φ̂ conj(ψ̂) e^{-(t-u)a_b}[S_b + (1-S_b)e^{-2ua_b}] dξ`
  for `t ≥ u ≥ 0`, symmetric extension otherwise); the Fourier transform is Mathlib's `𝓕`
  (`φ̂(ξ) = ∫ φ(x) e^{-2πi⟨x,ξ⟩} dx`, the convention of the source, `r = 2π|ξ|`) and the integral is real (its
  real part is taken).  The stationary Gaussian evolution with spectral density `S_b` is `mesoStatCovMatrix`.
* `o_N = C₀ N^{-q/d} + 1_{s=0} log N/(2dN)` is `HRS.oN` (the same expression, `q = d - s`).  The source
  fixes `C₀` "sufficiently large" so that `F_N^γ(X_N, dx) + o_N ≥ 0` (`O:eq:meso-o`); this is part of the
  conclusion (`∃ C₀ ≥ 0, ...`).  The two further pointwise inputs `O:eq:meso-comm`, `O:eq:meso-coer` are the
  periodic commutator/coercivity estimates of Propositions 3.32-3.33 and are not restated.
* Constants: `C` depends on `d, s, p`, the tests and the compact interval `[b₋,b₊] ⊂ (0,∞)` containing
  `b_N` and `b`; it is chosen before `N`, `β_N`, `ℓ_N`, `b`, the times and the particle system.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal FourierTransform

namespace HRS

variable {d : ℕ}

/-- The multiplier `a_b(ξ) = b⁻¹ r² + c_{d,s} r^{2-q}`, `r = 2π|ξ|`, `q = d - s` (`O:eq:meso-multipliers`,
M L7586-7589). -/
def mesoRate (d : ℕ) (s b : ℝ) (ξ : Euc d) : ℝ :=
  b⁻¹ * (2 * Real.pi * ‖ξ‖) ^ 2 + rieszConst d s * (2 * Real.pi * ‖ξ‖) ^ (2 - ((d : ℝ) - s))

/-- The equal-time spectral density `S_b(ξ) = r^q/(r^q + b c_{d,s})` (`O:eq:meso-multipliers`). -/
def mesoSpectral (d : ℕ) (s b : ℝ) (ξ : Euc d) : ℝ :=
  (2 * Real.pi * ‖ξ‖) ^ ((d : ℝ) - s) /
    ((2 * Real.pi * ‖ξ‖) ^ ((d : ℝ) - s) + b * rieszConst d s)

/-- The covariance integral `O:eq:meso-limit-cov` (M L7594-7598) for `t ≥ u ≥ 0`:
`∫_{ℝ^d} φ̂(ξ) conj(ψ̂(ξ)) e^{-(t-u)a_b(ξ)}[S_b(ξ) + (1 - S_b(ξ)) e^{-2u a_b(ξ)}] dξ` (real part). -/
def mesoCovIntegral (d : ℕ) (s b t u : ℝ) (φ ψ : Euc d → ℝ) : ℝ :=
  (∫ ξ : Euc d, 𝓕 (fun x => (φ x : ℂ)) ξ * (starRingEnd ℂ) (𝓕 (fun x => (ψ x : ℂ)) ξ) *
    (((Real.exp (-(t - u) * mesoRate d s b ξ) *
      (mesoSpectral d s b ξ + (1 - mesoSpectral d s b ξ) *
        Real.exp (-2 * u * mesoRate d s b ξ)) : ℝ) : ℂ))).re

/-- The covariance matrix of the centered Gaussian evolution `Z` at times `t_a` and tests `φ_a`:
`E[Z^{t_a}(φ_a) Z^{t_c}(φ_c)]` is `mesoCovIntegral` with the later time first. -/
def mesoCovMatrix (d : ℕ) (s b : ℝ) {p : ℕ} (t : Fin p → ℝ) (φ : Fin p → Euc d → ℝ) :
    Matrix (Fin p) (Fin p) ℝ :=
  Matrix.of fun a c =>
    if t c ≤ t a then mesoCovIntegral d s b (t a) (t c) (φ a) (φ c)
    else mesoCovIntegral d s b (t c) (t a) (φ c) (φ a)

/-- The stationary Gaussian evolution with spectral density `S_b`: covariance
`∫ φ̂ conj(ψ̂) e^{-(t-u)a_b} S_b dξ` for `t ≥ u` (the `u → ∞` limit of `mesoCovMatrix`,
M L7641-7642, L7711-7713). -/
def mesoStatCovMatrix (d : ℕ) (s b : ℝ) {p : ℕ} (t : Fin p → ℝ) (φ : Fin p → Euc d → ℝ) :
    Matrix (Fin p) (Fin p) ℝ :=
  Matrix.of fun a c =>
    if t c ≤ t a then
      (∫ ξ : Euc d, 𝓕 (fun x => (φ a x : ℂ)) ξ * (starRingEnd ℂ) (𝓕 (fun x => (φ c x : ℂ)) ξ) *
        (((Real.exp (-(t a - t c) * mesoRate d s b ξ) * mesoSpectral d s b ξ : ℝ) : ℂ))).re
    else
      (∫ ξ : Euc d, 𝓕 (fun x => (φ c x : ℂ)) ξ * (starRingEnd ℂ) (𝓕 (fun x => (φ a x : ℂ)) ξ) *
        (((Real.exp (-(t c - t a) * mesoRate d s b ξ) * mesoSpectral d s b ξ : ℝ) : ℂ))).re

/-- The periodized mesoscopic test `φ_ℓ(x) = ℓ^{-d/2} ∑_{z∈ℤ^d} φ((x - x₀ + z)/ℓ)` (`O:eq:meso-test`,
M L7576-7578) as a function on the torus (any representative of `x` gives the same value). -/
def mesoTest (d : ℕ) (ℓ : ℝ) (x₀ : Euc d) (φ : Euc d → ℝ) : Torus d → ℝ :=
  fun x => ℓ ^ (-(d : ℝ) / 2) *
    ∑' z : Lattice d, φ (ℓ⁻¹ • (Torus.rep x - x₀ + Lattice.toEuc z))

/-- The admissible exponent bound of `O:eq:kappa-range` (M L7630-7637): the minimum of the four
displayed quantities, `q = d - s`. -/
def kappaMax (d : ℕ) (s : ℝ) : ℝ :=
  min (min (1 / (d : ℝ))
      ((((d : ℝ) - s) / d - 1 / 2) / ((d : ℝ) / 2 + max ((d : ℝ) - s) 2)))
    (min (1 / ((d : ℝ) * ((d : ℝ) + 3 - min ((d : ℝ) - s) 2)))
      (((d : ℝ) - s) / (2 * d * (((d : ℝ) + ((d : ℝ) - s)) / 2 + 2 - min ((d : ℝ) - s) 2))))

/-- Proposition 6.1 (`M:O:prop:screening`, TeX M L7613-7642), the bound `O:eq:screening-bound`.
Fix `d ≥ 2`, `0 ≤ s < d/2`, `q = d - s`, finitely many real tests `φ_a ∈ C_c^∞(ℝ^d)`, a center `x₀` and a
compact interval `[b₋,b₊] ⊂ (0,∞)`.  There are `C₀ ≥ 0` (so that `F_N^γ(X_N,dx) + o_N ≥ 0` off collisions,
`O:eq:meso-o`) and `C` such that for every `N ≥ 2`, `β_N > 0`, `ℓ > 0` (= `ℓ_N`), `b ∈ [b₋,b₊]` with
`b_N = β_N ℓ^q ∈ [b₋,b₊]`, every particle system (Haar initial positions, `V = 0`, inverse temperature
`β_N`) and every `t_1,…,t_p ≥ 0`:
`sup_{‖F‖_{C_b^3} ≤ 1} |E F((Z_{N,ℓ}^{τ_N t_i}(φ_i))_i) - E F((Z^{t_i}(φ_i))_i)|`
`≤ C[N^{-1/2}ℓ^{-d/2} + √N o_N ℓ^{-d/2-max(q,2)} + N^{-1/d} ℓ^{-d-3+min(q,2)}`
`+ √o_N ℓ^{-(d+q)/2-2+min(q,2)} + ℓ + |b_N - b|]`, `τ_N = ℓ^{2-q}` (`O:eq:meso-scales`).
No upper bound on `ℓ` is imposed (the bound is trivial for `ℓ ≥ 1` once `C ≥ 2`).  Technical
hypotheses: `hsd : s < d` (implied by `s < d/2`, needed for `PDE.mfData`), `1 ≤ N` is subsumed by
`2 ≤ N`; the global strong solution (`∀ T'`) is needed because the times `t_i` are arbitrary.

Statement repair (ISSUES.md, entry "Filtered strong solutions: follow-up repairs"): the proof (TeX L7640-7680) uses the exact empirical identity, Itô's formula for the Gaussian replacement, and entropy contraction for the invariant Gibbs law (B.15), which need a Brownian filtration, so `X` is assumed a filtered strong solution (`∃ ℱ W', IsFilteredSolution P ℱ W' W X`, the strong-solution adaptedness of A.1 that `IsStrongSolution` records only as measurability, ISSUES D1). -/
theorem screening_comparison (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (hsd : s < d) (p : ℕ) (φ : Fin p → Euc d → ℝ)
    (hφ : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (φ a) ∧ HasCompactSupport (φ a)) (x₀ : Euc d)
    (bm bp : ℝ) (hbm : 0 < bm) (hbmp : bm ≤ bp) :
    ∃ C₀ C : ℝ, 0 ≤ C₀ ∧ 0 ≤ C ∧
      (∀ N : ℕ, 2 ≤ N → ∀ X : Config d N, X ∉ collisionSet d N →
        0 ≤ rieszEnergy d s X (volume : Measure (Torus d)) + oN d s C₀ N) ∧
      ∀ (N : ℕ), 2 ≤ N → ∀ (βN : ℝ) (hβN : 0 < βN) (ℓ b : ℝ), 0 < ℓ →
        βN * ℓ ^ ((d : ℝ) - s) ∈ Set.Icc bm bp → b ∈ Set.Icc bm bp →
        ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
          IsVectorBrownian P W →
          ProbabilityTheory.IndepFun X₀ (fun ω => fun t : ℝ≥0 => W t ω) P →
          P.map X₀ = Measure.pi (fun _ : Fin N => (volume : Measure (Torus d))) →
          (∀ T' : ℝ, 0 ≤ T' →
            IsStrongSolution P (PDE.mfData d s hs0 hsd (fun _ => 0) βN hβN) T' X₀ W X) →
          (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
            (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X) →
          ∀ t : Fin p → ℝ, (∀ a, 0 ≤ t a) →
            smoothDist 3
                (law P fun ω => (WithLp.toLp 2 fun a =>
                  linCoord (volume : Measure (Torus d)) (mesoTest d ℓ x₀ (φ a))
                    (X (ℓ ^ (2 - ((d : ℝ) - s)) * t a).toNNReal ω) : EuclideanSpace ℝ (Fin p)))
                (ProbabilityTheory.multivariateGaussian 0 (mesoCovMatrix d s b t φ)) ≤
              C * ((N : ℝ) ^ (-(1 : ℝ) / 2) * ℓ ^ (-(d : ℝ) / 2) +
                Real.sqrt N * oN d s C₀ N * ℓ ^ (-(d : ℝ) / 2 - max ((d : ℝ) - s) 2) +
                (N : ℝ) ^ (-(1 : ℝ) / d) * ℓ ^ (-(d : ℝ) - 3 + min ((d : ℝ) - s) 2) +
                Real.sqrt (oN d s C₀ N) *
                  ℓ ^ (-((d : ℝ) + ((d : ℝ) - s)) / 2 - 2 + min ((d : ℝ) - s) 2) +
                ℓ + |βN * ℓ ^ ((d : ℝ) - s) - b|) := by
  sorry

/-- Proposition 6.1, `O:eq:kappa-range` and the following two sentences (M L7630-7637): the interval
`0 < κ < kappaMax d s` is nonempty for every `0 ≤ s < d/2` (`d ≥ 2`), and it is `κ < 1/6` for
`(d,s) = (2,0)` and `κ < 1/21` for `(d,s) = (3,1)`. -/
theorem kappaMax_pos_and_values :
    (∀ (d : ℕ) (s : ℝ), 2 ≤ d → 0 ≤ s → s < (d : ℝ) / 2 → 0 < kappaMax d s) ∧
      kappaMax 2 0 = 1 / 6 ∧ kappaMax 3 1 = 1 / 21 := by
  refine ⟨fun d s hd hs0 hs => ?_, ?_, ?_⟩
  · have hD : (2 : ℝ) ≤ d := by exact_mod_cast hd
    have hD0 : (0 : ℝ) < d := by linarith
    have hq : (0 : ℝ) < (d : ℝ) - s := by linarith
    have hm2 : min ((d : ℝ) - s) 2 ≤ 2 := min_le_right _ _
    have hmx : (2 : ℝ) ≤ max ((d : ℝ) - s) 2 := le_max_right _ _
    unfold kappaMax
    have hX : (0 : ℝ) < ((d : ℝ) - s) / d - 1 / 2 := by
      have h : (1 / 2 : ℝ) < ((d : ℝ) - s) / d := by
        rw [lt_div_iff₀ hD0]
        linarith
      linarith
    have hY : (0 : ℝ) < (d : ℝ) / 2 + max ((d : ℝ) - s) 2 := by linarith
    have hE : (0 : ℝ) < (d : ℝ) + 3 - min ((d : ℝ) - s) 2 := by linarith
    refine lt_min (lt_min (div_pos one_pos hD0) (div_pos hX hY))
      (lt_min (div_pos one_pos (mul_pos hD0 hE)) (div_pos hq (mul_pos (mul_pos two_pos hD0) ?_)))
    linarith
  · unfold kappaMax
    norm_num [min_def, max_def]
  · unfold kappaMax
    norm_num [min_def, max_def]

/-- Proposition 6.1, "In particular" (M L7628-7630): for `ℓ_N = N^{-κ}` with `0 < κ < kappaMax d s`, all
terms of the right-hand side of `O:eq:screening-bound` other than `|b_N - b|` tend to zero (for every
`C₀ ≥ 0`, with `o_N = oN d s C₀ N`). -/
theorem screening_error_tendsto (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (C₀ : ℝ) (hC₀ : 0 ≤ C₀) (κ : ℝ) (hκ : 0 < κ) (hκm : κ < kappaMax d s) :
    Tendsto (fun N : ℕ =>
      (N : ℝ) ^ (-(1 : ℝ) / 2) * ((N : ℝ) ^ (-κ)) ^ (-(d : ℝ) / 2) +
        Real.sqrt N * oN d s C₀ N * ((N : ℝ) ^ (-κ)) ^ (-(d : ℝ) / 2 - max ((d : ℝ) - s) 2) +
        (N : ℝ) ^ (-(1 : ℝ) / d) * ((N : ℝ) ^ (-κ)) ^ (-(d : ℝ) - 3 + min ((d : ℝ) - s) 2) +
        Real.sqrt (oN d s C₀ N) *
          ((N : ℝ) ^ (-κ)) ^ (-((d : ℝ) + ((d : ℝ) - s)) / 2 - 2 + min ((d : ℝ) - s) 2) +
        (N : ℝ) ^ (-κ)) atTop (𝓝 0) := by
  have hD : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hD0 : (0 : ℝ) < d := by linarith
  have hq : (0 : ℝ) < (d : ℝ) - s := by linarith
  have hm2 : min ((d : ℝ) - s) 2 ≤ 2 := min_le_right _ _
  have hmx : (2 : ℝ) ≤ max ((d : ℝ) - s) 2 := le_max_right _ _
  have hts : (d : ℝ) * (s / d) = s := by field_simp
  have hsD : ((d : ℝ) - s) / d = 1 - s / d := by rw [sub_div, div_self hD0.ne']
  unfold kappaMax at hκm
  have hY : (0 : ℝ) < (d : ℝ) / 2 + max ((d : ℝ) - s) 2 := by linarith
  have hκa := lt_of_lt_of_le hκm (min_le_left _ _)
  have hκ1 := lt_of_lt_of_le hκa (min_le_left _ _)
  have hκ2 := lt_of_lt_of_le hκa (min_le_right _ _)
  have hκ3 := lt_of_lt_of_le hκm (le_trans (min_le_right _ _) (min_le_left _ _))
  have hκ4 := lt_of_lt_of_le hκm (le_trans (min_le_right _ _) (min_le_right _ _))
  have hE : (0 : ℝ) < (d : ℝ) + 3 - min ((d : ℝ) - s) 2 := by linarith
  have hF : (0 : ℝ) < ((d : ℝ) + ((d : ℝ) - s)) / 2 + 2 - min ((d : ℝ) - s) 2 := by linarith
  rw [lt_div_iff₀ hD0] at hκ1
  rw [lt_div_iff₀ hY, hsD] at hκ2
  rw [lt_div_iff₀ (mul_pos hD0 hE)] at hκ3
  rw [lt_div_iff₀ (mul_pos (mul_pos two_pos hD0) hF)] at hκ4
  have hκE : κ * ((d : ℝ) + 3 - min ((d : ℝ) - s) 2) < 1 / d := by
    rw [lt_div_iff₀ hD0]
    linarith
  have key4 : κ * (((d : ℝ) + ((d : ℝ) - s)) / 2 + 2 - min ((d : ℝ) - s) 2) * 2 < 1 - s / d := by
    by_contra hc
    push_neg at hc
    have := mul_le_mul_of_nonneg_left hc hD0.le
    linarith
  have hf1 : -(1 : ℝ) / 2 + (-κ) * (-(d : ℝ) / 2) < 0 := by linarith
  have hf2 : 1 / 2 + ((s : ℝ) / d - 1) + (-κ) * (-(d : ℝ) / 2 - max ((d : ℝ) - s) 2) < 0 := by
    linarith
  have hf3 : -(1 : ℝ) / d + (-κ) * (-(d : ℝ) - 3 + min ((d : ℝ) - s) 2) < 0 := by
    have e : -(1 : ℝ) / d + (-κ) * (-(d : ℝ) - 3 + min ((d : ℝ) - s) 2) =
        -(1 / (d : ℝ)) + κ * ((d : ℝ) + 3 - min ((d : ℝ) - s) 2) := by ring
    rw [e]
    linarith
  have hf4 : (s / d - 1) * (1 / 2) + (-κ) * (-((d : ℝ) + ((d : ℝ) - s)) / 2 - 2 +
      min ((d : ℝ) - s) 2) < 0 := by
    linarith
  have hT1 : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(1 : ℝ) / 2) * ((N : ℝ) ^ (-κ)) ^ (-(d : ℝ) / 2))
      atTop (𝓝 0) := by
    refine (scrn_rpow_nat_tendsto hf1).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hx : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    exact (scrn_pow_mul_pow hx _ _ _).symm
  have hT2 : Tendsto (fun N : ℕ => Real.sqrt N * oN d s C₀ N *
      ((N : ℝ) ^ (-κ)) ^ (-(d : ℝ) / 2 - max ((d : ℝ) - s) 2)) atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ (scrn_logpoly_nat_tendsto C₀ (1 / (2 * (d : ℝ))) hf2)
    · filter_upwards [eventually_ge_atTop 1] with N hN
      exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (scrn_oN_nonneg hC₀ hN)) (by positivity)
    · filter_upwards [eventually_ge_atTop 1] with N hN
      refine (scrn_term2_le hC₀ hN).trans_eq ?_
      ring
  have hT3 : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(1 : ℝ) / d) *
      ((N : ℝ) ^ (-κ)) ^ (-(d : ℝ) - 3 + min ((d : ℝ) - s) 2)) atTop (𝓝 0) := by
    refine (scrn_rpow_nat_tendsto hf3).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hx : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    exact (scrn_pow_mul_pow hx _ _ _).symm
  have hT4 : Tendsto (fun N : ℕ => Real.sqrt (oN d s C₀ N) *
      ((N : ℝ) ^ (-κ)) ^ (-((d : ℝ) + ((d : ℝ) - s)) / 2 - 2 + min ((d : ℝ) - s) 2))
      atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ (scrn_logpoly_nat_tendsto (1 + C₀) (1 / (2 * (d : ℝ))) hf4)
    · filter_upwards [eventually_ge_atTop 1] with N hN
      exact mul_nonneg (Real.sqrt_nonneg _) (by positivity)
    · filter_upwards [eventually_ge_atTop 1] with N hN
      refine (scrn_term4_le hC₀ hN).trans_eq ?_
      ring
  have hT5 : Tendsto (fun N : ℕ => (N : ℝ) ^ (-κ)) atTop (𝓝 0) :=
    scrn_rpow_nat_tendsto (by linarith)
  have hsum := ((((hT1.add hT2).add hT3).add hT4).add hT5)
  rw [show ((0 : ℝ) + 0 + 0 + 0 + 0) = 0 by ring] at hsum
  exact hsum

/-- Proposition 6.1, last paragraph (M L7639-7642): for every `u_N → ∞`, the vector at rescaled times
`u_N + t_i` (fixed nonnegative lags `t_i`) converges to the stationary Gaussian evolution with spectral
density `S_b`, in the smooth distance `d_{C³}` (finitely many tests and times).  Regime: `ℓ_N = N^{-κ}`,
`0 < κ < kappaMax d s` (the regime in which the error terms of `O:eq:screening-bound` vanish),
`b_N = β_N ℓ_N^q → b ∈ (0,∞)`; the systems are indexed by `n ↦ N = n+2`, with the inverse temperature
`β_N = βN n`.  The sentence "no sharp occupancy assertion under only `Nℓ^d → ∞`" is a non-claim.

Statement repair (ISSUES.md, entry "Filtered strong solutions: follow-up repairs"): the stationary limit is the last paragraph of the proof of Proposition 6.1 (TeX L7680-7690), which reuses the uniform particle errors of `screening_comparison` (Itô/duality identity), so each `X n` is assumed a filtered strong solution (`hfilt`, `IsFilteredSolution`). -/
theorem screening_stationary_limit (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (hsd : s < d) (p : ℕ) (φ : Fin p → Euc d → ℝ)
    (hφ : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (φ a) ∧ HasCompactSupport (φ a)) (x₀ : Euc d)
    (κ : ℝ) (hκ : 0 < κ) (hκm : κ < kappaMax d s) (b : ℝ) (hb : 0 < b) (βN : ℕ → ℝ)
    (hβN : ∀ n, 0 < βN n)
    (hbN : Tendsto (fun n : ℕ => βN n * (((n + 2 : ℕ) : ℝ) ^ (-κ)) ^ ((d : ℝ) - s)) atTop (𝓝 b))
    (Ω : ℕ → Type) [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)] (X₀ : ∀ n, Ω n → Config d (n + 2))
    (W : ∀ n, ℝ≥0 → Ω n → (Fin (n + 2) → Euc d)) (X : ∀ n, ℝ≥0 → Ω n → Config d (n + 2))
    (hW : ∀ n, IsVectorBrownian (P n) (W n))
    (hI : ∀ n, ProbabilityTheory.IndepFun (X₀ n) (fun ω => fun t : ℝ≥0 => W n t ω) (P n))
    (hX₀ : ∀ n, (P n).map (X₀ n) = Measure.pi (fun _ : Fin (n + 2) => (volume : Measure (Torus d))))
    (hsol : ∀ n, ∀ T' : ℝ, 0 ≤ T' →
      IsStrongSolution (P n) (PDE.mfData d s hs0 hsd (fun _ => 0) (βN n) (hβN n)) T' (X₀ n) (W n)
        (X n))
    (hfilt : ∀ n, ∃ (ℱ : MeasureTheory.Filtration ℝ (inferInstance : MeasurableSpace (Ω n)))
      (W' : ℝ≥0 → Ω n → (Fin (n + 2) × Fin d) → ℝ), IsFilteredSolution (P n) ℱ W' (W n) (X n))
    (u : ℕ → ℝ) (hu0 : ∀ n, 0 ≤ u n) (hu : Tendsto u atTop atTop) (t : Fin p → ℝ)
    (ht : ∀ a, 0 ≤ t a) :
    Tendsto (fun n : ℕ => smoothDist 3
      (law (P n) fun ω => (WithLp.toLp 2 fun a =>
        linCoord (volume : Measure (Torus d))
          (mesoTest d (((n + 2 : ℕ) : ℝ) ^ (-κ)) x₀ (φ a))
          (X n ((((n + 2 : ℕ) : ℝ) ^ (-κ)) ^ (2 - ((d : ℝ) - s)) * (u n + t a)).toNNReal ω) :
            EuclideanSpace ℝ (Fin p)))
      (ProbabilityTheory.multivariateGaussian 0 (mesoStatCovMatrix d s b t φ))) atTop (𝓝 0) := by
  sorry

/-- Remark "Formation at low frequency" (`M:@remark:L7716`, TeX M L7716-7718): at a fixed positive
rescaled time `t`, the limit as `ξ → 0` of the equal-time spectral density
`S_b(ξ) + (1 - S_b(ξ)) e^{-2t a_b(ξ)}` (`O:eq:meso-limit-cov` at `u = t`) is `1` if `q < 2`, is
`e^{-2 c_{d,s} t}` if `q = 2`, and is `0` if `q > 2`, `q = d - s`, `c_{d,s} = rieszConst d s`; in all
cases the stationary density `S_b(ξ)` tends to `0` as `ξ → 0`.  Standing assumptions of Section 6:
`d ≥ 2`, `0 ≤ s < d/2`, fixed `b > 0`. -/
theorem meso_low_frequency (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (b : ℝ)
    (hb : 0 < b) (t : ℝ) (ht : 0 < t) :
    (((d : ℝ) - s < 2 → Tendsto (fun ξ : Euc d => mesoSpectral d s b ξ +
        (1 - mesoSpectral d s b ξ) * Real.exp (-2 * t * mesoRate d s b ξ)) (𝓝[≠] 0) (𝓝 1)) ∧
      ((d : ℝ) - s = 2 → Tendsto (fun ξ : Euc d => mesoSpectral d s b ξ +
        (1 - mesoSpectral d s b ξ) * Real.exp (-2 * t * mesoRate d s b ξ)) (𝓝[≠] 0)
          (𝓝 (Real.exp (-2 * rieszConst d s * t)))) ∧
      (2 < (d : ℝ) - s → Tendsto (fun ξ : Euc d => mesoSpectral d s b ξ +
        (1 - mesoSpectral d s b ξ) * Real.exp (-2 * t * mesoRate d s b ξ)) (𝓝[≠] 0) (𝓝 0))) ∧
    Tendsto (fun ξ : Euc d => mesoSpectral d s b ξ) (𝓝[≠] 0) (𝓝 0) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : s < d := by linarith
  have hq0 : 0 < (d : ℝ) - s := by linarith
  have hc : 0 < rieszConst d s := rieszConst_pos hd hs0 hsd
  -- the radial variable `u(ξ) = 2π‖ξ‖`
  set u : Euc d → ℝ := fun ξ => 2 * Real.pi * ‖ξ‖ with hu_def
  have hu_cont : Continuous u := continuous_const.mul continuous_norm
  have hu0 : u 0 = 0 := by simp [hu_def]
  have hupos : ∀ ξ : Euc d, ξ ≠ 0 → 0 < u ξ := fun ξ hξ => by
    have : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
    simp only [hu_def]
    positivity
  have hS_eq : ∀ ξ, mesoSpectral d s b ξ =
      (u ξ) ^ ((d : ℝ) - s) / ((u ξ) ^ ((d : ℝ) - s) + b * rieszConst d s) := fun ξ => rfl
  have hA_eq : ∀ ξ, mesoRate d s b ξ = b⁻¹ * (u ξ) ^ 2 + rieszConst d s * (u ξ) ^ (2 - ((d : ℝ) - s)) :=
    fun ξ => rfl
  have hpow_cont : ∀ p : ℝ, 0 ≤ p → ContinuousAt (fun ξ => (u ξ) ^ p) 0 := fun p hp => by
    have h1 : ContinuousAt (fun x : ℝ => x ^ p) (u 0) :=
      Real.continuousAt_rpow_const _ _ (Or.inr hp)
    exact h1.comp (f := u) hu_cont.continuousAt
  -- value of `S` at the origin and its continuity
  have hS_cont : ContinuousAt (fun ξ => mesoSpectral d s b ξ) 0 := by
    have hden : (u 0) ^ ((d : ℝ) - s) + b * rieszConst d s ≠ 0 := by
      rw [hu0, Real.zero_rpow hq0.ne']
      have : 0 < b * rieszConst d s := mul_pos hb hc
      linarith
    have := ((hpow_cont _ hq0.le).div ((hpow_cont _ hq0.le).add continuousAt_const)
      (by simpa using hden) : ContinuousAt (fun ξ => (u ξ) ^ ((d : ℝ) - s) /
        ((u ξ) ^ ((d : ℝ) - s) + b * rieszConst d s)) 0)
    exact this
  have hS_val : mesoSpectral d s b 0 = 0 := by
    rw [hS_eq, hu0, Real.zero_rpow hq0.ne', zero_div]
  have hS0 : Tendsto (fun ξ => mesoSpectral d s b ξ) (𝓝[≠] 0) (𝓝 0) := by
    have h := hS_cont.tendsto.mono_left (nhdsWithin_le_nhds (s := {(0 : Euc d)}ᶜ))
    rw [hS_val] at h
    exact h
  refine ⟨⟨?_, ?_, ?_⟩, hS0⟩
  · -- `d - s < 2`: the limit is `1`
    intro hlt
    have hexp : ContinuousAt (fun ξ => Real.exp (-2 * t * mesoRate d s b ξ)) 0 := by
      have hA : ContinuousAt (fun ξ => mesoRate d s b ξ) 0 := by
        have e : (fun ξ => mesoRate d s b ξ) = fun ξ => b⁻¹ * (u ξ) ^ 2 +
            rieszConst d s * (u ξ) ^ (2 - ((d : ℝ) - s)) := funext hA_eq
        rw [e]
        exact ((continuousAt_const.mul ((hu_cont.pow 2).continuousAt))).add
          (continuousAt_const.mul (hpow_cont _ (by linarith)))
      exact (Real.continuous_exp.continuousAt).comp (continuousAt_const.mul hA)
    have hF : ContinuousAt (fun ξ => mesoSpectral d s b ξ +
        (1 - mesoSpectral d s b ξ) * Real.exp (-2 * t * mesoRate d s b ξ)) 0 :=
      hS_cont.add ((continuousAt_const.sub hS_cont).mul hexp)
    have hval : mesoSpectral d s b 0 + (1 - mesoSpectral d s b 0) *
        Real.exp (-2 * t * mesoRate d s b 0) = 1 := by
      have hA0 : mesoRate d s b 0 = 0 := by
        rw [hA_eq, hu0]
        simp [Real.zero_rpow (show (2 - ((d : ℝ) - s)) ≠ 0 by linarith)]
      rw [hS_val, hA0]
      simp
    have h := hF.tendsto.mono_left (nhdsWithin_le_nhds (s := {(0 : Euc d)}ᶜ))
    rw [hval] at h
    exact h
  · -- `d - s = 2`: the limit is `exp(-2 c t)`
    intro heq
    have hA_const : (fun ξ => mesoRate d s b ξ) = fun ξ => b⁻¹ * (u ξ) ^ 2 + rieszConst d s := by
      funext ξ
      rw [hA_eq, heq, sub_self, Real.rpow_zero, mul_one]
    have hA : ContinuousAt (fun ξ => mesoRate d s b ξ) 0 := by
      rw [hA_const]
      exact (continuousAt_const.mul (hu_cont.pow 2).continuousAt).add continuousAt_const
    have hexp : ContinuousAt (fun ξ => Real.exp (-2 * t * mesoRate d s b ξ)) 0 :=
      (Real.continuous_exp.continuousAt).comp (continuousAt_const.mul hA)
    have hF : ContinuousAt (fun ξ => mesoSpectral d s b ξ +
        (1 - mesoSpectral d s b ξ) * Real.exp (-2 * t * mesoRate d s b ξ)) 0 :=
      hS_cont.add ((continuousAt_const.sub hS_cont).mul hexp)
    have hval : mesoSpectral d s b 0 + (1 - mesoSpectral d s b 0) *
        Real.exp (-2 * t * mesoRate d s b 0) = Real.exp (-2 * rieszConst d s * t) := by
      have hA0 : mesoRate d s b 0 = rieszConst d s := by
        rw [hA_eq, hu0, heq, sub_self, Real.rpow_zero]
        simp
      rw [hS_val, hA0]
      simp only [zero_add, sub_zero, one_mul]
      congr 1
      ring
    have h := hF.tendsto.mono_left (nhdsWithin_le_nhds (s := {(0 : Euc d)}ᶜ))
    rw [hval] at h
    exact h
  · -- `2 < d - s`: the limit is `0`, since the rate blows up at the origin
    intro hgt
    have hu_lim : Tendsto u (𝓝[≠] 0) (𝓝[>] 0) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have := (hu_cont.tendsto (0 : Euc d)).mono_left (nhdsWithin_le_nhds (s := {(0 : Euc d)}ᶜ))
        rw [hu0] at this
        exact this
      · filter_upwards [self_mem_nhdsWithin] with ξ hξ
        exact hupos ξ hξ
    have hpow_lim : Tendsto (fun ξ => (u ξ) ^ (2 - ((d : ℝ) - s))) (𝓝[≠] 0) atTop := by
      have hinv : Tendsto (fun ξ => (u ξ)⁻¹) (𝓝[≠] 0) atTop :=
        tendsto_inv_nhdsGT_zero.comp hu_lim
      have h2 := (tendsto_rpow_atTop (show 0 < ((d : ℝ) - s) - 2 by linarith)).comp hinv
      refine h2.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ξ hξ
      have hp := hupos ξ hξ
      simp only [Function.comp]
      rw [Real.inv_rpow hp.le, ← Real.rpow_neg hp.le]
      congr 1
      ring
    have hA_lim : Tendsto (fun ξ => mesoRate d s b ξ) (𝓝[≠] 0) atTop := by
      have hc' : Tendsto (fun ξ => rieszConst d s * (u ξ) ^ (2 - ((d : ℝ) - s))) (𝓝[≠] 0) atTop :=
        Tendsto.const_mul_atTop hc hpow_lim
      refine tendsto_atTop_mono (fun ξ => ?_) hc'
      rw [hA_eq]
      have : 0 ≤ b⁻¹ * (u ξ) ^ 2 := mul_nonneg (inv_nonneg.mpr hb.le) (sq_nonneg _)
      linarith
    have hE : Tendsto (fun ξ => Real.exp (-2 * t * mesoRate d s b ξ)) (𝓝[≠] 0) (𝓝 0) := by
      have h1 : Tendsto (fun ξ => -2 * t * mesoRate d s b ξ) (𝓝[≠] 0) atBot :=
        Tendsto.const_mul_atTop_of_neg (by linarith) hA_lim
      exact Real.tendsto_exp_atBot.comp h1
    have h1 : Tendsto (fun _ : Euc d => (1 : ℝ)) (𝓝[≠] 0) (𝓝 1) := tendsto_const_nhds
    have hF := hS0.add ((h1.sub hS0).mul hE)
    have h0 : (0 : ℝ) + (1 - 0) * 0 = 0 := by ring
    rw [h0] at hF
    exact hF

end HRS
