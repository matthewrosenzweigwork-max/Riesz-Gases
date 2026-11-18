import HRS.Whole.Static
import HRS.Prob.Gaussian

/-!
# Thermal fields and support-independent correctors (package S-STAT-01, part II): Section S4

Source: HRS whole-space supplement (S), Section S4 (`S:sec:thermal-fields`), standing
hypotheses S lines 2043-2056: `d ≥ 2`, `a, β > 0`, `V(x) = a|x|²/2`, `g(x) = |x|^{-s}`
(`0 < s < d`) or `-log|x|` (`s = 0`), `𝓗_N = ∑ V(x_i) + N⁻¹∑_{i<j} g(x_i-x_j)`,
`P_N = Z_N⁻¹ e^{-β𝓗_N} dX_N` (`W:eq:r2-quadratic-Gibbs`), "the interaction has not been
divided by `s`"; `μ = ρ dx` the thermal equilibrium measure, `m_N = P_N^{(1)}`.

* S4.1 `W:prop:r2-log-thermal` (S lines 2060-2085).
* S4.2 `W:lem:r2-affine-Poisson` (2194-2211), S4.3 `W:cor:r2-higher-Poisson` (2327-2334).
* S4.4 `W:lem:r2-thermal-corrector` (2405-2420), operators S lines 2391-2403.
* S4.5 `W:thm:r2-quadratic-static-field` (2517-2550), `δ_N` `W:eq:r2-static-delta`
  (2496-2502).
* S4.6 `W:cor:r2-quadratic-preparation-static` (2649-2669).
* S4.7 `W:cor:r2-tilt-static` (2705-2745).
* S4.8 `W:lem:r2-derivative-corrector` (2842-2861).
* S4.9 `W:rem:r2-reflection-gap` (2918-2942): the quantitative claim is the one-body Poincaré
  inequality `∫|∇f|² dμ ≥ c Var_μ(f)` for the logarithmic thermal measure and its compact
  relative perturbations (stated below); the semigroup decay
  `‖e^{-tL_μ}f‖ ≤ C Lip(f) e^{-ct}(1+μ(|x|²))^{1/2}` and the spectral-support statement are
  **not** stated (they need the diffusion semigroup `e^{-tL_μ}`, which has no Lean definition;
  reported).

## Representation decisions

* The thermal equilibrium measure is `thermalMeasure d s a β` of `Basic.lean`
  (`IsThermalEquilibrium`, which covers `s = 0` with `rieszKernel d 0 = -log|x|`).
* "Invariant probability measure of the diffusion with generator `Δ + b·∇`" (S4.2) is the
  infinitesimal invariance `∫ (Δφ + b·∇φ) dμ = 0` for `φ ∈ C_c^∞` (`IsInvariantMeasure`);
  for a globally Lipschitz drift this is equivalent to invariance under the (nonexplosive)
  diffusion semigroup.
* `C_b^J` membership is `HRS.MemCb J` (`C^J` with bounded derivatives), so `HRS.cbNorm J` is
  the honest sum of suprema.  `H^J(dx)` tests are smooth functions with square-integrable
  derivatives through order `J` and norm `sobolevWNorm J 2` (smooth representatives).
* `ℓ²`-valued feature vectors live in `SeqL2 = lp (fun _ : ℕ => ℝ) 2`; the Gaussian `Z` is any
  centered Gaussian law on `SeqL2` with the prescribed coordinate covariances
  (`IsCenteredGaussianSeq`), its existence being a separate claim.  The metric
  `d_{C_b²(ℓ²)}` is the project's `HRS.smoothDist 2` (sum norm `‖F‖_∞+‖DF‖_∞+‖D²F‖_∞ ≤ 1`,
  S line 2533).
* Sums of suprema `∑_j ‖D^jχ‖_∞ ≤ C` are written as `∀ x : Fin _ → ℝ^d, ∑_j ‖D^jχ(x_j)‖ ≤ C`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole

variable {d N : ℕ}

/-! ### S4.1 `W:prop:r2-log-thermal` (S lines 2060-2085) -/

section LogThermal

/-- Inverse stereographic projection `u(x) = (2x/(1+|x|²), (|x|²-1)/(1+|x|²)) ∈ S^d ⊂ ℝ^{d+1}`
(S lines 1567-1570). -/
def stereoInv (x : Euc d) : EuclideanSpace ℝ (Fin (d + 1)) :=
  WithLp.toLp 2 (Fin.snoc (α := fun _ => ℝ) (fun i => 2 * x i / (1 + ‖x‖ ^ 2))
    ((‖x‖ ^ 2 - 1) / (1 + ‖x‖ ^ 2)))

/-- The surface measure of the unit sphere `S^d ⊂ ℝ^{d+1}`, pushed to the ambient space
(Mathlib's `volume.toSphere`, a constant multiple of surface measure). -/
def sphereSurface (d : ℕ) : Measure (EuclideanSpace ℝ (Fin (d + 1))) :=
  (volume : Measure (EuclideanSpace ℝ (Fin (d + 1)))).toSphere.map Subtype.val

/-- Proposition S4.1 `W:prop:r2-log-thermal`, existence/uniqueness (S lines 2061-2067): for
`s = 0`, `d ≥ 2`, `a, β > 0`, the logarithmic free energy `W:eq:euc-free-energy` with
`g = -log|x|` has a unique minimiser, which is a bounded thermal density (the `s = 0`
counterpart of `thermalDensity_spec`). -/
theorem logThermalDensity_spec (hd : 2 ≤ d) (a β : ℝ) (ha : 0 < a) (hβ : 0 < β) :
    (∃ ρ : Euc d → ℝ, IsThermalEquilibrium d 0 a β ρ ∧ ∃ C, ∀ x, ρ x ≤ C) ∧
      (∀ ρ ρ' : Euc d → ℝ, IsFreeEnergyMinimizer (rieszKernel d 0) (confinement a) β ρ →
        IsFreeEnergyMinimizer (rieszKernel d 0) (confinement a) β ρ' → ρ =ᵐ[volume] ρ') ∧
      (∀ ρ : Euc d → ℝ, IsFreeEnergyMinimizer (rieszKernel d 0) (confinement a) β ρ →
        ρ =ᵐ[volume] thermalDensity d 0 a β) := by
  sorry

/-- Proposition S4.1, bounds `W:eq:r2-log-thermal-bounds` (S lines 2068-2073):
`c(1+|x|²)^{β/2} e^{-βa|x|²/2} ≤ ρ(x) ≤ C(1+|x|²)^{β/2} e^{-βa|x|²/2}` (the thermal equation
itself is part of `IsThermalEquilibrium`). -/
theorem logThermal_bounds (hd : 2 ≤ d) (a β : ℝ) (ha : 0 < a) (hβ : 0 < β) :
    ∃ c > 0, ∃ C : ℝ, ∀ x,
      c * (1 + ‖x‖ ^ 2) ^ (β / 2) * Real.exp (-β * a * ‖x‖ ^ 2 / 2) ≤ thermalDensity d 0 a β x ∧
      thermalDensity d 0 a β x ≤ C * (1 + ‖x‖ ^ 2) ^ (β / 2) * Real.exp (-β * a * ‖x‖ ^ 2 / 2) := by
  sorry

/-- Proposition S4.1, regularity (S lines 2074-2079): the density is a Schwartz function,
every derivative of `g*ρ` of positive order is bounded, and
`(g*ρ)(x) + ½ log(1+|x|²) ∈ C_b^k(ℝ^d)` for every `k ≥ 0` (`W:eq:r2-log-at-infinity`). -/
theorem logThermal_regularity (hd : 2 ≤ d) (a β : ℝ) (ha : 0 < a) (hβ : 0 < β) :
    (∃ f : SchwartzMap (Euc d) ℝ, ∀ x, f x = thermalDensity d 0 a β x) ∧
    ContDiff ℝ ∞ (convMeasure (rieszKernel d 0) (thermalMeasure d 0 a β)) ∧
    (∀ k : ℕ, 1 ≤ k → ∃ C : ℝ, ∀ x,
      ‖iteratedFDeriv ℝ k (convMeasure (rieszKernel d 0) (thermalMeasure d 0 a β)) x‖ ≤ C) ∧
    ∀ k : ℕ, MemCb k fun x => convMeasure (rieszKernel d 0) (thermalMeasure d 0 a β) x +
      (1 / 2) * Real.log (1 + ‖x‖ ^ 2) := by
  sorry

/-- Proposition S4.1, pushforward (S lines 2080-2082): the image of `μ` under inverse
stereographic projection has a bounded density relative to surface measure on `S^d`
(hence, S lines 1513-1515 and 2120-2122, `μ` satisfies the hypothesis `W:eq:r2-log-density`
of Theorem S3.5). -/
theorem logThermal_stereographic (hd : 2 ≤ d) (a β : ℝ) (ha : 0 < a) (hβ : 0 < β) :
    (∃ C : ℝ≥0, (thermalMeasure d 0 a β).map stereoInv ≤ C • sphereSurface d) ∧
    ∃ A : ℝ, HasSphericalBound A (thermalDensity d 0 a β) := by
  sorry

/-- Proposition S4.1, last sentence (S lines 2083-2084): the law `W:eq:r2-quadratic-Gibbs`
is exactly the modulated Gibbs law with reference `μ`, with the original deleted diagonal. -/
theorem logThermal_canonical (hd : 2 ≤ d) (a β : ℝ) (ha : 0 < a) (hβ : 0 < β) (N : ℕ) :
    canonicalGibbs (rieszKernel d 0) (confinement a) N β =
      modulatedGibbs (rieszKernel d 0) N β (thermalMeasure d 0 a β) := by
  sorry

end LogThermal

/-! ### S4.2 `W:lem:r2-affine-Poisson`, S4.3 `W:cor:r2-higher-Poisson` -/

section Poisson

/-- `μ` is an invariant probability measure of the diffusion with generator `Δ + b·∇`:
`∫ (Δφ + b·∇φ) dμ = 0` for every `φ ∈ C_c^∞` (infinitesimal invariance; S lines 2196-2197). -/
def IsInvariantMeasure (b : Euc d → Euc d) (μ : Measure (Euc d)) : Prop :=
  IsProbabilityMeasure μ ∧ ∀ φ : Euc d → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
    ∫ x, Laplacian.laplacian φ x + inner ℝ (b x) (gradient φ x) ∂μ = 0

/-- The Poisson operator `(-Δ - b·∇)χ`. -/
def poissonOp (b : Euc d → Euc d) (χ : Euc d → ℝ) (x : Euc d) : ℝ :=
  -Laplacian.laplacian χ x - inner ℝ (b x) (gradient χ x)

/-- `B ∈ C_b^m(ℝ^d;ℝ^d)` with all derivatives of order `≤ m` bounded by `Mb`. -/
def HasCbBound (m : ℕ) (Mb : ℝ) (B : Euc d → Euc d) : Prop :=
  ContDiff ℝ m B ∧ ∀ j ≤ m, ∀ x, ‖iteratedFDeriv ℝ j B x‖ ≤ Mb

/-- The conclusions `W:eq:r2-affine-Poisson-bound` (S lines 2199-2207) for a solution `χ`:
centered, `C²`, solving `(-Δ - b·∇)χ = r`, with `|χ(x)| ≤ C‖r‖_{C_b²}(1+log(2+|x|))` and
`‖∇χ‖_∞ + ‖D²χ‖_∞ ≤ C‖r‖_{C_b²}`. -/
def IsPoissonSolution (b : Euc d → Euc d) (μ : Measure (Euc d)) (r : Euc d → ℝ) (C : ℝ)
    (χ : Euc d → ℝ) : Prop :=
  ContDiff ℝ 2 χ ∧ Integrable χ μ ∧ ∫ x, χ x ∂μ = 0 ∧ (∀ x, poissonOp b χ x = r x) ∧
    (∀ x, |χ x| ≤ C * cbNorm 2 r * (1 + Real.log (2 + ‖x‖))) ∧
    ∀ x y, ‖gradient χ x‖ + ‖iteratedFDeriv ℝ 2 χ y‖ ≤ C * cbNorm 2 r

/-- Lemma S4.2 `W:lem:r2-affine-Poisson` (S lines 2194-2211): `q > 0`, `b(x) = -qx + B(x)`
with `B ∈ C_b²`, `μ` an invariant probability measure of `Δ + b·∇` with finite second
moment; for `r ∈ C_b²` with `μ(r) = 0` there is a centered solution of `(-Δ-b·∇)χ = r`
with the bounds `W:eq:r2-affine-Poisson-bound`.  The constant depends on `q`, the bound `Mb`
for `B`, and the second moment bound `m₂` of `μ`, on no support radius and on no lower bound
for the density of `μ` (so `C` is quantified before `B, μ, r`). -/
theorem affine_poisson (hd : 1 ≤ d) (q Mb m₂ : ℝ) (hq : 0 < q) :
    ∃ C : ℝ, ∀ B : Euc d → Euc d, HasCbBound 2 Mb B → ∀ μ : Measure (Euc d),
      IsInvariantMeasure (fun x => -q • x + B x) μ → Integrable (fun x => ‖x‖ ^ 2) μ →
      ∫ x, ‖x‖ ^ 2 ∂μ ≤ m₂ → ∀ r : Euc d → ℝ, MemCb 2 r → Integrable r μ → ∫ x, r x ∂μ = 0 →
        ∃ χ : Euc d → ℝ, IsPoissonSolution (fun x => -q • x + B x) μ r C χ := by
  sorry

/-- Corollary S4.3 `W:cor:r2-higher-Poisson` (S lines 2327-2334): under the assumptions of
S4.2, if moreover `B ∈ C_b^m` and `r ∈ C_b^m` for an integer `m ≥ 2`, the same solution
satisfies `∑_{j=1}^m ‖D^jχ‖_∞ ≤ C_m ‖r‖_{C_b^m}` (`W:eq:r2-higher-Poisson`): there is one
centered solution with both the S4.2 bounds and the higher bounds. -/
theorem affine_poisson_higher (hd : 1 ≤ d) (q Mb m₂ : ℝ) (hq : 0 < q) (m : ℕ) (hm : 2 ≤ m) :
    ∃ C Cm : ℝ, ∀ B : Euc d → Euc d, HasCbBound m Mb B → ∀ μ : Measure (Euc d),
      IsInvariantMeasure (fun x => -q • x + B x) μ → Integrable (fun x => ‖x‖ ^ 2) μ →
      ∫ x, ‖x‖ ^ 2 ∂μ ≤ m₂ → ∀ r : Euc d → ℝ, MemCb m r → Integrable r μ → ∫ x, r x ∂μ = 0 →
        ∃ χ : Euc d → ℝ, IsPoissonSolution (fun x => -q • x + B x) μ r C χ ∧
          ContDiff ℝ m χ ∧
          ∀ x : Fin m → Euc d, ∑ j : Fin m, ‖iteratedFDeriv ℝ ((j : ℕ) + 1) χ (x j)‖ ≤ Cm * cbNorm m r := by
  sorry

/-- Row S4.8b `affine_poisson_deriv` (supplement repair P11; `HRS/MS/PoissonPlan.md` section 5): the
version of S4.3 needed to prove S4.8, where the right-hand side `r = a_φ` is a `C^m` function that is
only Lipschitz-controlled (its sup norm is not controlled by `‖P_μφ‖_{L²(μ)} + ∑_{j≥1}‖D^jφ‖_∞`).
Under the assumptions of S4.2 (`B ∈ C_b^m`, invariant `μ` with second moment `≤ m₂`), for `r ∈ C^m`
with `‖D^j r‖_∞ ≤ D` for `1 ≤ j ≤ m` and `∫ r dμ = 0` (`r` is Lipschitz, hence `μ`-integrable), the
centered Poisson solution `χ` of `𝓛χ = r` has `‖D^jχ‖_∞ ≤ Cm D` for `1 ≤ j ≤ m`: only positive-order
derivatives of `r` enter. -/
theorem affine_poisson_deriv (hd : 1 ≤ d) (q Mb m₂ : ℝ) (hq : 0 < q) (m : ℕ) (hm : 2 ≤ m) :
    ∃ Cm : ℝ, ∀ B : Euc d → Euc d, HasCbBound m Mb B → ∀ μ : Measure (Euc d),
      IsInvariantMeasure (fun x => -q • x + B x) μ → Integrable (fun x => ‖x‖ ^ 2) μ →
      ∫ x, ‖x‖ ^ 2 ∂μ ≤ m₂ → ∀ r : Euc d → ℝ, ContDiff ℝ m r → ∀ D : ℝ,
        (∀ j : ℕ, 1 ≤ j → j ≤ m → ∀ x, ‖iteratedFDeriv ℝ j r x‖ ≤ D) → ∫ x, r x ∂μ = 0 →
        ∃ χ : Euc d → ℝ, ContDiff ℝ m χ ∧ Integrable χ μ ∧ ∫ x, χ x ∂μ = 0 ∧
          (∀ x, poissonOp (fun x => -q • x + B x) χ x = r x) ∧
          ∀ j : ℕ, 1 ≤ j → j ≤ m → ∀ x, ‖iteratedFDeriv ℝ j χ x‖ ≤ Cm * D := by
  sorry

end Poisson

/-! ### S4.4 `W:lem:r2-thermal-corrector` (S lines 2405-2420) -/

section Corrector

variable {s : ℝ}

/-- `L = -Δ + β∇(V + g*μ)·∇` (S line 2397) for the thermal measure `μ = μ_{a,β}`. -/
def thermalGen (d : ℕ) (s a β : ℝ) (χ : Euc d → ℝ) (x : Euc d) : ℝ :=
  -Laplacian.laplacian χ x +
    β * inner ℝ (gradient (fun y => confinement a y + convMeasure (rieszKernel d s)
      (thermalMeasure d s a β) y) x) (gradient χ x)

/-- `A = γ⁻¹ I + K_μ` on `L²_0(μ)` (S line 2396). -/
def susceptibilityOp (g : Euc d → ℝ) (μ : Measure (Euc d)) (γ : ℝ) (f : Euc d → ℝ) :
    Euc d → ℝ :=
  fun x => γ⁻¹ * f x + Kop g μ f x

/-- The corrector conclusions `W:eq:r2-thermal-corrector` (S lines 2408-2415) at level `k`:
`χ ∈ L²(μ)` centered, `C^{k+1}`, `Lχ ∈ L²(μ)`, `ALχ = P_μ φ` (`μ`-a.e.),
`|χ(x)| ≤ C‖φ‖(1 + log(2+|x|))`, `∑_{j=1}^{k+1} ‖D^jχ‖_∞ ≤ C‖φ‖` (for `k = 1`:
`‖∇χ‖_∞ + ‖D²χ‖_∞ ≤ C‖φ‖`). -/
def IsThermalCorrector (d : ℕ) (s a β γ : ℝ) (k : ℕ) (φ : Euc d → ℝ) (normφ C : ℝ)
    (χ : Euc d → ℝ) : Prop :=
  MemL2Zero (thermalMeasure d s a β) χ ∧ ContDiff ℝ (k + 1) χ ∧
    MemLp (thermalGen d s a β χ) 2 (thermalMeasure d s a β) ∧
    (∀ᵐ x ∂(thermalMeasure d s a β),
      susceptibilityOp (rieszKernel d s) (thermalMeasure d s a β) γ (thermalGen d s a β χ) x =
        projMean (thermalMeasure d s a β) φ x) ∧
    (∀ x, |χ x| ≤ C * normφ * (1 + Real.log (2 + ‖x‖))) ∧
    ∀ x : Fin (k + 1) → Euc d, ∑ j : Fin (k + 1), ‖iteratedFDeriv ℝ ((j : ℕ) + 1) χ (x j)‖ ≤ C * normφ

/-- Lemma S4.4 `W:lem:r2-thermal-corrector` (S lines 2405-2420), `C_b^J` version: for
`0 ≤ s < d`, `k ≥ 1` and an integer `J > k + 1 + d/2` (`k = 1` is the first assertion,
`J > d/2 + 2`), for every `φ ∈ C_b^J(ℝ^d)` there is a centered `χ ∈ L²(μ)` with `ALχ = P_μφ`,
`|χ(x)| ≤ C‖φ‖_{C_b^J}(1+log(2+|x|))` and `∑_{j=1}^{k+1}‖D^jχ‖_∞ ≤ C_k‖φ‖_{C_b^J}`.  The
constants are independent of the support of `φ` and uniform for `a, β, γ` in compact subsets
of `(0,∞)` (quantified before them). -/
theorem thermal_corrector (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (k : ℕ) (hk : 1 ≤ k)
    (J : ℕ) (hJ : (k : ℝ) + 1 + (d : ℝ) / 2 < J) (am ap βm βp γm γp : ℝ) (ham : 0 < am)
    (hβm : 0 < βm) (hγm : 0 < γm) :
    ∃ C : ℝ, ∀ a ∈ Set.Icc am ap, ∀ β ∈ Set.Icc βm βp, ∀ γ ∈ Set.Icc γm γp,
      ∀ φ : Euc d → ℝ, MemCb J φ →
        ∃ χ : Euc d → ℝ, IsThermalCorrector d s a β γ k φ (cbNorm J φ) C χ := by
  sorry

/-- `φ ∈ H^J(dx)` (smooth representative): `C^J` with all derivatives through order `J`
square integrable; the norm is `sobolevWNorm J 2`. -/
def MemHSmooth (J : ℕ) (φ : Euc d → ℝ) : Prop :=
  ContDiff ℝ J φ ∧ ∀ j ≤ J, MemLp (fun x => iteratedFDeriv ℝ j φ x) 2 (volume : Measure (Euc d))

/-- Lemma S4.4, last sentence (S lines 2418-2419): the same assertion for `φ ∈ H^J(dx)` with
`‖φ‖_{H^J}` in place of `‖φ‖_{C_b^J}`. -/
theorem thermal_corrector_sobolev (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (k : ℕ) (hk : 1 ≤ k)
    (J : ℕ) (hJ : (k : ℝ) + 1 + (d : ℝ) / 2 < J) (am ap βm βp γm γp : ℝ) (ham : 0 < am)
    (hβm : 0 < βm) (hγm : 0 < γm) :
    ∃ C : ℝ, ∀ a ∈ Set.Icc am ap, ∀ β ∈ Set.Icc βm βp, ∀ γ ∈ Set.Icc γm γp,
      ∀ φ : Euc d → ℝ, MemHSmooth J φ →
        ∃ χ : Euc d → ℝ, IsThermalCorrector d s a β γ k φ (sobolevWNorm J 2 φ) C χ := by
  sorry

end Corrector

/-! ### `ℓ²`-valued feature vectors and Gaussian laws -/

/-- `ℓ² = ℓ²(ℕ)`, the target of the feature coordinates (S line 2524). -/
def SeqL2 : Type := lp (fun _ : ℕ => ℝ) 2

namespace SeqL2

instance : NormedAddCommGroup SeqL2 := inferInstanceAs (NormedAddCommGroup (lp (fun _ : ℕ => ℝ) 2))
instance : InnerProductSpace ℝ SeqL2 := inferInstanceAs (InnerProductSpace ℝ (lp (fun _ : ℕ => ℝ) 2))
instance : CompleteSpace SeqL2 := inferInstanceAs (CompleteSpace (lp (fun _ : ℕ => ℝ) 2))
instance : MeasurableSpace SeqL2 := borel _
instance : BorelSpace SeqL2 := ⟨rfl⟩

/-- The `i`-th coordinate. -/
def coord (z : SeqL2) (i : ℕ) : ℝ := (show lp (fun _ : ℕ => ℝ) 2 from z) i

open Classical in
/-- The element of `ℓ²` with coordinates `c` (`0` if `c ∉ ℓ²`). -/
def ofSeq (c : ℕ → ℝ) : SeqL2 :=
  if h : Memℓp c 2 then (⟨c, h⟩ : lp (fun _ : ℕ => ℝ) 2) else 0

end SeqL2

/-- The centered feature vector `(√N (μ_N - ν)(φ_j))_{j ≥ 1} ∈ ℓ²` of a configuration
(S line 2524 with `ν = m_N`; S line 2732 with `ν = μ₀`). -/
def featureVec (φ : ℕ → Euc d → ℝ) (ν : Measure (Euc d)) (X : EucConfig d N) : SeqL2 :=
  SeqL2.ofSeq fun j => Real.sqrt N * (pair (empirical X) (φ j) - pair ν (φ j))

/-- A centered Gaussian law on `ℓ²` with coordinate covariances `E[Z_i Z_j] = C i j`
(S lines 2525-2531). -/
def IsCenteredGaussianSeq (γ : Measure SeqL2) (C : ℕ → ℕ → ℝ) : Prop :=
  IsCenteredGaussian γ ∧ ∀ i j, Integrable (fun z => SeqL2.coord z i * SeqL2.coord z j) γ ∧
    ∫ z, SeqL2.coord z i * SeqL2.coord z j ∂γ = C i j

/-- A centered Gaussian law on `B_m` whose covariance on the Hermite functions is
`Cov(F(h_α), F(h_β)) = C(h_α, h_β)` (the field version, S lines 2544-2546). -/
def IsCenteredGaussianOsc (m : ℝ) (γ : Measure (OscDual d m))
    (C : (Euc d → ℝ) → (Euc d → ℝ) → ℝ) : Prop :=
  IsCenteredGaussian γ ∧ ∀ α β : MultiIndex d,
    Integrable (fun F => OscDual.hermiteCoeff F α * OscDual.hermiteCoeff F β) γ ∧
    ∫ F, OscDual.hermiteCoeff F α * OscDual.hermiteCoeff F β ∂γ = C (hermiteFunD α) (hermiteFunD β)

/-- The summability hypothesis `W:eq:r2-feature-summability` `S = ∑_j ‖φ_j‖_{C_b^J} < ∞`
(S lines 2519-2523): each `φ_j ∈ C_b^J` and the norms are summable. -/
def IsSummableFeatureFamily (J : ℕ) (φ : ℕ → Euc d → ℝ) : Prop :=
  (∀ j, MemCb J (φ j)) ∧ Summable fun j => cbNorm J (φ j)

/-- `S = ∑_j ‖φ_j‖_{C_b^J}`. -/
def featureSum (J : ℕ) (φ : ℕ → Euc d → ℝ) : ℝ := ∑' j, cbNorm J (φ j)

/-- The conclusions of Theorem S4.5 for a law `P` on configurations, a centering `ν`, a
Gaussian `γ` and the constant `C` (S lines 2524-2543): the feature vector is an `ℓ²`-valued
random variable; `d_{C_b²(ℓ²)}(X_N, Z) ≤ C(S+S²)√δ_N` (`W:eq:r2-static-feature-rate`); and
for every `F ∈ C²(ℓ²)` with bounded first and second derivatives,
`|E F(X_N) - E F(Z)| ≤ C√δ_N (S‖DF‖_∞ + S²‖D²F‖_∞)` (`W:eq:r2-static-derivative-only`). -/
def StaticFieldConclusion (d : ℕ) (s : ℝ) (N : ℕ) (P : Measure (EucConfig d N))
    (ν : Measure (Euc d)) (J : ℕ) (φ : ℕ → Euc d → ℝ) (γ : Measure SeqL2) (C : ℝ) : Prop :=
  (∀ X : EucConfig d N,
    Memℓp (fun j => Real.sqrt N * (pair (empirical X) (φ j) - pair ν (φ j))) 2) ∧
  Measurable (featureVec φ ν : EucConfig d N → SeqL2) ∧
  smoothDist 2 (law P (featureVec φ ν)) γ ≤
    C * (featureSum J φ + featureSum J φ ^ 2) * Real.sqrt (deltaN d s N) ∧
  ∀ F : SeqL2 → ℝ, ContDiff ℝ 2 F → ∀ D₁ D₂ : ℝ, (∀ z, ‖fderiv ℝ F z‖ ≤ D₁) →
    (∀ z, ‖iteratedFDeriv ℝ 2 F z‖ ≤ D₂) →
    Integrable (fun X => F (featureVec φ ν X)) P ∧ Integrable F γ ∧
    |∫ X, F (featureVec φ ν X) ∂P - ∫ z, F z ∂γ| ≤
      C * Real.sqrt (deltaN d s N) * (featureSum J φ * D₁ + featureSum J φ ^ 2 * D₂)

/-! ### S4.5 `W:thm:r2-quadratic-static-field` (S lines 2517-2550) -/

section StaticField

variable {s : ℝ}

/-- Existence of the centered Gaussian `Z` of S4.5 (S lines 2525-2531): for a summable
feature family and a bounded reference density the susceptibility covariances are those of a
centered Gaussian law on `ℓ²`.  At `s = 0` the second logarithmic moment `HasLogMoment2` is assumed
(supplement repair P1: the first log moment does not make `K_μ` an operator on `L²_0(μ)`). -/
theorem exists_gaussian_feature (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (J : ℕ)
    (hJ : (d : ℝ) / 2 + 2 < J) (ρ : Euc d → ℝ) (hρ : IsProbDensity ρ) (M : ℝ)
    (hM : ∀ x, ρ x ≤ M) (γ₀ : ℝ) (hγ₀ : 0 < γ₀) (φ : ℕ → Euc d → ℝ)
    (hφ : IsSummableFeatureFamily J φ) (L : ℝ) (hL : s = 0 → HasLogMoment2 (withDensityReal ρ) L) :
    (∀ ψ, MemCb J ψ → ∃ h, IsResponse (rieszKernel d s) (withDensityReal ρ) γ₀ ψ h) ∧
    ∃ γ : Measure SeqL2, IsCenteredGaussianSeq γ
      fun i j => susceptibilityCov (rieszKernel d s) (withDensityReal ρ) γ₀ (φ i) (φ j) := by
  sorry

/-- Theorem S4.5 `W:thm:r2-quadratic-static-field` (S lines 2517-2546), feature form: for fixed
`a, β > 0`, `0 ≤ s < d`, `P_N` the canonical Gibbs law `W:eq:r2-quadratic-Gibbs`, an integer
`J > d/2 + 2` and `(φ_j) ⊂ C_b^J` with `S = ∑_j ‖φ_j‖_{C_b^J} < ∞`:
`X_N = (√N(μ_N - m_N)(φ_j))_j` is an `ℓ²`-valued random variable and, for `Z` the centered
Gaussian with covariance `⟨P_μφ_i, (I+βK_μ)⁻¹P_μφ_j⟩_{L²(μ)}`,
`d_{C_b²(ℓ²)}(X_N, Z) ≤ C(S+S²)√δ_N` and `|EF(X_N) - EF(Z)| ≤ C√δ_N(S‖DF‖_∞ + S²‖D²F‖_∞)`
for `F ∈ C²(ℓ²)` with bounded first and second derivatives.  The constant depends on
`d, s, a, β, J` only (quantified before the family and `N`).  "Nondecaying tests and initial
semigroup-orbit coordinates" (S lines 2547-2549) are included: no decay of `φ_j` is assumed. -/
theorem quadratic_static_field (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (a β : ℝ) (ha : 0 < a)
    (hβ : 0 < β) (J : ℕ) (hJ : (d : ℝ) / 2 + 2 < J) :
    ∃ C : ℝ, ∀ φ : ℕ → Euc d → ℝ, IsSummableFeatureFamily J φ → ∀ N, 2 ≤ N →
      ∀ γ : Measure SeqL2, IsCenteredGaussianSeq γ
        (fun i j => susceptibilityCov (rieszKernel d s) (thermalMeasure d s a β) β (φ i) (φ j)) →
      StaticFieldConclusion d s N (canonicalGibbs (rieszKernel d s) (confinement a) N β)
        (firstMarginal (canonicalGibbs (rieszKernel d s) (confinement a) N β)) J φ γ C := by
  sorry

/-- Theorem S4.5, oscillator-field clause (S lines 2544-2546): with the Hermite test basis of
`W:eq:euc-oscillator-space` and `m > J + 2d`, the exactly centered field
`ζ_N = √N(μ_N - m_N)` satisfies the Gaussian field theorem in `B_m`:
`d_{C_b²(B_m)}(ζ_N, Z) ≤ C√δ_N` for `Z` the centered Gaussian on `B_m` with the
susceptibility covariance on Hermite functions, throughout `0 ≤ s < d`. -/
theorem quadratic_static_field_osc (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (a β : ℝ)
    (ha : 0 < a) (hβ : 0 < β) (J : ℕ) (hJ : (d : ℝ) / 2 + 2 < J) (m : ℝ)
    (hm : (J : ℝ) + 2 * d < m) :
    ∃ C : ℝ, ∀ N, 2 ≤ N → ∀ γ : Measure (OscDual d m),
      IsCenteredGaussianOsc m γ (susceptibilityCov (rieszKernel d s) (thermalMeasure d s a β) β) →
      Measurable (zetaB m (canonicalGibbs (rieszKernel d s) (confinement a) N β) :
        EucConfig d N → OscDual d m) ∧
      smoothDist 2 (law (canonicalGibbs (rieszKernel d s) (confinement a) N β)
        (zetaB m (canonicalGibbs (rieszKernel d s) (confinement a) N β))) γ ≤
        C * Real.sqrt (deltaN d s N) := by
  sorry

/-- Corollary S4.6 `W:cor:r2-quadratic-preparation-static` (S lines 2649-2669): with the
quadratic thermal reference `μ = μ_{a,β}` and any other fixed `γ₀ > 0`, all conclusions of
S4.5 hold for `Q_{N,γ₀} = 𝒦⁻¹ e^{-γ₀ N F_N^g(·,μ)} μ^{⊗N}`, `m_{N,γ₀} = Q_{N,γ₀}^{(1)}`, with
covariance `⟨P_μφ_i, (I+γ₀K_μ)⁻¹P_μφ_j⟩_{L²(μ)}` and the same `√δ_N` rate, with constants
uniform for `a, β, γ₀` in compact subsets of `(0,∞)`. -/
theorem quadratic_preparation_static (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (J : ℕ)
    (hJ : (d : ℝ) / 2 + 2 < J) (am ap βm βp γm γp : ℝ) (ham : 0 < am) (hβm : 0 < βm)
    (hγm : 0 < γm) :
    ∃ C : ℝ, ∀ a ∈ Set.Icc am ap, ∀ β ∈ Set.Icc βm βp, ∀ γ₀ ∈ Set.Icc γm γp,
      ∀ φ : ℕ → Euc d → ℝ, IsSummableFeatureFamily J φ → ∀ N, 2 ≤ N →
      ∀ γ : Measure SeqL2, IsCenteredGaussianSeq γ
        (fun i j => susceptibilityCov (rieszKernel d s) (thermalMeasure d s a β) γ₀ (φ i) (φ j)) →
      StaticFieldConclusion d s N (modulatedGibbs (rieszKernel d s) N γ₀ (thermalMeasure d s a β))
        (firstMarginal (modulatedGibbs (rieszKernel d s) N γ₀ (thermalMeasure d s a β))) J φ γ C := by
  sorry

/-- Corollary S4.6, oscillator-field clause ("all conclusions", S line 2658, with the indices
of S4.5). -/
theorem quadratic_preparation_static_osc (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (J : ℕ)
    (hJ : (d : ℝ) / 2 + 2 < J) (m : ℝ) (hm : (J : ℝ) + 2 * d < m) (am ap βm βp γm γp : ℝ)
    (ham : 0 < am) (hβm : 0 < βm) (hγm : 0 < γm) :
    ∃ C : ℝ, ∀ a ∈ Set.Icc am ap, ∀ β ∈ Set.Icc βm βp, ∀ γ₀ ∈ Set.Icc γm γp, ∀ N, 2 ≤ N →
      ∀ γ : Measure (OscDual d m),
      IsCenteredGaussianOsc m γ (susceptibilityCov (rieszKernel d s) (thermalMeasure d s a β) γ₀) →
      Measurable (zetaB m (modulatedGibbs (rieszKernel d s) N γ₀ (thermalMeasure d s a β)) :
        EucConfig d N → OscDual d m) ∧
      smoothDist 2 (law (modulatedGibbs (rieszKernel d s) N γ₀ (thermalMeasure d s a β))
        (zetaB m (modulatedGibbs (rieszKernel d s) N γ₀ (thermalMeasure d s a β)))) γ ≤
        C * Real.sqrt (deltaN d s N) := by
  sorry

end StaticField

/-! ### S4.7 `W:cor:r2-tilt-static` (S lines 2705-2745) -/

section Tilt

variable {s : ℝ}

/-- The tilted reference `μ₀ = (1 + εψ) μ_*` (S line 2711). -/
def tiltedMeasure (d : ℕ) (s a β ε : ℝ) (ψ : Euc d → ℝ) : Measure (Euc d) :=
  withDensityReal (perturbedDensity (thermalDensity d s a β) ε ψ)

/-- The perturbation data of S4.7: `ψ ∈ C_c^∞` real with `μ_*(ψ) = 0`, and
`|ε| ‖ψ‖_∞ ≤ 1/2` (S lines 2708-2709). -/
structure IsTiltData (d : ℕ) (s a β : ℝ) (ψ : Euc d → ℝ) (ε : ℝ) : Prop where
  smooth : ContDiff ℝ ∞ ψ
  compactSupport : HasCompactSupport ψ
  meanZero : ∫ x, ψ x * thermalDensity d s a β x = 0
  small : ∀ x, |ε| * |ψ x| ≤ 1 / 2

/-- Corollary S4.7 `W:cor:r2-tilt-static`, exactly centered part (S lines 2705-2729): for the
preparation `Q⁰_{N,γ₀} = 𝒦⁻¹ e^{-γ₀ N F_N^g(·,μ₀)} μ₀^{⊗N}` about `μ₀ = (1+εψ)μ_*`, all
conclusions of S4.5 hold for the exactly centered coordinates `√N(μ_N - m⁰_{N,γ₀})(φ_j)` with
covariance `C⁰_{ij} = ⟨P_{μ₀}φ_i, (I+γ₀K_{μ₀})⁻¹P_{μ₀}φ_j⟩_{L²(μ₀)}`
(`W:eq:r2-tilt-static-covariance`).  Constants are uniform for `a, β, γ₀` in compact positive intervals.
Repair ED15 (approved): the constant is uniform over the whole class of tilts with `‖εψ‖_{C_b^{100d+1001}} ≤ ε_*`
(the TeX proof uses only finitely many `C_b` seminorms of `εψ`, with `|εψ| ≤ 1/2`): `C` is chosen after `ε_*` and BEFORE `(ε, ψ)`, as S2.1(ii) needs. -/
theorem tilt_static (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (J : ℕ)
    (hJ : (d : ℝ) / 2 + 2 < J) (am ap βm βp γm γp : ℝ) (ham : 0 < am) (hβm : 0 < βm)
    (hγm : 0 < γm) (εstar : ℝ) :
    ∃ C : ℝ, ∀ a ∈ Set.Icc am ap, ∀ β ∈ Set.Icc βm βp, ∀ γ₀ ∈ Set.Icc γm γp, ∀ ε : ℝ,
      ∀ ψ : Euc d → ℝ, IsTiltData d s a β ψ ε →
      cbNorm (100 * d + 1001) (fun x => ε * ψ x) ≤ εstar →
      ∀ φ : ℕ → Euc d → ℝ, IsSummableFeatureFamily J φ → ∀ N, 2 ≤ N →
      ∀ γ : Measure SeqL2, IsCenteredGaussianSeq γ
        (fun i j => susceptibilityCov (rieszKernel d s) (tiltedMeasure d s a β ε ψ) γ₀ (φ i) (φ j)) →
      StaticFieldConclusion d s N (modulatedGibbs (rieszKernel d s) N γ₀ (tiltedMeasure d s a β ε ψ))
        (firstMarginal (modulatedGibbs (rieszKernel d s) N γ₀ (tiltedMeasure d s a β ε ψ)))
        J φ γ C := by
  sorry

/-- Corollary S4.7, oscillator-field clause (S lines 2728-2729): the same indices `J > d/2+2`
and `m > J + 2d` as before. -/
theorem tilt_static_osc (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (J : ℕ)
    (hJ : (d : ℝ) / 2 + 2 < J) (m : ℝ) (hm : (J : ℝ) + 2 * d < m) (am ap βm βp γm γp : ℝ)
    (ham : 0 < am) (hβm : 0 < βm) (hγm : 0 < γm) (ψ : Euc d → ℝ) :
    ∃ C : ℝ, ∀ a ∈ Set.Icc am ap, ∀ β ∈ Set.Icc βm βp, ∀ γ₀ ∈ Set.Icc γm γp, ∀ ε : ℝ,
      IsTiltData d s a β ψ ε → ∀ N, 2 ≤ N → ∀ γ : Measure (OscDual d m),
      IsCenteredGaussianOsc m γ
        (susceptibilityCov (rieszKernel d s) (tiltedMeasure d s a β ε ψ) γ₀) →
      Measurable (zetaB m (modulatedGibbs (rieszKernel d s) N γ₀ (tiltedMeasure d s a β ε ψ)) :
        EucConfig d N → OscDual d m) ∧
      smoothDist 2 (law (modulatedGibbs (rieszKernel d s) N γ₀ (tiltedMeasure d s a β ε ψ))
        (zetaB m (modulatedGibbs (rieszKernel d s) N γ₀ (tiltedMeasure d s a β ε ψ)))) γ ≤
        C * Real.sqrt (deltaN d s N) := by
  sorry

/-- Corollary S4.7, mean-field-centered part `W:eq:r2-tilt-initial-bias` (S lines 2731-2741):
for `Y_N = (√N(μ_N - μ₀)(φ_j))_j` and `F ∈ C²(ℓ²)` with bounded first and second derivatives,
`|EF(Y_N) - EF(Z⁰)| ≤ C[S‖DF‖_∞(√Nδ_N + √δ_N) + S²‖D²F‖_∞√δ_N]`.  (That this is a leading
Gaussian comparison for `0 ≤ s < 2d/3` is `sqrt_mul_deltaN_tendsto_zero_iff`.)
Repair ED15 (approved): `C` is uniform over the class `‖εψ‖_{C_b^{100d+1001}} ≤ ε_*` (chosen after `ε_*`, before `(ε, ψ)`), as in `tilt_static`. -/
theorem tilt_static_mean_field (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (J : ℕ)
    (hJ : (d : ℝ) / 2 + 2 < J) (am ap βm βp γm γp : ℝ) (ham : 0 < am) (hβm : 0 < βm)
    (hγm : 0 < γm) (εstar : ℝ) :
    ∃ C : ℝ, ∀ a ∈ Set.Icc am ap, ∀ β ∈ Set.Icc βm βp, ∀ γ₀ ∈ Set.Icc γm γp, ∀ ε : ℝ,
      ∀ ψ : Euc d → ℝ, IsTiltData d s a β ψ ε →
      cbNorm (100 * d + 1001) (fun x => ε * ψ x) ≤ εstar →
      ∀ φ : ℕ → Euc d → ℝ, IsSummableFeatureFamily J φ → ∀ N, 2 ≤ N →
      ∀ γ : Measure SeqL2, IsCenteredGaussianSeq γ
        (fun i j => susceptibilityCov (rieszKernel d s) (tiltedMeasure d s a β ε ψ) γ₀ (φ i) (φ j)) →
      ∀ F : SeqL2 → ℝ, ContDiff ℝ 2 F → ∀ D₁ D₂ : ℝ, (∀ z, ‖fderiv ℝ F z‖ ≤ D₁) →
        (∀ z, ‖iteratedFDeriv ℝ 2 F z‖ ≤ D₂) →
        Integrable (fun X => F (featureVec φ (tiltedMeasure d s a β ε ψ) X))
          (modulatedGibbs (rieszKernel d s) N γ₀ (tiltedMeasure d s a β ε ψ)) ∧ Integrable F γ ∧
        |∫ X, F (featureVec φ (tiltedMeasure d s a β ε ψ) X)
            ∂(modulatedGibbs (rieszKernel d s) N γ₀ (tiltedMeasure d s a β ε ψ)) - ∫ z, F z ∂γ| ≤
          C * (featureSum J φ * D₁ * (Real.sqrt N * deltaN d s N + Real.sqrt (deltaN d s N)) +
            featureSum J φ ^ 2 * D₂ * Real.sqrt (deltaN d s N)) := by
  sorry

end Tilt

/-! ### S4.8 `W:lem:r2-derivative-corrector` (S lines 2842-2861) -/

section DerivativeCorrector

variable {s : ℝ}

/-- The references of S4.8 (S lines 2843-2844): the quadratic thermal equilibrium density, or
one of the compact relative perturbations `(1+εψ)ρ_*` of S4.7 (for a fixed `ψ`). -/
inductive IsStaticReference (d : ℕ) (s a β : ℝ) (ψ : Euc d → ℝ) : (Euc d → ℝ) → Prop
  | thermal : IsStaticReference d s a β ψ (thermalDensity d s a β)
  | perturbed (ε : ℝ) (hε : IsTiltData d s a β ψ ε) :
      IsStaticReference d s a β ψ (perturbedDensity (thermalDensity d s a β) ε ψ)

/-- `L_μ = -Δ - ∇log ρ · ∇` (S line 2850). -/
def weightedGen (ρ : Euc d → ℝ) (χ : Euc d → ℝ) (x : Euc d) : ℝ :=
  -Laplacian.laplacian χ x - inner ℝ (gradient (fun y => Real.log (ρ y)) x) (gradient χ x)

/-- Lemma S4.8 `W:lem:r2-derivative-corrector` (S lines 2842-2861): for `μ = ρ dx` a
quadratic thermal equilibrium measure or one of its compact relative perturbations, `γ₀ > 0`
and an integer `k ≥ 0`, there is an integer `J > k + 1 + d/2` such that for every
`φ ∈ C_b^J`, with `a_φ = (I+γ₀K_μ)⁻¹P_μφ` and `v_φ = ∇L_μ⁻¹a_φ` (`L_μ⁻¹a_φ` a centered
solution of `L_μχ = a_φ`):
`‖v_φ‖_{C_b^k} ≤ C(‖P_μφ‖_{L²(μ)} + ∑_{j=1}^J ‖D^jφ‖_∞)` (`W:eq:r2-derivative-corrector`),
and the same bound holds for every positive-order derivative of `a_φ` through order `k+1`
(a `C^{k+1}` version of `a_φ`).  Constants have the uniformity of the preceding static
theorems (`a, β, γ₀` in compact positive intervals, `ε` in its interval, `ψ` fixed). -/
theorem derivative_corrector (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (k : ℕ)
    (am ap βm βp γm γp : ℝ) (ham : 0 < am) (hβm : 0 < βm) (hγm : 0 < γm) (ψ : Euc d → ℝ) :
    ∃ J : ℕ, (k : ℝ) + 1 + (d : ℝ) / 2 < J ∧ ∃ C : ℝ,
      ∀ a ∈ Set.Icc am ap, ∀ β ∈ Set.Icc βm βp, ∀ γ₀ ∈ Set.Icc γm γp,
      ∀ ρ : Euc d → ℝ, IsStaticReference d s a β ψ ρ → ∀ φ : Euc d → ℝ, MemCb J φ →
        (∃ aφ : Euc d → ℝ,
          IsResponse (rieszKernel d s) (withDensityReal ρ) γ₀ φ aφ ∧
          ContDiff ℝ (k + 1) aφ ∧
          (∀ x : Fin (k + 1) → Euc d, ∑ j : Fin (k + 1), ‖iteratedFDeriv ℝ ((j : ℕ) + 1) aφ (x j)‖ ≤
            C * (l2Norm (withDensityReal ρ) (projMean (withDensityReal ρ) φ) +
              ∑ j ∈ Finset.range J, ⨆ y, ‖iteratedFDeriv ℝ (j + 1) φ y‖)) ∧
          ∃ χ : Euc d → ℝ, ContDiff ℝ (k + 2) χ ∧ MemL2Zero (withDensityReal ρ) χ ∧
            (∀ x, weightedGen ρ χ x = aφ x) ∧
            ∀ x : Fin (k + 1) → Euc d, ∑ j : Fin (k + 1), ‖iteratedFDeriv ℝ (j : ℕ) (gradient χ) (x j)‖ ≤
              C * (l2Norm (withDensityReal ρ) (projMean (withDensityReal ρ) φ) +
                ∑ j ∈ Finset.range J, ⨆ y, ‖iteratedFDeriv ℝ (j + 1) φ y‖)) := by
  sorry

end DerivativeCorrector

/-! ### S4.9 `W:rem:r2-reflection-gap` (S lines 2918-2942): the quantitative claim -/

/-- Remark S4.9 `W:rem:r2-reflection-gap` (S lines 2918-2942), the one-body Poincaré inequality
`∫|∇f|² dμ ≥ c Var_μ(f)` on the closed form domain, for the logarithmic thermal measure
(`s = 0`) and its compact relative perturbations; stated for `C¹` functions with bounded
gradient in `L²(μ)`.  (The semigroup decay bound and the spectral-support statement of the
remark are not stated: no Lean definition of `e^{-tL_μ}` exists.) -/
theorem reflection_gap_poincare (hd : 2 ≤ d) (a β : ℝ) (ha : 0 < a) (hβ : 0 < β)
    (ψ : Euc d → ℝ) (ρ : Euc d → ℝ) (hρ : IsStaticReference d 0 a β ψ ρ) :
    ∃ c > 0, ∀ f : Euc d → ℝ, ContDiff ℝ 1 f → (∃ Cf, ∀ x, ‖gradient f x‖ ≤ Cf) →
      MemLp f 2 (withDensityReal ρ) →
      c * ProbabilityTheory.variance f (withDensityReal ρ) ≤
        ∫ x, ‖gradient f x‖ ^ 2 ∂(withDensityReal ρ) := by
  sorry

end HRS.Whole
