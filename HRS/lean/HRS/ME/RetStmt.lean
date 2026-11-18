import HRS.Sections.Sec5
import HRS.Main.Equilibrium29Spec
import HRS.Stochastic.LyonsZhengSpec

/-!
# Row 5.10: the statements of the two stationary retained-initial-field estimates

`retVec` and the two statements `RetStationaryInitial`, `RetStationaryShift` (stated as propositions, so that files that use them
need not import any theorem carrying `sorry`; `HRS/ME/RetSpec.lean` states them as theorems for the proof packets).  Each is the
proposition `∀ (binders), conclusion` of the corresponding `theorem` in the packet text below, with `d` fixed.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.ME.Ret

open HRS HRS.LZ

/-- The vector `(linCoord m_N (φ_a) (Y_a))_a ∈ ℝ^p` of `ui_comparison`, centred at the first marginal `m_N` of the canonical
Gibbs law; `Y a` is the configuration at which the `a`-th coordinate is read. -/
def retVec (d : ℕ) (s β : ℝ) (V : Torus d → ℝ) (N : ℕ) {p : ℕ} (φ : Fin p → Torus d → ℝ)
    (Y : Fin p → Config d N) : EuclideanSpace ℝ (Fin p) :=
  WithLp.toLp 2 fun a =>
    linCoord (firstMarginal (canonicalGibbs (periodicRiesz d s) V N β)) (φ a) (Y a)

/-- (S2a.)  Stationary, `X₀`-retaining comparison on `[0,T]`, weighted by a bounded measurable probability density `h(X₀)`
(`∫ h(X₀) dP = 1`, so `P.withDensity (h ∘ X₀)` is a probability measure).  The target is `law(U ζ⁰) ∗ N(0, Σ)` under the same weight, i.e. the
transported initial vector plus an independent Gaussian vector with the noise covariance `noiseCovMatrix` (frozen coefficient
`ρβ`, `q = β⁻¹`, as in `ui_comparison` (1)).  The constants are chosen before `N`, the spaces, the flow and `h`; the right side is
`C ‖h‖_{L²(ℙ_{N,β})} √δ_N`.  For `h ≡ 1` this is the `X₀`-joint form of Theorem 2.9 (no initial CLT is used because `X₀` is
kept). -/
def RetStationaryInitial (d : ℕ) : Prop :=
  ∀ (hd : 2 ≤ d) {s β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρS : Torus.IsSmooth ρβ)
    (hρpos : ∀ x, 0 < ρβ x) (T : ℝ) (hT : 0 < T) (p : ℕ) (φ : Fin p → Torus d → ℝ)
    (hφ : ∀ a, Torus.IsSmooth (φ a)),
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ), 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        IsStationaryGibbsFlow P s hs0 hsd V β hβ T X₀ W X →
        ∀ h : Config d N → ℝ≥0∞, Measurable h → (∃ M : ℝ≥0, ∀ x, h x ≤ M) →
        ∫⁻ ω, h (X₀ ω) ∂P = 1 →
        ∀ t : Fin p → ℝ, (∀ a, t a ∈ Set.Icc (0 : ℝ) T) →
          ENNReal.ofReal (smoothDist 2
              ((P.withDensity fun ω => h (X₀ ω)).map fun ω =>
                retVec d s β V N φ fun a => X (t a).toNNReal ω)
              (((P.withDensity fun ω => h (X₀ ω)).map fun ω =>
                  retVec d s β V N
                    (fun a => propagator (PDE.mfData d s hs0 hsd V β hβ) (fun _ => ρβ) 0 (t a) (φ a))
                    fun _ => X₀ ω) ∗
                ProbabilityTheory.multivariateGaussian 0
                  (noiseCovMatrix (PDE.mfData d s hs0 hsd V β hβ) (fun _ => ρβ) β⁻¹ t φ))) ≤
            ENNReal.ofReal C * (∫⁻ ω, h (X₀ ω) ^ 2 ∂P) ^ (1 / 2 : ℝ) *
              ENNReal.ofReal (Real.sqrt (deltaN d s N))

/-- (S2b.)  Stationary, shifted window: at times `u + t_a` the weighted vector is within `C ‖h‖_{L²} (√δ_N + e^{-cu})`
of the stationary Gaussian vector `PDE.stationaryLagCov` (Prop 3.28 with the independent copy
`X₀' ∼ Z⁰` of the initial datum; the factor `e^{-cu}` is the initial term). -/
def RetStationaryShift (d : ℕ) : Prop :=
  ∀ (hd : 2 ≤ d) {s β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρS : Torus.IsSmooth ρβ)
    (hρpos : ∀ x, 0 < ρβ x) (T : ℝ) (hT : 0 < T) (p : ℕ) (φ : Fin p → Torus d → ℝ)
    (hφ : ∀ a, Torus.IsSmooth (φ a)),
    ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧ ∀ (N : ℕ), 2 ≤ N → ∀ u : ℝ, 0 ≤ u →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        IsStationaryGibbsFlow P s hs0 hsd V β hβ (u + T) X₀ W X →
        ∀ h : Config d N → ℝ≥0∞, Measurable h → (∃ M : ℝ≥0, ∀ x, h x ≤ M) →
        ∫⁻ ω, h (X₀ ω) ∂P = 1 →
        ∀ t : Fin p → ℝ, (∀ a, t a ∈ Set.Icc (0 : ℝ) T) →
          ENNReal.ofReal (smoothDist 2
              ((P.withDensity fun ω => h (X₀ ω)).map fun ω =>
                retVec d s β V N φ fun a => X (u + t a).toNNReal ω)
              (ProbabilityTheory.multivariateGaussian 0
                (PDE.stationaryLagCov d s β (PDE.mfData d s hs0 hsd V β hβ) ρβ t φ))) ≤
            ENNReal.ofReal C * (∫⁻ ω, h (X₀ ω) ^ 2 ∂P) ^ (1 / 2 : ℝ) *
              ENNReal.ofReal (Real.sqrt (deltaN d s N) + Real.exp (-c * u))

end HRS.ME.Ret

end
