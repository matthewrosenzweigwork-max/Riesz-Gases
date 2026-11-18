import HRS.ME.RetStmt
import HRS.Main.Headline
import HRS.Uniform.Spec

/-!
# Row 5.10: the path-space weighted estimates (statements only)

Both statements are for a fixed `β > 0` and compare the `h`-weighted law of the window `ζ_N^{a+·}` of a stationary Gibbs flow
(`P.withDensity (h ∘ X₀)`, `h` bounded measurable with `∫ h(X₀) dP = 1`, so the weighted measure is a probability measure) in
`C([0,T]; E_m)` with a Gaussian process law, at the cost `C ‖h‖_{L²} (...)`:

* `RetBurnShift`: the stationary Gaussian field `Z`, error `√δ_N + e^{-ca}` (the weighted form of `BurninConcl` with
  `smoothDist 2` only; the initial term is the one of the burn-in, `a` is the burn-in time);
* `RetBurnInit`: the window starting at time `0` (so `a = 0`), compared with a solution of the linear fluctuation equation whose
  initial law is the weighted law of `ζ_N^0` (the initial field is retained, there is no burn-in); the error is `√δ_N`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.ME.Ret

open HRS HRS.LZ HRS.Uniform

def RetBurnShift (d : ℕ) : Prop :=
  ∀ (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (V : Torus d → ℝ) (_hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β)
    (m : ℝ), max ((d : ℝ) + 1) ((d : ℝ) / 2 + 2) < m → ∀ (T : ℝ), 0 < T →
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (ρβ : Torus d → ℝ), IsThermalDensity (periodicRiesz d s) V β ρβ →
      ∀ a : ℝ, 0 ≤ a → ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        IsStationaryGibbsFlow P s hs0 hsd V β hβ (a + T) X₀ W X →
      ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
        (Z : ℝ → Ω' → NegSobolev d m),
        IsStationaryGaussianField P' s β hs0 hsd hβ V ρβ m Z →
      ∀ h : Config d N → ℝ≥0∞, Measurable h → (∃ M : ℝ≥0, ∀ x, h x ≤ M) → ∫⁻ ω, h (X₀ ω) ∂P = 1 →
        ENNReal.ofReal (smoothDist 2
            ((P.withDensity fun ω => h (X₀ ω)).map (Main.windowZeta m T a P X))
            (law P' (Main.windowPath m T 0 Z))) ≤
          ENNReal.ofReal C * (∫⁻ ω, h (X₀ ω) ^ 2 ∂P) ^ (1 / 2 : ℝ) *
            ENNReal.ofReal (Real.exp (-c * a) + Real.sqrt (deltaN d s N))

def RetBurnInit (d : ℕ) : Prop :=
  ∀ (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (V : Torus d → ℝ) (_hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β)
    (ρβ : Torus d → ℝ), IsThermalDensity (periodicRiesz d s) V β ρβ →
    ∀ (m : ℝ), max ((d : ℝ) + 2) (max ((d : ℝ) + 1) ((d : ℝ) / 2 + 2)) < m → ∀ (T : ℝ), 0 < T →
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        IsStationaryGibbsFlow P s hs0 hsd V β hβ T X₀ W X →
      ∀ h : Config d N → ℝ≥0∞, Measurable h → (∃ M : ℝ≥0, ∀ x, h x ≤ M) → ∫⁻ ω, h (X₀ ω) ∂P = 1 →
        ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (_ : IsProbabilityMeasure P')
          (Y₀ : Ω' → NegSobolev d m) (Y : ℝ → Ω' → NegSobolev d m),
          IsLinearFluctuationSolution P' (PDE.mfData d s hs0 hsd V β hβ) (fun _ => ρβ) m β⁻¹ T Y₀ Y ∧
          P'.map Y₀ = (P.withDensity fun ω => h (X₀ ω)).map
            (fun ω => zetaE m (P.map (X 0)) (X 0 ω)) ∧
          ENNReal.ofReal (smoothDist 2
              ((P.withDensity fun ω => h (X₀ ω)).map (Main.windowZeta m T 0 P X))
              (law P' (Main.windowPath m T 0 Y))) ≤
            ENNReal.ofReal C * (∫⁻ ω, h (X₀ ω) ^ 2 ∂P) ^ (1 / 2 : ℝ) *
              ENNReal.ofReal (Real.sqrt (deltaN d s N))

end HRS.ME.Ret

end
