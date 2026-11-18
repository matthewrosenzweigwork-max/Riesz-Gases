import HRS.MD.EQ29Vocab
import HRS.Main.T25PAux13

/-!
# EQ-BURN-DEFS (chunk D): sorry-free definitions of the burn-in route

`EvoPkg` and `BurninConcl`, split from `HRS/MD/EQBurnSpec.lean` so that proof modules need not import the sorried specification file.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

namespace MD

namespace EQBurn

open HRS.LZ HRS.Uniform HRS.Main

/-! ### Definitions (sorry-free) -/

/-- The evolution package hypothesis of the burn-in: for every `β ∈ [βm,βp]` and every thermal density `ρβ`, a dual evolution `Vev` of the
frozen coefficient `ρβ` (`IsDualEvolution (PDE.mfData ..) (fun _ => ρβ) m Vev`) that carries the `T25Ev` package (plain evolution, decay
`K e^{-c(t-u)}`, measurable maximal estimate on windows of length `T` with constant `Cmax`, existence of the stochastic convolution),
with `K, c, Cmax` chosen BEFORE `β` and `ρβ`. -/
def EvoPkg (d : ℕ) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (V : Torus d → ℝ) (βm βp : ℝ) (hβm : 0 < βm)
    (m K c T Cmax : ℝ) : Prop :=
  ∀ (β : ℝ) (hβ : β ∈ Set.Icc βm βp) (ρβ : Torus d → ℝ), IsThermalDensity (periodicRiesz d s) V β ρβ →
    ∃ Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m,
      HRS.T25P.T25Ev m K c T Cmax Vev ∧
      IsDualEvolution (PDE.mfData d s hs0 hsd V β (hβm.trans_le hβ.1)) (fun _ => ρβ) m Vev

/-- The conclusion of `eq_burnin` (copied verbatim from `HRS/MD/EQ29Spec.lean`, for the fixed data `d s V βm βp m T`). -/
def BurninConcl (d : ℕ) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (V : Torus d → ℝ) (βm βp : ℝ) (hβm : 0 < βm)
    (m T : ℝ) : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (β : ℝ) (hβ : β ∈ Set.Icc βm βp) (ρβ : Torus d → ℝ),
      IsThermalDensity (periodicRiesz d s) V β ρβ →
      ∀ a : ℝ, 0 ≤ a → ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        IsStationaryGibbsFlow P s hs0 hsd V β (hβm.trans_le hβ.1) (a + T) X₀ W X →
      ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
        (Z : ℝ → Ω' → NegSobolev d m),
        IsStationaryGaussianField P' s β hs0 hsd (hβm.trans_le hβ.1) V ρβ m Z →
        smoothDist 2 (law P (Main.windowZeta m T a P X)) (law P' (Main.windowPath m T 0 Z)) ≤
            C * (Real.exp (-c * a) + Real.sqrt (deltaN d s N)) ∧
        wassersteinE 2 (law P (Main.windowZeta m T a P X)) (law P' (Main.windowPath m T 0 Z)) ≤
            ENNReal.ofReal (C * (Real.exp (-c * a) + (N : ℝ) ^ (-(1 : ℝ) / 4) +
              Real.sqrt (deltaN d s N)))

end EQBurn

end MD

end HRS
