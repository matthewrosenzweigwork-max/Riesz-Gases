import HRS.MD.EQBurnDefs
import HRS.ME.Defs417

/-!
# Chunk E, row 2.10 path clauses: definitions (sorry-free)

The conclusion `CritBurnConcl` of the critical burn-in estimate (the analogue of `HRS.MD.EQBurn.BurninConcl` at `s = d/2` with the
rate `N^{-1/2}` of Proposition 2.10 in place of `N^{-1/4} + √δ_N`), and the two forms of the time-integrated centered forcing bound
that the critical estimate consumes:

* `CritForcing`: the bound in the form used by the engine, `E (sup_{t∈[a,a+T]∩ℚ} ‖∫_0^t 𝒱^{t,r}𝓡_stat^r dr‖_{E_m})² ≤ C²/N`
  (the critical analogue of `HRS.MD.EQ29.eq_rem_integrated`), with the constant chosen before `β ∈ [βm,βp]`, the thermal density,
  `a`, `N`, the probability space and the flow;
* `Uniform417`: Proposition 4.17 for a stationary Gibbs flow on the finite horizon `a+T`, with the constant chosen before
  `β ∈ [βm,βp]` and the thermal density.  The frozen statement `HRS.integrated_forcing` has the constant after `β`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.ME.Crit

open HRS HRS.LZ HRS.Uniform HRS.Main HRS.MD.EQ29

variable {d : ℕ}

/-- Proposition 4.17 on the finite horizon `a + T` (the form that the proof of `HRS.ME.integrated_forcing_type_proof` actually uses),
with the constant `C` chosen before `β ∈ [βm, βp]` and the thermal density. -/
def Uniform417 (d : ℕ) (hs0 : 0 ≤ (d : ℝ) / 2) (hsd : (d : ℝ) / 2 < d) (V : Torus d → ℝ) (βm βp : ℝ) (hβm : 0 < βm)
    (m T : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (β : ℝ) (hβ : β ∈ Set.Icc βm βp) (ρβ : Torus d → ℝ),
    IsThermalDensity (periodicRiesz d ((d : ℝ) / 2)) V β ρβ → Torus.IsSmooth ρβ → (∀ x, 0 < ρβ x) →
    ∀ N : ℕ, 2 ≤ N → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N) (a : ℝ), 0 ≤ a →
      IsStationaryGibbsFlow P ((d : ℝ) / 2) hs0 hsd V β (hβm.trans_le hβ.1) (a + T) X₀ W X →
      ∫⁻ ω, ⨆ t ∈ ratTimes 0 T, ∑' k : NonzeroLattice d,
          ENNReal.ofReal (integratedCenteredForcing (PDE.mfData d ((d : ℝ) / 2) hs0 hsd V β (hβm.trans_le hβ.1)) ρβ P X m k
            (a + t) ω ^ 2) ∂P ≤
        ENNReal.ofReal (C ^ 2 / N)

/-- The time-integrated stationary remainder at the critical rate, in the form consumed by the engine: for a stationary Gibbs flow on the
horizon `a + T`, `E (sup_{t ∈ [a,a+T] ∩ ℚ} ‖∫_0^t 𝒱^{t,r} 𝓡_stat^r dr‖_{E_m})² ≤ C²/N`, `C` chosen before `β ∈ [βm,βp]`,
the thermal density, `a`, `N`, the space and the flow; the window start `a` is rational, so that the rational times of `[a, a+T]` are
`a + (rational times of [0,T])`, the set over which `Uniform417` takes its supremum. -/
def CritForcing (d : ℕ) (hs0 : 0 ≤ (d : ℝ) / 2) (hsd : (d : ℝ) / 2 < d) (V : Torus d → ℝ) (βm βp : ℝ) (hβm : 0 < βm)
    (m T : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (β : ℝ) (hβ : β ∈ Set.Icc βm βp) (ρβ : Torus d → ℝ),
    IsThermalDensity (periodicRiesz d ((d : ℝ) / 2)) V β ρβ →
    ∀ N : ℕ, 2 ≤ N → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N) (a : ℝ), 0 ≤ a →
      (∃ q : ℚ, (q : ℝ) = a) →
      IsStationaryGibbsFlow P ((d : ℝ) / 2) hs0 hsd V β (hβm.trans_le hβ.1) (a + T) X₀ W X →
      ∫⁻ ω, (⨆ t ∈ ratTimes a T,
          (coordEnergy m (fun k => statForcingCoord d hs0 hsd V (hβm.trans_le hβ.1) ρβ X k t ω)) ^ (1 / 2 : ℝ)) ^ 2 ∂P ≤
        ENNReal.ofReal (C ^ 2 / N)

/-- The conclusion of the critical burn-in estimate (`s = d/2`), for rational window starts `a` (the supremum of `CritForcing` runs over
the rational times of `[a, a+T]`, which is `a + (rational times of [0,T])` only for rational `a`; the limit `a → ∞` uses `a ∈ ℕ`): `W_2` between the window `[a, a+T]` of the actual stationary process and
the window `[0, T]` of the stationary Gaussian field is at most `C (e^{-ca} + N^{-1/2})`, with `C, c` chosen before
`β ∈ [βm,βp]`, the thermal density, `a`, `N`, the spaces, the flow and the field. -/
def CritBurnConcl (d : ℕ) (hs0 : 0 ≤ (d : ℝ) / 2) (hsd : (d : ℝ) / 2 < d) (V : Torus d → ℝ) (βm βp : ℝ) (hβm : 0 < βm)
    (m T : ℝ) : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (β : ℝ) (hβ : β ∈ Set.Icc βm βp) (ρβ : Torus d → ℝ),
    IsThermalDensity (periodicRiesz d ((d : ℝ) / 2)) V β ρβ →
    ∀ a : ℝ, 0 ≤ a → (∃ q : ℚ, (q : ℝ) = a) → ∀ N : ℕ, 2 ≤ N →
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
      IsStationaryGibbsFlow P ((d : ℝ) / 2) hs0 hsd V β (hβm.trans_le hβ.1) (a + T) X₀ W X →
    ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
      (Z : ℝ → Ω' → NegSobolev d m),
      IsStationaryGaussianField P' ((d : ℝ) / 2) β hs0 hsd (hβm.trans_le hβ.1) V ρβ m Z →
      wassersteinE 2 (law P (Main.windowZeta m T a P X)) (law P' (Main.windowPath m T 0 Z)) ≤
        ENNReal.ofReal (C * (Real.exp (-c * a) + (N : ℝ) ^ (-(1 : ℝ) / 2)))

end HRS.ME.Crit

end
