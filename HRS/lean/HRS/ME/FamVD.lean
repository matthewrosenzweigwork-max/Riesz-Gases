import HRS.ME.FamVC
import HRS.MD.EQGaussWindow
import HRS.MD.EQBurnClt

/-!
# Packet V3b (namespace `HRS.ME.FamV`): the time-zero rate observable of a stationary Gaussian field

For a stationary Gaussian field `Z` with the equilibrium susceptibility covariance (predicate
`HRS.IsStationaryGaussianField`), the image under `rateEval` (the time-zero coordinate paired with
`cos_k`, see `HRS/ME/FamVC.lean`) of the law of the window `ζ^{0+·} = windowPath m T 0 Z` is the
centred Gaussian `HRS.Main.rateGaussian d s k β ρ`.

* `rate_gauss_law`: the main statement.  Route: `rateEval` of the window is `NegSobolev.eval (Z 0 ·) cos_k`
  almost surely (continuity of the trajectory, `eqgw_windowPath_at`); the one-dimensional marginal at time
  `0` is the centred Gaussian with variance `C_{β,ρ}(cos_k, cos_k)` (`HRS.MD.EQBurnClt.eqclt_gauss_law`,
  which uses `equilibriumSemigroup_zero_ck` for the time-zero semigroup).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.ME.FamV

/-- Main statement (packet V3b). For a stationary Gaussian field with the equilibrium covariance of the
thermal density `ρ` of the potential `V`, the image under `rateEval` of the law of the window
`windowPath m T 0 Z` is the rate Gaussian `HRS.Main.rateGaussian d s k β ρ`. -/
theorem rate_gauss_law {d : ℕ} (hd : 2 ≤ d) {s β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β)
    (k : Lattice d) (V ρ : Torus d → ℝ) (hV : Torus.IsSmooth V)
    (hρ : HRS.IsThermalDensity (HRS.periodicRiesz d s) V β ρ) {m T : ℝ} (hT : 0 ≤ T)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Z : ℝ → Ω' → NegSobolev d m)
    (hZ : HRS.IsStationaryGaussianField P' s β hs0 hsd hβ V ρ m Z) :
    (HRS.law P' (HRS.Main.windowPath m T 0 Z)).map (rateEval d m T hT k) =
      HRS.Main.rateGaussian d s k β ρ := by
  have hW : AEMeasurable (HRS.Main.windowPath m T 0 Z) P' :=
    (HRS.MD.EQGaussWindow.eqgw_fidi hd hs0 hsd V hβ ρ m T P' Z hZ 0 le_rfl).1
  have hae : (rateEval d m T hT k ∘ HRS.Main.windowPath m T 0 Z) =ᵐ[P']
      (fun ω => NegSobolev.eval (Z 0 ω) (Torus.cosMode k)) := by
    filter_upwards [hZ.cont] with ω hω
    have h0 : (0 : ℝ) + ((t0 hT : Set.Icc (0 : ℝ) T) : ℝ) = 0 := by simp [t0]
    show rateEval d m T hT k (HRS.Main.windowPath m T 0 Z ω) = _
    rw [rateEval_apply, HRS.MD.EQGaussWindow.eqgw_windowPath_at T 0 le_rfl Z ω hω (t0 hT), h0]
  calc (HRS.law P' (HRS.Main.windowPath m T 0 Z)).map (rateEval d m T hT k)
      = P'.map (rateEval d m T hT k ∘ HRS.Main.windowPath m T 0 Z) :=
        AEMeasurable.map_map_of_aemeasurable (rateEval d m T hT k).continuous.measurable.aemeasurable hW
    _ = P'.map (fun ω => NegSobolev.eval (Z 0 ω) (Torus.cosMode k)) := Measure.map_congr hae
    _ = HRS.Main.rateGaussian d s k β ρ :=
        HRS.MD.EQBurnClt.eqclt_gauss_law hd hs0 hsd V hV hβ ρ hρ P' Z hZ (HRS.d1_isSmooth_cosMode k)

end HRS.ME.FamV
