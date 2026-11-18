import HRS.ME.SuscPos
import HRS.ME.TiltBounds
import HRS.ME.TiltConv
import HRS.MD.EQFrozen29Trans

/-!
# Example 5.12 (`cosine_tilt_example`): proof of the frozen statement

The three conjuncts of `HRS.cosine_tilt_example`:
* the uniform bounds on the tilt density: `HRS.ME.TiltBounds.tilt_density_bounds` applied to the canonical Gibbs law, which is a
  probability measure for every `N` (`N ≥ 1` by `HRS.MD.EQLawFlow.eqlaw_gibbs_prob`; for `N = 0` the configuration space is a point);
* the convergence of the tilted law: `HRS.ME.TiltConv.tilt_convergence`, whose analytic input is the centering clause of
  Theorem 2.9 (`HRS.MD.EQFrozen29Trans.centering_transition_proof`) and the positivity of `v` (`HRS.ME.SuscPos.susc_pos`);
* the limit density is not Gaussian: `HRS.ME.TiltBounds.cosineTiltDensity_not_gaussian`.
-/

open MeasureTheory

namespace HRS.ME.CosineTiltFinal

theorem gibbs_isProb {d : ℕ} (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {V : Torus d → ℝ}
    (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β) (N : ℕ) :
    IsProbabilityMeasure (canonicalGibbs (periodicRiesz d s) V N β) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have hH : ∀ X : Config d 0, canonicalHamiltonian (periodicRiesz d s) V X = 0 := fun X => by
      simp [canonicalHamiltonian]
    have hZ : canonicalPartition (periodicRiesz d s) V 0 β = 1 := by
      simp [canonicalPartition, hH]
    have e : canonicalGibbs (periodicRiesz d s) V 0 β = (volume : Measure (Config d 0)) := by
      simp [canonicalGibbs, hZ, hH]
    rw [e]
    infer_instance
  · exact HRS.MD.EQLawFlow.eqlaw_gibbs_prob hd hs0 hsd hV hβ hN

theorem cosine_tilt_example_proof {d : ℕ} : type_of% (@HRS.cosine_tilt_example d) := by
  intro s hd hs0 hs β hβ V hV ρ hρ ψ hψ hnc a ha0 ha1
  have hsd : s < d := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hv := HRS.ME.SuscPos.susc_pos hd hs0 hs β hβ V hV ρ hρ ψ hψ hnc
  have hψc : Continuous ψ := StaticLimitAux.continuous_of_smooth hψ
  refine ⟨fun N X => ?_, HRS.ME.TiltConv.tilt_convergence hd hs0 hs β hβ V hV ρ hρ ψ hψ
    HRS.MD.EQFrozen29Trans.centering_transition_proof hv a ha1, fun m w => ?_⟩
  · haveI := gibbs_isProb hd hs0 hsd hV hβ N
    exact HRS.ME.TiltBounds.tilt_density_bounds (canonicalGibbs (periodicRiesz d s) V N β)
      (linCoord (withDensityReal ρ) ψ) (HRS.ME.CondExample.linCoord_measurable hψc) ha1 X
  · exact HRS.ME.TiltBounds.cosineTiltDensity_not_gaussian ha0 ha1 hv m w

end HRS.ME.CosineTiltFinal
