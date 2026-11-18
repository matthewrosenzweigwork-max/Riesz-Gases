import HRS.MS.Fp81S21MovingDuality2
import HRS.MS.Fp81S21ParticleSixthSlices
import HRS.MS.Fp81S21WindowOrbitDecay2

/-!
# HRS S2.1(iii), SOL40 packet 9d: L⁶ integral brick

Source audit (the displayed formulas below are copied from the compiled source
definitions/contracts, not inferred from the manuscript notation):

* `s102_zf P X ζ u f` is definitionally
  `Real.sqrt N * (pair (empirical (X u.toNNReal ζ)) f -
    pair (meanEmpirical (P.map (X u.toNNReal))) f)`.
* `r2QuadField s μ P X u ζ f` is definitionally
  `N * (pairEnergy (commutatorKernel d s (fun x => gradient f x))
    (X u.toNNReal ζ) μ -
    ∫ ζ', pairEnergy (commutatorKernel d s (fun x => gradient f x))
      (X u.toNNReal ζ') μ ∂P)`. It is the positive centered field; the
  external minus `Real.sqrt N⁻¹` belongs to the moving orbit identity.
* `fp81s21_moving_orbit_zeta` has, for fixed terminal `t` and `τ ∈ [0,t]`,
  `s102_zf A.P F.X ζ τ (U^{τ,t} φ) = s102_zf A.P F.X ζ 0 (U^{0,t} φ)`
  plus the Itô term with coefficient
  `Real.sqrt N * (Real.sqrt (2 * p.β⁻¹) / N)` and the integral of
  `-(Real.sqrt N)⁻¹ * r2QuadField p.s (r26t3_mu R r) A.P F.X r ζ
    (U^{r,t} φ)` over `[0,τ]`.
* `fp81s21_window_Bpos` is definitionally
  `Cs0 * Real.sqrt (∑' α, (s104_b p.d α)^2) *
    exp (-cdec * max (a-v) 0)`. The coordinate amplitude is the factor
  `s104_b p.d α` inside this square-sum identity, so it is not inserted a
  second time into the coordinate.

The public `fp81s21_moving_observation_window_orbit_decay` exports gradient
decay for the terminal test and generator terminal test. The broader moving
`S101Data` contract exports bounded spatial derivatives and `derivWithin`
regularity; the construction's generator equality is private in
`Fp81S21MovingStd2`. This file currently proves only the Banach-valued L⁶
Minkowski brick below. It does not assert a path supremum estimate or establish
measurability of any path supremum.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace HRS.Fp81.S21

local instance : Fact ((1 : ℝ≥0∞) ≤ (6 : ℝ≥0∞)) := ⟨by norm_num⟩

/-- Banach-valued Minkowski for a time-integrable family in `L⁶(P)`.  This is
the integral brick used before a pathwise majorant can be turned into a
supremum estimate. -/
theorem fp81s21_l6_lp_integral_minkowski
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) (ν : Measure S) [SFinite ν]
    (G : S → Lp ℝ (6 : ℝ≥0∞) P) (hG : Integrable G ν) :
    (eLpNorm (∫ s, G s ∂ν : Lp ℝ (6 : ℝ≥0∞) P)
      (6 : ℝ≥0∞) P).toReal ≤
        ∫ s, (eLpNorm (G s) (6 : ℝ≥0∞) P).toReal ∂ν := by
  calc
    (eLpNorm (∫ s, G s ∂ν : Lp ℝ (6 : ℝ≥0∞) P)
      (6 : ℝ≥0∞) P).toReal = ‖∫ s, G s ∂ν‖ := by rw [Lp.norm_def]
    _ ≤ ∫ s, ‖G s‖ ∂ν := norm_integral_le_integral_norm G
    _ = ∫ s, (eLpNorm (G s) (6 : ℝ≥0∞) P).toReal ∂ν := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun s => by
        exact (show (eLpNorm (G s) (6 : ℝ≥0∞) P).toReal = ‖G s‖ by
          rw [Lp.norm_def]).symm

#print axioms fp81s21_l6_lp_integral_minkowski

end HRS.Fp81.S21

end
