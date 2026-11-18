import HRS.MS.Fp81S21WindowSup6

/-!
# HRS S2.1(iii), SOL40 packet 9d: centering adapter for the initial coordinate

Source audit carried forward from the compiled declarations:

* `s102_zf P X ζ u f` is definitionally
  `Real.sqrt N * (pair (empirical (X u.toNNReal ζ)) f -
    pair (meanEmpirical (P.map (X u.toNNReal))) f)`.
* `r2QuadField s μ P X u ζ f` is definitionally the positive centered
  `N * (pairEnergy (commutatorKernel d s (fun x => gradient f x))
    (X u.toNNReal ζ) μ -
    ∫ ζ', pairEnergy (commutatorKernel d s (fun x => gradient f x))
      (X u.toNNReal ζ') μ ∂P)`. The moving orbit identity places the external
  `-(Real.sqrt N)⁻¹` in front of its time integral.
* `fp81s21_particle_sixth_slices` bounds the reference-centered linear
  fluctuation `sqrt N * (pair (empirical ...) f - pair (r26t3_mu R u) f)`.
  The exact `s102_zf` is centered at its own expectation, so the generic
  centering step below costs a factor two in L⁶.
* `fp81s21_window_zero_order_orbit_bound_all_horizons` bounds
  `propagatorW (r26t3_coeff R) b t (oscTestFun ... α)` and `s101Dt` by
  `B * s104_b p.d α`; `s104_b` is already the coordinate amplitude.

This file proves only the probability-space centering adapter. It does not yet
assert an FTC identity or a path-supremum estimate.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace HRS.Fp81.S21

/-- Centering a real L⁶ coordinate by its own expectation costs at most a
factor two in the L⁶ seminorm on a probability space. -/
theorem fp81s21_centered_sixth_eLpNorm
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ) (hYmeas : Measurable Y) (M : ℝ)
    (hY : SixthBound P Y M) :
    eLpNorm (fun ω => Y ω - ∫ ω', Y ω' ∂P) (6 : ℝ≥0∞) P ≤
      2 * eLpNorm Y (6 : ℝ≥0∞) P := by
  have hYmem : MemLp Y (ENNReal.ofReal 6) P := by
    apply (integrable_norm_rpow_iff hYmeas.aestronglyMeasurable
      (by norm_num) (by norm_num)).1
    simpa [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 6)] using hY.1
  have hYint : Integrable Y P := hYmem.integrable (by norm_num)
  let m : ℝ := ∫ ω', Y ω' ∂P
  have hmean : ‖m‖ₑ ≤ eLpNorm Y 1 P := by
    calc
      ‖m‖ₑ ≤ ∫⁻ ω, ‖Y ω‖ₑ ∂P := enorm_integral_le_lintegral_enorm Y
      _ = eLpNorm Y 1 P := by
        symm
        exact eLpNorm_one_eq_lintegral_enorm hYint.aestronglyMeasurable
  have hmono : eLpNorm Y 1 P ≤ eLpNorm Y (6 : ℝ≥0∞) P :=
    eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
  have hcenter :
      (fun ω => Y ω - ∫ ω', Y ω' ∂P) = Y + (fun _ : Ω => -m) := by
    funext ω
    simp [m, sub_eq_add_neg]
  rw [hcenter]
  calc
    eLpNorm (Y + (fun _ : Ω => -m)) (6 : ℝ≥0∞) P ≤
        eLpNorm Y (6 : ℝ≥0∞) P + eLpNorm (fun _ : Ω => -m) (6 : ℝ≥0∞) P :=
      eLpNorm_add_le (by norm_num)
    _ = eLpNorm Y (6 : ℝ≥0∞) P + ‖m‖ₑ := by
      rw [eLpNorm_const _ (by norm_num) (IsProbabilityMeasure.ne_zero P)]
      simp
    _ ≤ eLpNorm Y (6 : ℝ≥0∞) P + eLpNorm Y (6 : ℝ≥0∞) P :=
      add_le_add le_rfl (hmean.trans hmono)
    _ = 2 * eLpNorm Y (6 : ℝ≥0∞) P := by ring

#print axioms fp81s21_centered_sixth_eLpNorm

end HRS.Fp81.S21

end
