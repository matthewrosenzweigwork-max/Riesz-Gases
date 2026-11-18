import HRS.MS.Fp81S21MovingHeat3

/-!
# HRS S2.1(iii), packet 12c: public moving heat family

The reduced 12c contract exports the full-horizon regularity clauses from
12a/12b together with probability and spatial derivative formulas on physical
windows.  It does not assert local-window S102LipProj or projected convergence:
the full-horizon route uses H = b + p.T and the test Φ ∘ W_b.  The window
restriction keeps the absolute cutoff v unchanged, including v = 0; no
constants uniform in the window start b are asserted.  Also, s102_projHeatD
projects its evaluation point, not its derivative arguments.  No cross-horizon
compatibility clause is needed by this package.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.Sec7 HRS.MS.R26T3 HRS.MS.R2Interp

/-- The reduced consumer-facing packet-12 contract: retain every full-horizon
12a/12b clause for one selected future and add its probability and spatial
heat-derivative formulas on every physical observation window. -/
theorem fp81s21_moving_heat_family (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∃ future : (H : ℝ) → ℝ →
            Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H),
          fp81s21_moving_heat_full_clause p R future ∧
          (∀ b : ℝ, ∀ hb : 0 ≤ b, ∀ v : ℝ,
            IsProbabilityMeasure (windowFuture future b hb v)) ∧
          (∀ b : ℝ, ∀ hb : 0 ≤ b,
            ∀ (Φ : Window p → ℝ), MemCb 5 Φ → ∀ u : ℝ,
              ContDiff ℝ 5 (r2HeatFn (windowFuture future b hb) Φ u) ∧
              ∀ j ≤ 5, ∀ y,
                iteratedFDeriv ℝ j
                    (r2HeatFn (windowFuture future b hb) Φ u) y =
                  ∫ z, iteratedFDeriv ℝ j Φ (y + z)
                    ∂(windowFuture future b hb u) ∧
                ‖iteratedFDeriv ℝ j
                    (r2HeatFn (windowFuture future b hb) Φ u) y‖ ≤
                  ⨆ z, ‖iteratedFDeriv ℝ j Φ z‖) :=
  fp81s21_moving_heat_family_window_derivs p

/-- Pull the physical-window heat function back to the full-history space.
This is the change-of-variables identity for the measure map defining
windowFuture; it makes no claim about transferring a projection estimate. -/
theorem fp81s21_initialHeat_pullback
    {p : Parameters}
    (future : (H : ℝ) → ℝ →
      Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H))
    (b : ℝ) (hb : 0 ≤ b)
    (Φ : Window p → ℝ) (hΦ : MemCb 5 Φ)
    (v : ℝ)
    (y : OscPath p.d (wholeSpaceIndex p.d : ℝ) (b + p.T)) :
    let W :=
      HRS.MS.ProClosureS111.physicalWindowRestriction
        (d := p.d) (m := (wholeSpaceIndex p.d : ℝ))
        (T := p.T) (H := b + p.T) hb le_rfl
    initialHeat future b hb Φ v (W y) =
      r2HeatFn (future (b + p.T)) (fun w => Φ (W w)) v y := by
  let W :=
    HRS.MS.ProClosureS111.physicalWindowRestriction
      (d := p.d) (m := (wholeSpaceIndex p.d : ℝ))
      (T := p.T) (H := b + p.T) hb le_rfl
  change
    (∫ z : OscPath p.d (wholeSpaceIndex p.d : ℝ) p.T,
      Φ (W y + z) ∂Measure.map W (future (b + p.T) v)) =
    ∫ z : OscPath p.d (wholeSpaceIndex p.d : ℝ) (b + p.T),
      Φ (W (y + z)) ∂future (b + p.T) v
  have hsm :
      AEStronglyMeasurable
        (fun z : OscPath p.d (wholeSpaceIndex p.d : ℝ) p.T => Φ (W y + z))
        (Measure.map W (future (b + p.T) v)) :=
    (hΦ.1.continuous.comp (by fun_prop)).aestronglyMeasurable
  rw [integral_map W.continuous.aemeasurable hsm]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [map_add]

#print axioms HRS.Fp81.S21.fp81s21_moving_heat_family
#print axioms HRS.Fp81.S21.fp81s21_initialHeat_pullback

end HRS.Fp81.S21

end
