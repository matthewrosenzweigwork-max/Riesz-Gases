import HRS.MS.Fp81S21MovingHeat4

/-! Derivatives of the full-history heat function are the pullbacks of the
derivatives on the physical observation window. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.Sec7 HRS.MS.R26T3 HRS.MS.R2Interp

/-- Iterated derivatives commute with restriction to a physical window.
The full-history future is assumed probability-valued so the established
window heat regularity theorem applies. -/
theorem fp81s21_initialHeat_pullback_iteratedFDeriv
    {p : Parameters}
    (future : (H : ℝ) → ℝ →
      Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H))
    (hfuture : ∀ H v, IsProbabilityMeasure (future H v))
    (b : ℝ) (hb : 0 ≤ b)
    (Φ : Window p → ℝ) (hΦ : MemCb 5 Φ) (v : ℝ) :
    let W := HRS.MS.ProClosureS111.physicalWindowRestriction
      (d := p.d) (m := (wholeSpaceIndex p.d : ℝ))
      (T := p.T) (H := b + p.T) hb le_rfl
    ∀ j ≤ 5, ∀ y,
      iteratedFDeriv ℝ j
          (r2HeatFn (future (b + p.T)) (fun w => Φ (W w)) v) y =
        (iteratedFDeriv ℝ j (initialHeat future b hb Φ v) (W y)).compContinuousLinearMap
          (fun _ => W) := by
  let W := HRS.MS.ProClosureS111.physicalWindowRestriction
    (d := p.d) (m := (wholeSpaceIndex p.d : ℝ))
    (T := p.T) (H := b + p.T) hb le_rfl
  intro W' j hj y
  have hcont : ContDiff ℝ 5 (initialHeat future b hb Φ v) :=
    (fp81s21_windowFuture_heat_derivs future hfuture b hb Φ hΦ v).1
  have hfun :
      r2HeatFn (future (b + p.T)) (fun w => Φ (W' w)) v =
        initialHeat future b hb Φ v ∘ W' := by
    funext y
    simpa only [Function.comp_apply] using
      (fp81s21_initialHeat_pullback future b hb Φ hΦ v y).symm
  rw [hfun]
  exact W'.iteratedFDeriv_comp_right hcont y (by exact_mod_cast hj)

/-- Operator norm bound for the pulled-back iterated derivative. -/
theorem fp81s21_initialHeat_pullback_iteratedFDeriv_norm
    {p : Parameters}
    (future : (H : ℝ) → ℝ →
      Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H))
    (hfuture : ∀ H v, IsProbabilityMeasure (future H v))
    (b : ℝ) (hb : 0 ≤ b)
    (Φ : Window p → ℝ) (hΦ : MemCb 5 Φ) (v : ℝ) :
    let W := HRS.MS.ProClosureS111.physicalWindowRestriction
      (d := p.d) (m := (wholeSpaceIndex p.d : ℝ))
      (T := p.T) (H := b + p.T) hb le_rfl
    ∀ j ≤ 5, ∀ y,
      ‖iteratedFDeriv ℝ j
          (r2HeatFn (future (b + p.T)) (fun w => Φ (W w)) v) y‖ ≤
        ‖iteratedFDeriv ℝ j (initialHeat future b hb Φ v) (W y)‖ * ‖W‖ ^ j := by
  let W := HRS.MS.ProClosureS111.physicalWindowRestriction
    (d := p.d) (m := (wholeSpaceIndex p.d : ℝ))
    (T := p.T) (H := b + p.T) hb le_rfl
  intro W' j hj y
  rw [fp81s21_initialHeat_pullback_iteratedFDeriv future hfuture b hb Φ hΦ v j hj y]
  calc
    ‖(iteratedFDeriv ℝ j (initialHeat future b hb Φ v) (W y)).compContinuousLinearMap
        (fun _ => W)‖ ≤
      ‖iteratedFDeriv ℝ j (initialHeat future b hb Φ v) (W y)‖ *
        ∏ i : Fin j, ‖W‖ := ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = ‖iteratedFDeriv ℝ j (initialHeat future b hb Φ v) (W y)‖ * ‖W‖ ^ j := by simp

#print axioms HRS.Fp81.S21.fp81s21_initialHeat_pullback_iteratedFDeriv
#print axioms HRS.Fp81.S21.fp81s21_initialHeat_pullback_iteratedFDeriv_norm

end HRS.Fp81.S21

end
