import HRS.MS.Fp81S21WindowDriftId3

/-! Whole-horizon specialization for the projection-removal value. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp

/-- The unprojected whole-horizon RS value from projection removal is the
window RS selection on the whole horizon. -/
theorem fp81s21_unprojected_isR2RS_window_drift_value
    (p : Parameters) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (a : ℝ) (ha : 0 ≤ a) (hH : 0 < a + p.T)
    (future : (H : ℝ) → ℝ → Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H))
    (hfuture : ∀ H v, IsProbabilityMeasure (future H v))
    (Φ : Window p → ℝ) (hΦ : MemCb 5 Φ)
    (C : WholeCoeff p.d) (b : Ω → ℝ → (Euc p.d → ℝ) → ℝ)
    (Y Fd : Ω → ℝ → OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T))
    (hFd : ∀ᵐ ω ∂μ, Fd ω 0 = 0 ∧
      ∀ u v, 0 ≤ u → u ≤ v → v ≤ a + p.T →
        Fd ω v - Fd ω u = r2DriftInc C (wholeSpaceIndex p.d : ℝ) (a + p.T)
          (fun t f => b ω t f) u v)
    (WSW : fp81s21_RSBVWindow μ (a + p.T)
      (fun ω τ => fderiv ℝ (initialHeat future a ha Φ τ)
        (HRS.MS.ProClosureS111.physicalWindowRestriction
          (d := p.d) (m := (wholeSpaceIndex p.d : ℝ))
          (T := p.T) (H := a + p.T) ha le_rfl (Y ω τ)))
      (fun ω t => fp81s21_weightedDrift_windowCum
        (m := (wholeSpaceIndex p.d : ℝ)) ha le_rfl C (fun u f => b ω u f) t))
    (dval : Ω → ℝ)
    (hdval : ∀ᵐ ω ∂μ, IsR2RS (a + p.T)
      (fun t u v => fderiv ℝ
        (r2HeatFn (future (a + p.T))
          (fun w => Φ (HRS.MS.ProClosureS111.physicalWindowRestriction
            (d := p.d) (m := (wholeSpaceIndex p.d : ℝ))
            (T := p.T) (H := a + p.T) ha le_rfl w)) t) (Y ω t)
        (r2DriftInc C (wholeSpaceIndex p.d : ℝ) (a + p.T)
          (fun s f => b ω s f) u v)) (dval ω)) :
    dval =ᵐ[μ] WSW.value 0 (a + p.T) := by
  apply fp81s21_unprojected_isRSOn_window_drift_value p μ a ha future hfuture Φ hΦ C b
    Y Fd hFd WSW 0 (a + p.T) (le_refl 0) (le_of_lt hH) (le_refl _) dval
  simpa only [fp81s21_IsRSOn, sub_zero, zero_add] using hdval

end HRS.Fp81.S21
end
#print axioms HRS.Fp81.S21.fp81s21_unprojected_isR2RS_window_drift_value
