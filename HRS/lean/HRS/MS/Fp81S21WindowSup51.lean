import HRS.MS.Fp81S21WindowSup50

/-! Pathwise triangular majorant for a frozen-source drift. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace HRS.Fp81.S21

/-- A frozen-source FTC implies the whole-window supremum is bounded by the
baseline lower integral plus the two-time lower integral. -/
theorem fp81s21_window_frozen_drift_majorant
    (b T : ℝ) (hbT : b ≤ T) (A : ℝ → ℝ → ℝ) (q : ℝ → ℝ) (k : ℝ → ℝ → ℝ)
    (hq : Measurable q) (hk : Measurable (Function.uncurry k))
    (hRep : ∀ v t, b ≤ v → v ≤ t → t ≤ T →
      A v t = q v + ∫ u in (0 : ℝ)..(t - v), k v (v + u)) :
    (⨆ t : Icc b T, ENNReal.ofReal |∫ v in b..(t : ℝ), A v t|) ≤
      (∫⁻ v in Icc b T, ENNReal.ofReal |q v|) +
      ∫⁻ z : ℝ × ℝ, ENNReal.ofReal |k z.1 z.2|
        ∂((volume.restrict (Icc b T)).prod (volume.restrict (Icc b T))) := by
  let ν : Measure ℝ := volume.restrict (Icc b T)
  let Q : ℝ → ℝ≥0∞ := fun v => ENNReal.ofReal |q v|
  let K : ℝ × ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal |k z.1 z.2|
  let J : ℝ → ℝ≥0∞ := fun v => ∫⁻ s, K (v, s) ∂ν
  have hQ : Measurable Q := ENNReal.measurable_ofReal.comp (measurable_abs.comp hq)
  have hK : Measurable K := ENNReal.measurable_ofReal.comp (measurable_abs.comp hk)
  have hJ : Measurable J := hK.lintegral_prod_right'
  have hloc : ∀ v t, b ≤ v → v ≤ t → t ≤ T →
      ENNReal.ofReal |A v t| ≤ Q v + J v := by
    intro v t hbv hvt htT
    have hnonneg : 0 ≤ t - v := by linarith
    have hft := hRep v t hbv hvt htT
    have hIntegral : ENNReal.ofReal |∫ u in (0 : ℝ)..(t - v), k v (v + u)| ≤
        ∫⁻ u in Ioc (0 : ℝ) (t - v), ENNReal.ofReal |k v (v + u)| := by
      rw [intervalIntegral.integral_of_le hnonneg]
      simpa [Real.enorm_eq_ofReal_abs] using
        (enorm_integral_le_lintegral_enorm (μ := volume.restrict (Ioc (0 : ℝ) (t - v)))
          (fun u => k v (v + u)))
    have hshift := fp81s21_window_lintegral_elapsed_le b T v t hbv hvt htT
      (fun s => ENNReal.ofReal |k v s|)
    calc
      _ ≤ ENNReal.ofReal (|q v| + |∫ u in (0 : ℝ)..(t - v), k v (v + u)|) := by
        apply ENNReal.ofReal_le_ofReal
        rw [hft]
        exact abs_add_le _ _
      _ = Q v + ENNReal.ofReal |∫ u in (0 : ℝ)..(t - v), k v (v + u)| := by
        simp [Q, ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
      _ ≤ Q v + J v := add_le_add le_rfl (hIntegral.trans hshift)
  have hprod : (∫⁻ z, K z ∂(ν.prod ν)) = ∫⁻ v, J v ∂ν := by
    exact lintegral_prod K hK.aemeasurable
  apply iSup_le
  intro t
  have hbt : b ≤ (t : ℝ) := t.2.1
  have hOuter : ENNReal.ofReal |∫ v in b..(t : ℝ), A v t| ≤
      ∫⁻ v in Ioc b (t : ℝ), ENNReal.ofReal |A v t| := by
    rw [intervalIntegral.integral_of_le hbt]
    simpa [Real.enorm_eq_ofReal_abs] using
      (enorm_integral_le_lintegral_enorm (μ := volume.restrict (Ioc b (t : ℝ)))
        (fun v => A v t))
  calc
    _ ≤ ∫⁻ v in Ioc b (t : ℝ), (Q v + J v) := by
      refine hOuter.trans (setLIntegral_mono' measurableSet_Ioc ?_)
      intro v hv
      exact hloc v t hv.1.le hv.2 t.2.2
    _ = (∫⁻ v in Ioc b (t : ℝ), Q v) + ∫⁻ v in Ioc b (t : ℝ), J v := by
      rw [lintegral_add_left' hQ.aemeasurable]
    _ ≤ (∫⁻ v, Q v ∂ν) + ∫⁻ v, J v ∂ν := by
      apply add_le_add <;> apply lintegral_mono_set <;>
        exact fun v hv => ⟨hv.1.le, hv.2.trans t.2.2⟩
    _ = _ := by rw [hprod]

#print axioms fp81s21_window_frozen_drift_majorant
end HRS.Fp81.S21
end
