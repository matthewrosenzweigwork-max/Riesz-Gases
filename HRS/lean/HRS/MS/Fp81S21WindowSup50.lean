import HRS.MS.Fp81S21WindowSup49

/-! Time-shift comparison for the frozen-source drift majorant. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace HRS.Fp81.S21
open HRS.MS.R2WinErr

/-- An elapsed-time lower integral over `[0,t-v]` is bounded by the
corresponding physical-time lower integral over the whole shifted window. -/
theorem fp81s21_window_lintegral_elapsed_le
    (b T v t : ℝ) (hbv : b ≤ v) (hvt : v ≤ t) (htT : t ≤ T)
    (f : ℝ → ℝ≥0∞) :
    (∫⁻ u in Ioc (0 : ℝ) (t - v), f (v + u)) ≤
      ∫⁻ s in Icc b T, f s := by
  have hshift := s104_lintegral_Ioc_sub (fun u => f (v + u)) v t v
  have heq : (∫⁻ u in Ioc (0 : ℝ) (t - v), f (v + u)) =
      ∫⁻ s in Ioc v t, f s := by
    simpa only [sub_self, add_sub_cancel] using hshift
  rw [heq]
  apply lintegral_mono_set
  intro s hs
  exact ⟨hbv.trans hs.1.le, hs.2.trans htT⟩

#print axioms fp81s21_window_lintegral_elapsed_le
end HRS.Fp81.S21
end
