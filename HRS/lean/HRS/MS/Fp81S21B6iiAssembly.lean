import HRS.MS.Fp81S21B6iiEmp4

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Set
namespace HRS.Fp81.S21

/-- Subtracting two primitives and translating the resulting interval. -/
theorem fp81s21_b6ii_shifted_primitive (g : ℝ → ℝ) {a H s t : ℝ}
    (ha : 0 ≤ a) (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ H)
    (hg : IntegrableOn g (Icc 0 (a + H))) :
    (∫ v in Icc 0 (a + t), g v) - (∫ v in Icc 0 (a + s), g v) =
      ∫ v in Icc s t, g (a + v) := by
  have has : 0 ≤ a + s := add_nonneg ha hs
  have hast : a + s ≤ a + t := by simpa [add_comm] using add_le_add_left hst a
  have hat : 0 ≤ a + t := has.trans hast
  have his : IntegrableOn g (Icc 0 (a + s)) :=
    hg.mono_set (Icc_subset_Icc le_rfl (by linarith))
  have hist : IntegrableOn g (Icc (a + s) (a + t)) :=
    hg.mono_set (Icc_subset_Icc has (by linarith))
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    ((intervalIntegrable_iff_integrableOn_Icc_of_le has).2 his)
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hast).2 hist)
  rw [intervalIntegral.integral_of_le has, intervalIntegral.integral_of_le hast,
    intervalIntegral.integral_of_le hat, ← integral_Icc_eq_integral_Ioc,
    ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc] at hadd
  have hshift := intervalIntegral.integral_comp_add_left (a := s) (b := t) g a
  rw [intervalIntegral.integral_of_le hst, intervalIntegral.integral_of_le hast,
    ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc] at hshift
  linarith

#print axioms fp81s21_b6ii_shifted_primitive
end HRS.Fp81.S21
end
