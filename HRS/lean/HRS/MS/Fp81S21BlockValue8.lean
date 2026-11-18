import HRS.MS.Fp81S21BlockValue7

/-!
# S2.1(iii), packet 15d-4: localized entry integrability

The four observation terms are ordinary integrals because each entry of the
localized trace density is integrable on the unit clock.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.Uniform HRS.MS.CovMeas

/-- Every scalar entry of a localized unit-clock form is integrable. This is
the entrywise consequence of the trace-norm integrability clause in
`IsTraceDensityL1`. -/
theorem fp81s21_windowLocal_entry_integrable
    {d : ℕ} {C : WholeCoeff d} {m H a : ℝ} {r : ℕ} {P : ℝ}
    {z : ℝ → (Euc d → ℝ) → ℝ} {Cmix cdec : ℝ}
    (D : fp81s21_WindowLocalInput C m H a r P z Cmix cdec)
    {I : Set ℝ} (hI : MeasurableSet I) (k : ℕ)
    (u w : KSpace d m H) :
    IntegrableOn
      (fun s => fp81s21_windowLocalD I k C m H a z D.fp81s21_ha
        (le_of_lt D.fp81s21_hH) s u w)
      (Icc (0 : ℝ) 1) := by
  let Dloc : ℝ → KSpace d m H →L[ℝ] KSpace d m H →L[ℝ] ℝ :=
    fun s => fp81s21_windowLocalD I k C m H a z D.fp81s21_ha
      (le_of_lt D.fp81s21_hH) s
  have htrace := fp81s21_windowLocal_isTraceDensityL1 D hI k
  have htr : IntegrableOn (fun s => traceNormForm (Dloc s))
      (Icc (0 : ℝ) 1) := htrace.2.2.2
  refine Integrable.mono' (htr.mul_const (‖u‖ * ‖w‖))
    ((htrace.2.2.1 u w).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  rw [Real.norm_eq_abs]
  exact s101_abs_le_tn (htrace.2.1 s hs) u w

#print axioms fp81s21_windowLocal_entry_integrable

end HRS.Fp81.S21

end
