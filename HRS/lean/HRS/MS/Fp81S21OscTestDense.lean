import HRS.MS.Fp81S21GaussianSourceSpace

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace HRS.Fp81.S21

open HRS HRS.Whole

/-- A Gaussian upper bound on a nonnegative density implies domination of its physical
measure by a constant multiple of Lebesgue measure. -/
theorem fp81s21_withDensityReal_le_smul_volume_of_gaussian_upper
    {d : ℕ} {ρ : Euc d → ℝ} (hρ : ∀ x, 0 ≤ ρ x)
    {C c : ℝ} (hc : 0 < c)
    (hupper : ∀ x, ρ x ≤ C * Real.exp (-c * ‖x‖ ^ 2)) :
    HRS.Whole.withDensityReal ρ ≤ ENNReal.ofReal C • (volume : Measure (Euc d)) := by
  have hC : 0 ≤ C := by
    have h0 := hupper 0
    simpa using (hρ 0).trans h0
  rw [HRS.Whole.withDensityReal]
  calc
    volume.withDensity (fun x => ENNReal.ofReal (ρ x)) ≤
        volume.withDensity (fun _ => ENNReal.ofReal C) := by
      apply withDensity_mono
      filter_upwards with x
      apply ENNReal.ofReal_le_ofReal
      calc
        ρ x ≤ C * Real.exp (-c * ‖x‖ ^ 2) := hupper x
        _ ≤ C * 1 := mul_le_mul_of_nonneg_left
          (Real.exp_le_one_iff.mpr
            (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) (sq_nonneg ‖x‖))) hC
        _ = C := by ring
    _ = ENNReal.ofReal C • volume := by rw [withDensity_const]

/-- The canonical `L²(μ)` class of an oscillator test, when `μ` is bounded above by a
finite multiple of Lebesgue measure. -/
noncomputable def fp81s21_oscTest_toLp
    {d : ℕ} (μ : Measure (Euc d)) (C : ℝ≥0∞) (hC : C ≠ ∞)
    (hμ : μ ≤ C • (volume : Measure (Euc d)))
    (φ : fp81s21_oscTest d) : Lp ℝ 2 μ :=
  (φ.2.2.1.of_measure_le_smul hC hμ).toLp φ.1

/-- Oscillator tests are dense in physical `L²` for every finite measure with bounded density
relative to Lebesgue measure.  The test class contains every Schwartz function, and Mathlib's
Schwartz-to-`L²` density theorem applies to finite measures. -/
theorem fp81s21_oscTest_toLp_denseRange
    {d : ℕ} {μ : Measure (Euc d)} [IsFiniteMeasure μ]
    [IsFiniteMeasureOnCompacts μ]
    (C : ℝ≥0∞) (hC : C ≠ ∞)
    (hμ : μ ≤ C • (volume : Measure (Euc d))) :
    DenseRange (fp81s21_oscTest_toLp μ C hC hμ) := by
  have hdense : DenseRange (SchwartzMap.toLpCLM ℝ ℝ 2 μ) :=
    SchwartzMap.denseRange_toLpCLM (E := Euc d) (F := ℝ) (p := 2)
      ENNReal.ofNat_ne_top
  apply hdense.mono
  rintro y ⟨f, rfl⟩
  let φ : fp81s21_oscTest d :=
    ⟨f, ⟨f.smooth ⊤, memOsc_schwartz (wholeSpaceIndex d : ℝ) f⟩⟩
  refine ⟨φ, ?_⟩
  apply Lp.ext
  have hfμ : MemLp (φ.1) 2 μ := φ.2.2.1.of_measure_le_smul hC hμ
  filter_upwards [hfμ.coeFn_toLp, f.coeFn_toLp 2 μ] with x hxφ hxf
  rw [fp81s21_oscTest_toLp, hxφ, SchwartzMap.toLpCLM_apply, hxf]

#print axioms fp81s21_oscTest_toLp_denseRange
#print axioms fp81s21_withDensityReal_le_smul_volume_of_gaussian_upper

end HRS.Fp81.S21
end
