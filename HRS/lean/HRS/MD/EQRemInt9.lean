import HRS.MD.EQRemInt8

/-!
# EQ-REM (b), part 9: Cauchy-Schwarz in `ℝ≥0∞`, coordinate bounds from the `E_M`-energy
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MD.EQRem

open HRS HRS.MD.EQ29 HRS.Quad

variable {d : ℕ}

theorem eqrem_sq_rpow_half (x : ℝ≥0∞) : (x ^ (1 / 2 : ℝ)) ^ 2 = x := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num

theorem eqrem_rpow_half_le_of_le_sq {x I : ℝ≥0∞} (h : x ≤ I ^ 2) : x ^ (1 / 2 : ℝ) ≤ I := by
  calc x ^ (1 / 2 : ℝ) ≤ (I ^ 2) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow h (by norm_num)
    _ = I := by rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num

/-- Cauchy-Schwarz in `ℝ≥0∞`. -/
theorem eqrem_cs {α : Type*} [MeasurableSpace α] (μ : Measure α) (h : α → ℝ≥0∞)
    (hh : AEMeasurable h μ) :
    (∫⁻ x, h x ∂μ) ^ 2 ≤ μ Set.univ * ∫⁻ x, h x ^ 2 ∂μ := by
  have H := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
    (aemeasurable_const (b := (1 : ℝ≥0∞))) hh
  simp only [Pi.mul_apply, one_mul, lintegral_const, ENNReal.rpow_two] at H
  calc (∫⁻ x, h x ∂μ) ^ 2 ≤ ((μ Set.univ) ^ (1 / 2 : ℝ) * (∫⁻ x, h x ^ 2 ∂μ) ^ (1 / 2 : ℝ)) ^ 2 := by
        refine pow_le_pow_left' ?_ 2
        simpa using H
    _ = _ := by rw [mul_pow, eqrem_sq_rpow_half, eqrem_sq_rpow_half]

/-- Weighted Cauchy-Schwarz. -/
theorem eqrem_cs_w {α : Type*} [MeasurableSpace α] (ν : Measure α) (w h : α → ℝ≥0∞)
    (hw : Measurable w) (hh : Measurable h) :
    (∫⁻ x, w x * h x ∂ν) ^ 2 ≤ (∫⁻ x, w x ∂ν) * ∫⁻ x, w x * h x ^ 2 ∂ν := by
  have e1 := lintegral_withDensity_eq_lintegral_mul ν hw hh
  have e2 := lintegral_withDensity_eq_lintegral_mul ν hw (hh.pow_const 2)
  have e3 : (ν.withDensity w) Set.univ = ∫⁻ x, w x ∂ν := by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have := eqrem_cs (ν.withDensity w) h hh.aemeasurable
  rw [e1, e2, e3] at this
  simpa using this

/-- A single coordinate is controlled by the `E_M`-energy. -/
theorem eqrem_abs_le_of_energy_le {M : ℝ} (c : NonzeroLattice d → ℝ) {g : ℝ≥0∞}
    (hc : coordEnergy M c ≤ g ^ 2) (k : NonzeroLattice d) :
    ENNReal.ofReal |c k| ≤ ENNReal.ofReal (Lattice.jp k.1 ^ M) * g := by
  have hjp : 0 < Lattice.jp k.1 := Torus.jp_pos _
  set y : ℝ := Lattice.jp k.1 ^ (-M) * |c k| with hy
  have hy0 : 0 ≤ y := mul_nonneg (Real.rpow_nonneg hjp.le _) (abs_nonneg _)
  have hy2 : y ^ 2 = Lattice.jp k.1 ^ (-2 * M) * c k ^ 2 := by
    rw [hy, mul_pow, sq_abs, ← Real.rpow_natCast (Lattice.jp k.1 ^ (-M)) 2, ← Real.rpow_mul hjp.le]
    have e : -M * ((2 : ℕ) : ℝ) = -2 * M := by push_cast; ring
    rw [e]
  have h1 : ENNReal.ofReal y ^ 2 ≤ g ^ 2 := by
    rw [← ENNReal.ofReal_pow hy0, hy2]
    refine le_trans ?_ hc
    unfold coordEnergy
    exact ENNReal.le_tsum (f := fun k : NonzeroLattice d => ENNReal.ofReal (Lattice.jp k.1 ^ (-2 * M) * c k ^ 2)) k
  have h2 : ENNReal.ofReal y ≤ g := eqrem_ennreal_le_of_sq_le h1
  have h3 : |c k| = Lattice.jp k.1 ^ M * y := by
    rw [hy, ← mul_assoc, ← Real.rpow_add hjp]; simp
  rw [h3, ENNReal.ofReal_mul (Real.rpow_nonneg hjp.le _)]
  exact mul_le_mul' le_rfl h2

end HRS.MD.EQRem

end
