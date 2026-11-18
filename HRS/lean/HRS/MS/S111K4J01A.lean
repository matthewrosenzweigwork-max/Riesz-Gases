import HRS.MS.S111K4J01D

/-!
# S11.1 / J01 pieces (S11K4): weighted coefficient fields and a.e. descent of the random interval maps

Piece 1: linearity of the coefficient field on weighted tests (`E.add`, `E.smul`).
Piece 2: for product-measurable `ℓ²`-valued fields, every time-slice is `L¹` on `[0,H]` for a.e. `ω`,
so the time-coefficient path respects subtraction a.e.; the random drift and covariance of any
`IntervalOperators` then respect coupled differences a.e. (the last clause of Pro `S111.J02`).
The existence of the operators (`coefficient_interval_operators`, S111.J01) is NOT here.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111K4J01

open HRS HRS.Whole

theorem k4j_coefField_add {d r : ℕ} {Pw : ℝ} (E : WeightedChart d r Pw) (q : ℝ → Coeff) (v : ℝ)
    {f g : Euc d → ℝ} (hf : IsR2WeightedTest r Pw f) (hg : IsR2WeightedTest r Pw g) :
    coefficientField E q v (f + g) = coefficientField E q v f + coefficientField E q v g := by
  unfold coefficientField
  rw [E.add f g hf hg, inner_add_right]

theorem k4j_coefField_smul {d r : ℕ} {Pw : ℝ} (E : WeightedChart d r Pw) (q : ℝ → Coeff) (v a : ℝ)
    {f : Euc d → ℝ} (hf : IsR2WeightedTest r Pw f) :
    coefficientField E q v (a • f) = a * coefficientField E q v f := by
  unfold coefficientField
  rw [E.smul a f hf, inner_smul_right]

/-- For a.e. `ω`, the time slice of an `L²` product field is `L¹` on `[0,H]`. -/
theorem k4j_slice_memLp1 {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {H : ℝ} {q : ℝ × Omega → Coeff}
    (hq : MemLp q 2 ((volume.restrict (Set.Icc (0 : ℝ) H)).prod P)) :
    ∀ᵐ w ∂P, MemLp (fun v => q (v, w)) 1 (volume.restrict (Set.Icc (0 : ℝ) H)) := by
  have hI : Integrable (fun p => ‖q p‖ ^ 2) ((volume.restrict (Set.Icc (0 : ℝ) H)).prod P) :=
    (memLp_two_iff_integrable_sq_norm hq.aestronglyMeasurable).1 hq
  filter_upwards [hI.prod_left_ae, hq.aestronglyMeasurable.prodMk_right] with w hw hm
  have h2 : MemLp (fun v => q (v, w)) 2 (volume.restrict (Set.Icc (0 : ℝ) H)) :=
    (memLp_two_iff_integrable_sq_norm hm).2 hw
  exact h2.mono_exponent (by norm_num)

/-- The time-coefficient path respects subtraction for a.e. `ω`. -/
theorem k4j_timeCoeffOf_sub {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {H : ℝ} {q q' : ℝ × Omega → Coeff}
    (hq : MemLp q 2 ((volume.restrict (Set.Icc (0 : ℝ) H)).prod P))
    (hq' : MemLp q' 2 ((volume.restrict (Set.Icc (0 : ℝ) H)).prod P)) :
    ∀ᵐ w ∂P, timeCoeffOf H (q - q') w = timeCoeffOf H q w - timeCoeffOf H q' w := by
  filter_upwards [k4j_slice_memLp1 hq, k4j_slice_memLp1 hq'] with w h1 h2
  have h12 : MemLp (fun v => (q - q') (v, w)) 1 (volume.restrict (Set.Icc (0 : ℝ) H)) := h1.sub h2
  unfold timeCoeffOf
  rw [dif_pos h12, dif_pos h1, dif_pos h2]
  exact MemLp.toLp_sub h1 h2

/-- Random drift and covariance of any interval operators respect coupled differences, a.e. `ω`,
for all `v` simultaneously (Pro `S111.J02`, last clause). -/
theorem k4j_random_sub {d r : ℕ} {Pw : ℝ} {E : WeightedChart d r Pw} {C : WholeCoeff d}
    {T u c0 B : ℝ} (O : IntervalOperators E C T u c0 B) {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} [IsProbabilityMeasure P] (q q' : ℝ × Omega → Coeff)
    (hq : MemLp q 2 ((volume.restrict (Set.Icc (0 : ℝ) (u + T))).prod P))
    (hq' : MemLp q' 2 ((volume.restrict (Set.Icc (0 : ℝ) (u + T))).prod P)) :
    ∀ᵐ w ∂P, ∀ v : ℝ,
      randomDrift O (q - q') v w = randomDrift O q v w - randomDrift O q' v w ∧
      randomCovariance O (q - q') v w = randomCovariance O q v w - randomCovariance O q' v w := by
  filter_upwards [k4j_timeCoeffOf_sub (H := u + T) hq hq'] with w hw
  intro v
  constructor
  · unfold randomDrift
    rw [hw, map_sub]
  · unfold randomCovariance
    rw [hw, map_sub]

end HRS.MS.S111K4J01
