import HRS.MS.R26T6CD03

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace HRS.Fp81.S21

/-- Finite-measure exponent comparison, specialized to `L²` into `L¹`. -/
theorem fp81s21_l2ToL1_memLp {α : Type*} [MeasurableSpace α]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure α} [IsFiniteMeasure μ] (f : Lp E 2 μ) : MemLp f 1 μ := by
  have hf : MemLp f (2 : ℝ≥0∞) μ := Lp.memLp f
  exact hf.mono_exponent (p := (1 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)) (by norm_num)

/-- The Cauchy--Schwarz estimate for a representative in `L²` on a finite measure space. -/
theorem fp81s21_l2ToL1_toLp_bound {α : Type*} [MeasurableSpace α]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure α} [IsFiniteMeasure μ] (f : Lp E 2 μ) :
    ‖(fp81s21_l2ToL1_memLp f).toLp f‖ ≤
      Real.sqrt ((μ Set.univ).toReal) * ‖f‖ := by
  have hcmp : eLpNorm f (1 : ℝ≥0∞) μ ≤
      eLpNorm f (2 : ℝ≥0∞) μ * μ Set.univ ^ (1 / 2 : ℝ) := by
    convert (eLpNorm_le_eLpNorm_mul_rpow_measure_univ
      (p := (1 : ℝ≥0∞)) (q := (2 : ℝ≥0∞))
      (by norm_num) (Lp.aestronglyMeasurable f)) using 1 <;> norm_num
  have hfac : μ Set.univ ^ (1 / 2 : ℝ) < ∞ :=
    ENNReal.rpow_lt_top_of_nonneg (by norm_num) (measure_lt_top μ Set.univ).ne
  have hprod : eLpNorm f (2 : ℝ≥0∞) μ * μ Set.univ ^ (1 / 2 : ℝ) ≠ ∞ :=
    ENNReal.mul_ne_top (Lp.eLpNorm_ne_top f) hfac.ne
  calc
    ‖(fp81s21_l2ToL1_memLp f).toLp f‖ =
        (eLpNorm f (1 : ℝ≥0∞) μ).toReal := by simp
    _ ≤ (eLpNorm f (2 : ℝ≥0∞) μ * μ Set.univ ^ (1 / 2 : ℝ)).toReal :=
      ENNReal.toReal_mono hprod hcmp
    _ = ‖f‖ * Real.sqrt ((μ Set.univ).toReal) := by
      rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, Lp.norm_def,
        ← Real.sqrt_eq_rpow]
    _ = Real.sqrt ((μ Set.univ).toReal) * ‖f‖ := by rw [mul_comm]

/-- The canonical inclusion from `L²` to `L¹` on a finite measure space. -/
noncomputable def fp81s21_l2ToL1 {α : Type*} [MeasurableSpace α]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure α) [IsFiniteMeasure μ] :
    Lp E 2 μ →L[ℝ] Lp E 1 μ := by
  let lin : Lp E 2 μ →ₗ[ℝ] Lp E 1 μ := {
    toFun := fun (f : Lp E 2 μ) => ⟨(f : α →ₘ[μ] E), by
      rw [Lp.mem_Lp_iff_memLp]
      exact fp81s21_l2ToL1_memLp f⟩
    map_add' := by intro f g; rfl
    map_smul' := by intro c f; rfl
  }
  exact lin.mkContinuous (Real.sqrt ((μ Set.univ).toReal)) (by
    intro f
    have heq : lin f = (fp81s21_l2ToL1_memLp f).toLp f := by
      apply Lp.ext
      exact (MemLp.coeFn_toLp (fp81s21_l2ToL1_memLp f)).symm
    simpa [heq] using (fp81s21_l2ToL1_toLp_bound f))

private theorem fp81s21_l2ToL1_eq_toLp {α : Type*} [MeasurableSpace α]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure α) [IsFiniteMeasure μ] (f : Lp E 2 μ) :
    fp81s21_l2ToL1 E μ f = (fp81s21_l2ToL1_memLp f).toLp f := by
  unfold fp81s21_l2ToL1
  dsimp
  apply Lp.ext
  exact (MemLp.coeFn_toLp (fp81s21_l2ToL1_memLp f)).symm

/-- The finite-measure inclusion has norm at most the square root of the measure. -/
theorem fp81s21_l2ToL1_norm_le {α : Type*} [MeasurableSpace α]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure α) [IsFiniteMeasure μ] :
    ‖fp81s21_l2ToL1 E μ‖ ≤ Real.sqrt ((μ Set.univ).toReal) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) ?_
  intro f
  rw [fp81s21_l2ToL1_eq_toLp]
  exact fp81s21_l2ToL1_toLp_bound f

/-- The inclusion is represented by the same function almost everywhere. -/
theorem fp81s21_l2ToL1_ae {α : Type*} [MeasurableSpace α]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure α) [IsFiniteMeasure μ] (f : Lp E 2 μ) :
    fp81s21_l2ToL1 E μ f =ᵐ[μ] f := by
  rw [fp81s21_l2ToL1_eq_toLp]
  exact MemLp.coeFn_toLp (fp81s21_l2ToL1_memLp f)

/-- The time-history inclusion from square-integrable coefficients to the staged
`r26t6_TimeCoeff` space. -/
noncomputable def fp81s21_timeL2L1 (H : ℝ) (hH : 0 ≤ H) :
    Lp HRS.MS.R26T6.r26t6_Coeff 2 (volume.restrict (Icc (0 : ℝ) H)) →L[ℝ]
      HRS.MS.R26T6.r26t6_TimeCoeff H :=
  fp81s21_l2ToL1 HRS.MS.R26T6.r26t6_Coeff (volume.restrict (Icc (0 : ℝ) H))

/-- The time-history inclusion obeys the sharp finite-interval bound `sqrt H`. -/
theorem fp81s21_timeL2L1_bound (H : ℝ) (hH : 0 ≤ H) :
    ‖fp81s21_timeL2L1 H hH‖ ≤ Real.sqrt H := by
  have hbase := fp81s21_l2ToL1_norm_le HRS.MS.R26T6.r26t6_Coeff
    (volume.restrict (Icc (0 : ℝ) H))
  simpa [fp81s21_timeL2L1, Measure.restrict_apply_univ, Real.volume_Icc,
    ENNReal.toReal_ofReal hH] using hbase

/-- The time-history inclusion preserves representatives almost everywhere. -/
theorem fp81s21_timeL2L1_ae (H : ℝ) (hH : 0 ≤ H)
    (f : Lp HRS.MS.R26T6.r26t6_Coeff 2 (volume.restrict (Icc (0 : ℝ) H))) :
    fp81s21_timeL2L1 H hH f =ᵐ[volume.restrict (Icc (0 : ℝ) H)] f := by
  exact fp81s21_l2ToL1_ae HRS.MS.R26T6.r26t6_Coeff
    (volume.restrict (Icc (0 : ℝ) H)) f

#print axioms fp81s21_l2ToL1_norm_le
#print axioms fp81s21_l2ToL1_memLp
#print axioms fp81s21_l2ToL1_toLp_bound
#print axioms fp81s21_l2ToL1_ae
#print axioms fp81s21_timeL2L1_bound
#print axioms fp81s21_timeL2L1_ae

end HRS.Fp81.S21
