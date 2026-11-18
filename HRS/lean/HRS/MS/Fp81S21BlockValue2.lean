import HRS.MS.Fp81S21BlockValue

/-!
# S2.1(iii), packet 15d-4: block value norm estimate

The estimate first uses the generic unit-clock variation bound and then
translates the localized trace integral to physical time.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3
noncomputable section

open MeasureTheory Set Classical
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.Uniform HRS.Uniform.Q45 HRS.MS.CovMeas

private lemma fp81s21_projectiveTensor_norm_coe
    {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (τ : projTensor B 2) :
    ‖τ‖ = ‖(τ : TensorDual B 2)‖ := Submodule.coe_norm _

/-- The trace integral of the localized unit-clock density is exactly its
physical-time integral over the requested block and measurable set. -/
lemma fp81s21_blockValue_traceIntegral_eq
    {d : ℕ} {C : WholeCoeff d} {m H a : ℝ} {r : ℕ} {P : ℝ}
    {z : ℝ → (Euc d → ℝ) → ℝ} {Cmix cdec : ℝ}
    (D : fp81s21_WindowLocalInput C m H a r P z Cmix cdec)
    {I : Set ℝ} (hI : MeasurableSet I) (k : ℕ) :
    (∫⁻ s in Icc (0 : ℝ) 1,
      ENNReal.ofReal (traceNormForm
        (fp81s21_windowLocalD I k C m H a z D.fp81s21_ha
          (le_of_lt D.fp81s21_hH) s))) =
      ∫⁻ v in fp81s21_windowLocalBlock a H k ∩ I,
        ENNReal.ofReal (traceNormForm
          (fp81s21_windowDm C m H a z D.fp81s21_ha
            (le_of_lt D.fp81s21_hH) v)) := by
  let S : Set ℝ := I ∩ Icc (0 : ℝ) (a + H)
  let F : ℝ → ℝ≥0∞ := fun v => ENNReal.ofReal (traceNormForm
    (fp81s21_windowDm C m H a z D.fp81s21_ha
      (le_of_lt D.fp81s21_hH) v))
  have hS : MeasurableSet S := hI.inter measurableSet_Icc
  have hpoint : ∀ s ∈ Icc (0 : ℝ) 1,
      ENNReal.ofReal (traceNormForm
        (fp81s21_windowLocalD I k C m H a z D.fp81s21_ha
          (le_of_lt D.fp81s21_hH) s)) = S.indicator F ((k : ℝ) + s) := by
    intro s hs
    by_cases hloc : (k : ℝ) + s ∈ S
    · simp [fp81s21_windowLocalD, S, F, hs, hloc]
    · simp [fp81s21_windowLocalD, S, F, hs, hloc, traceNormForm_zero_eq]
  calc
    (∫⁻ s in Icc (0 : ℝ) 1,
      ENNReal.ofReal (traceNormForm
        (fp81s21_windowLocalD I k C m H a z D.fp81s21_ha
          (le_of_lt D.fp81s21_hH) s))) =
      ∫⁻ s in Icc (0 : ℝ) 1, S.indicator F ((k : ℝ) + s) := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
        exact hpoint s hs
    _ = ∫⁻ v in Icc (k : ℝ) ((k : ℝ) + 1) ∩ S, F v :=
      fp81s21_windowLocal_lintegral_shift F S hS k
    _ = ∫⁻ v in fp81s21_windowLocalBlock a H k ∩ I, F v := by
      congr 1
      ext v
      simp [fp81s21_windowLocalBlock, S, Set.inter_left_comm,
        Set.inter_comm]

private lemma fp81s21_blockValue_coe
    {d : ℕ} {C : WholeCoeff d} {m H a : ℝ} {r : ℕ} {P : ℝ}
    {z : ℝ → (Euc d → ℝ) → ℝ} {Cmix cdec : ℝ}
    (D : fp81s21_WindowLocalInput C m H a r P z Cmix cdec)
    (I : Set ℝ) (k : ℕ) :
    ((fp81s21_blockValue D I k : projTensor (OscPath d m H) 2) :
      TensorDual (OscPath d m H) 2) =
      fp81s21_blockPsi
        (fp81s21_blockRecon (le_of_lt D.fp81s21_hH) a k)
        (fp81s21_blockCovariance (KSpace d m H)
          (fun s => fp81s21_windowLocalD I k C m H a z D.fp81s21_ha
            (le_of_lt D.fp81s21_hH) s) (Icc (0 : ℝ) 1)) := rfl

theorem fp81s21_blockValue_norm_le
    {d : ℕ} {C : WholeCoeff d} {m H a : ℝ} {r : ℕ} {P : ℝ}
    {z : ℝ → (Euc d → ℝ) → ℝ} {Cmix cdec : ℝ}
    (D : fp81s21_WindowLocalInput C m H a r P z Cmix cdec)
    {I : Set ℝ} (hI : MeasurableSet I) (k : ℕ) :
    ‖fp81s21_blockValue D I k‖ₑ ≤
      ENNReal.ofReal ((3 + Real.sqrt H) ^ 2 * fp81s21_blockC0) *
        (∫⁻ v in fp81s21_windowLocalBlock a H k ∩ I,
          ENNReal.ofReal (traceNormForm
            (fp81s21_windowDm C m H a z D.fp81s21_ha
              (le_of_lt D.fp81s21_hH) v))) := by
  let Q := fp81s21_blockCovariance (KSpace d m H)
  let Dloc : ℝ → KSpace d m H →L[ℝ] KSpace d m H →L[ℝ] ℝ := fun s =>
    fp81s21_windowLocalD I k C m H a z D.fp81s21_ha
      (le_of_lt D.fp81s21_hH) s
  let Rc : PathSp 1 (KSpace d m H) →L[ℝ] OscPath d m H :=
    fp81s21_blockRecon (le_of_lt D.fp81s21_hH) a k
  have hDloc : IsTraceDensityL1 1 Dloc :=
    fp81s21_windowLocal_isTraceDensityL1 D hI k
  have hprops := fp81s21_blockCovariance_props (KSpace d m H)
  have hQnorm : ‖Q Dloc (Icc (0 : ℝ) 1)‖ₑ ≤
      (Q Dloc).variation (Icc (0 : ℝ) 1) :=
    VectorMeasure.enorm_measure_le_variation _ _
  have hvar := hprops.tv Dloc hDloc
  have hmap := fp81s21_blockPsi_norm_le Rc (3 + Real.sqrt H)
    (fp81s21_blockRecon_norm_le (le_of_lt D.fp81s21_hH) a k)
    (Q Dloc (Icc (0 : ℝ) 1))
  have hreal : ‖fp81s21_blockValue D I k‖ ≤
      (3 + Real.sqrt H) ^ 2 * ‖Q Dloc (Icc (0 : ℝ) 1)‖ := by
    calc
      ‖fp81s21_blockValue D I k‖ =
          ‖((fp81s21_blockValue D I k : projTensor (OscPath d m H) 2) :
            TensorDual (OscPath d m H) 2)‖ :=
        fp81s21_projectiveTensor_norm_coe _
      _ = ‖fp81s21_blockPsi Rc (Q Dloc (Icc (0 : ℝ) 1))‖ := by
        rw [fp81s21_blockValue_coe]
      _ ≤ _ := by simpa [Q, Dloc, Rc] using hmap
  calc
    ‖fp81s21_blockValue D I k‖ₑ =
        ENNReal.ofReal ‖fp81s21_blockValue D I k‖ := by
      rw [← ofReal_norm_eq_enorm]
    _ ≤ ENNReal.ofReal ((3 + Real.sqrt H) ^ 2 *
          ‖Q Dloc (Icc (0 : ℝ) 1)‖) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal ((3 + Real.sqrt H) ^ 2) *
          ‖Q Dloc (Icc (0 : ℝ) 1)‖ₑ := by
      rw [ENNReal.ofReal_mul (sq_nonneg (3 + Real.sqrt H)), ofReal_norm_eq_enorm]
    _ ≤ ENNReal.ofReal ((3 + Real.sqrt H) ^ 2) *
          (Q Dloc).variation (Icc (0 : ℝ) 1) :=
      mul_le_mul' le_rfl hQnorm
    _ ≤ ENNReal.ofReal ((3 + Real.sqrt H) ^ 2) *
          (ENNReal.ofReal (fp81s21_blockC0) *
            (∫⁻ s in Icc (0 : ℝ) 1,
              ENNReal.ofReal (traceNormForm (Dloc s)))) :=
      mul_le_mul' le_rfl hvar
    _ = ENNReal.ofReal ((3 + Real.sqrt H) ^ 2 * fp81s21_blockC0) *
          (∫⁻ s in Icc (0 : ℝ) 1,
            ENNReal.ofReal (traceNormForm (Dloc s))) := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (sq_nonneg (3 + Real.sqrt H))]
    _ = ENNReal.ofReal ((3 + Real.sqrt H) ^ 2 * fp81s21_blockC0) *
          (∫⁻ v in fp81s21_windowLocalBlock a H k ∩ I,
            ENNReal.ofReal (traceNormForm
              (fp81s21_windowDm C m H a z D.fp81s21_ha
                (le_of_lt D.fp81s21_hH) v))) := by
      rw [fp81s21_blockValue_traceIntegral_eq D hI k]

#print axioms fp81s21_blockValue_traceIntegral_eq
#print axioms fp81s21_blockValue_norm_le

end HRS.Fp81.S21

end
