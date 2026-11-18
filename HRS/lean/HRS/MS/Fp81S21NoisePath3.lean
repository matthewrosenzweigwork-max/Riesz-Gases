import HRS.MS.Fp81S21NoisePath2

/-! A sixth-moment reconstruction estimate with the BDG constant chosen uniformly in time. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.U9

/-- The BDG constant does not depend on the horizon or on the martingale. -/
theorem fp81s21_noisePath_uniform_bdg :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m T : ℝ), 0 ≤ T → ∀ (d : ℕ)
      {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (ℱ : Filtration ℝ mΩ) (M : ℝ → Ω → KSpace d m T)
      (Sg : ℝ → Ω → (KSpace d m T →L[ℝ] KSpace d m T →L[ℝ] ℝ)),
      IsHilbertMartingaleWithCovariation P ℱ T M Sg → ∀ K : ℝ, 0 ≤ K →
      (∀ᵐ ζ ∂P, ∫ r in Icc (0 : ℝ) T, traceNormForm (Sg r ζ) ≤ K) →
      ∫⁻ ζ, (⨆ t : Icc (0 : ℝ) T, ENNReal.ofReal ‖reconstructPath m T M ζ t‖) ^ 6 ∂P ≤
        ENNReal.ofReal ((3 + Real.sqrt T) ^ 6 * C * K ^ 3) := by
  obtain ⟨C, hC, hbdg⟩ := HRS.HilbertBDG.hilbert_bdg 6 (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro m T hT d Ω mΩ P hP ℱ M Sg hM K hK hbd
  have hmax := fp81s21_u9_bound_six (d := d) (m := m) (ℱ := ℱ) hT C
    (hbdg Ω P ℱ (KSpace d m T) T M Sg hM)
  have hlin : ∀ᵐ ζ ∂P, (∫⁻ r in Icc (0 : ℝ) T,
      ENNReal.ofReal (traceNormForm (Sg r ζ))) ^ (3 : ℕ) ≤ ENNReal.ofReal (K ^ 3) := by
    filter_upwards [hM.sigma_pathint, hbd] with ζ hζ hζK
    have hJ : 0 ≤ ∫ r in Icc (0 : ℝ) T, traceNormForm (Sg r ζ) :=
      integral_nonneg fun r => u9_traceNormForm_nonneg (Sg r ζ)
    have he : ∫⁻ r in Icc (0 : ℝ) T, ENNReal.ofReal (traceNormForm (Sg r ζ)) =
        ENNReal.ofReal (∫ r in Icc (0 : ℝ) T, traceNormForm (Sg r ζ)) :=
      (ofReal_integral_eq_lintegral_ofReal hζ
        (Filter.Eventually.of_forall fun r => u9_traceNormForm_nonneg (Sg r ζ))).symm
    rw [he, ← ENNReal.ofReal_pow hJ]
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hJ hζK 3)
  have hmono : ∫⁻ ζ, (∫⁻ r in Icc (0 : ℝ) T,
      ENNReal.ofReal (traceNormForm (Sg r ζ))) ^ (3 : ℕ) ∂P ≤ ENNReal.ofReal (K ^ 3) := by
    calc
      _ ≤ ∫⁻ _ζ, ENNReal.ofReal (K ^ 3) ∂P := lintegral_mono_ae hlin
      _ = _ := by rw [lintegral_const, measure_univ, mul_one]
  have h3 : 0 ≤ 3 + Real.sqrt T := by positivity
  have h6 : 0 ≤ (3 + Real.sqrt T) ^ 6 := by positivity
  have hsplit : ENNReal.ofReal ((3 + Real.sqrt T) ^ 6 * C * K ^ 3) =
      ENNReal.ofReal (3 + Real.sqrt T) ^ 6 *
        (ENNReal.ofReal C * ENNReal.ofReal (K ^ 3)) := by
    rw [ENNReal.ofReal_mul (mul_nonneg h6 hC), ENNReal.ofReal_mul h6,
      ENNReal.ofReal_pow h3, mul_assoc]
  rw [hsplit]
  exact hmax.trans (mul_le_mul' le_rfl (mul_le_mul' le_rfl hmono))

#print axioms HRS.Fp81.S21.fp81s21_noisePath_uniform_bdg
end HRS.Fp81.S21
