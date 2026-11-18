import HRS.MS.S21E_Kappa

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

private theorem fp81s21_norm_sq_memLp
    {B Ω : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
    [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]
    [MeasurableSpace Ω] {P : Measure Ω} {Z : Ω → B}
    (hZ : MemLp Z 3 P) :
    MemLp (fun ω => ‖Z ω‖ ^ (2 : ℝ)) (ENNReal.ofReal (3 / 2)) P := by
  have h := hZ.norm_rpow_div (ENNReal.ofReal 2)
  convert h using 1
  · norm_num
  · rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num

private theorem fp81s21_mixed_DZZ_holder
    {B Ω : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
    [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]
    [MeasurableSpace Ω] {P : Measure Ω} {D Z : Ω → B}
    (hD : MemLp D 3 P) (hZ : MemLp Z 3 P) :
    Integrable (fun ω => ‖D ω‖ * ‖Z ω‖ * ‖Z ω‖) P ∧
      (∫ ω, ‖D ω‖ * ‖Z ω‖ * ‖Z ω‖ ∂P) ≤
        (∫ ω, ‖D ω‖ ^ 3 ∂P) ^ (1 / 3 : ℝ) *
          (∫ ω, ‖Z ω‖ ^ 3 ∂P) ^ (2 / 3 : ℝ) := by
  have hDnorm : MemLp (fun ω => ‖D ω‖) (ENNReal.ofReal 3) P := by
    simpa using hD.norm
  have hZsq : MemLp (fun ω => ‖Z ω‖ ^ (2 : ℝ)) (ENNReal.ofReal (3 / 2)) P :=
    fp81s21_norm_sq_memLp hZ
  have hconj : (3 : ℝ).HolderConjugate (3 / 2) := by
    rw [Real.holderConjugate_iff]
    constructor <;> norm_num
  letI : ENNReal.HolderConjugate (ENNReal.ofReal 3) (ENNReal.ofReal (3 / 2)) :=
    hconj.ennrealOfReal
  have hprod : Integrable (fun ω => ‖D ω‖ * (‖Z ω‖ ^ (2 : ℝ))) P :=
    hDnorm.integrable_mul hZsq
  have hi : Integrable (fun ω => ‖D ω‖ * ‖Z ω‖ * ‖Z ω‖) P := by
    apply hprod.congr
    filter_upwards [] with ω
    simp only [Real.rpow_two, pow_two]
    ring
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := P) (p := 3) (q := 3 / 2)
    hconj
    (ae_of_all _ fun ω => norm_nonneg (D ω))
    (ae_of_all _ fun ω => Real.rpow_nonneg (norm_nonneg (Z ω)) _)
    hDnorm hZsq
  have hpow :
      (∫ ω, (‖Z ω‖ ^ (2 : ℝ)) ^ (3 / 2 : ℝ) ∂P) =
        ∫ ω, ‖Z ω‖ ^ 3 ∂P := by
    apply integral_congr_ae
    filter_upwards [] with ω
    rw [← Real.rpow_mul (norm_nonneg (Z ω))]
    norm_num
  refine ⟨hi, ?_⟩
  calc
    (∫ ω, ‖D ω‖ * ‖Z ω‖ * ‖Z ω‖ ∂P) =
        ∫ ω, ‖D ω‖ * (‖Z ω‖ ^ (2 : ℝ)) ∂P := by
      apply integral_congr_ae
      filter_upwards [] with ω
      simp only [Real.rpow_two, pow_two]
      ring
    _ ≤ (∫ ω, ‖D ω‖ ^ 3 ∂P) ^ (1 / 3 : ℝ) *
          (∫ ω, (‖Z ω‖ ^ (2 : ℝ)) ^ (3 / 2 : ℝ) ∂P) ^ (1 / (3 / 2) : ℝ) := hholder
    _ = (∫ ω, ‖D ω‖ ^ 3 ∂P) ^ (1 / 3 : ℝ) *
          (∫ ω, ‖Z ω‖ ^ 3 ∂P) ^ (2 / 3 : ℝ) := by rw [hpow]; congr 1 <;> norm_num

set_option maxHeartbeats 400000 in
private theorem fp81s21_mixed_JZ_holder
    {B Ω : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
    [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]
    [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {J : Ω → TensorDual B 2} {Z : Ω → B}
    (hJ : MemLp J 2 P) (hZ : MemLp Z 3 P) :
    Integrable (fun ω => ‖J ω‖ * ‖Z ω‖) P ∧
      (∫ ω, ‖J ω‖ * ‖Z ω‖ ∂P) ≤
        Real.sqrt (∫ ω, ‖J ω‖ ^ 2 ∂P) * Real.sqrt (∫ ω, ‖Z ω‖ ^ 2 ∂P) := by
  letI hJSpace : NormedAddCommGroup (TensorDual B 2) := inferInstance
  letI : Norm (TensorDual B 2) := hJSpace.toNorm
  have hJnorm0 : MemLp (fun ω => ‖J ω‖) 2 P := hJ.norm
  have hJnorm : MemLp (fun ω => ‖J ω‖) (ENNReal.ofReal 2) P := by
    simpa using hJnorm0
  have hZ2 : MemLp Z 2 P := hZ.mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 3)
  have hZnorm0 : MemLp (fun ω => ‖Z ω‖) 2 P := hZ2.norm
  have hZnorm : MemLp (fun ω => ‖Z ω‖) (ENNReal.ofReal 2) P := by
    simpa using hZnorm0
  have hconj : (2 : ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two
  letI : ENNReal.HolderConjugate (ENNReal.ofReal 2) (ENNReal.ofReal 2) :=
    hconj.ennrealOfReal
  have hi : Integrable (fun ω => ‖J ω‖ * ‖Z ω‖) P := hJnorm.integrable_mul hZnorm
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := P) (p := 2) (q := 2)
    hconj
    (ae_of_all _ fun ω => norm_nonneg (J ω))
    (ae_of_all _ fun ω => norm_nonneg (Z ω))
    hJnorm hZnorm
  refine ⟨hi, ?_⟩
  simpa [Real.sqrt_eq_rpow, Real.rpow_two] using hholder

/-- Mixed-moment bound for the cubic tensor correction in `s21eKappa`. -/
theorem fp81s21_kappa_bound_of_moments
    {B Ω : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
    [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]
    [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (κ0 : TensorDual B 3) (D Z : Ω → B)
    (J : Ω → TensorDual B 2)
    (hD : MemLp D 3 P) (hZ : MemLp Z 3 P)
    (hJ : MemLp J 2 P) :
    Integrable (fun ω => ‖D ω‖ * ‖Z ω‖ * ‖Z ω‖) P ∧
    Integrable (fun ω => ‖J ω‖ * ‖Z ω‖) P ∧
    ‖HRS.MS.S21E.s21eKappa P κ0 D Z J‖ ≤
      ‖κ0‖ +
      3 * (∫ ω, ‖D ω‖ ^ 3 ∂P) ^ (1 / 3 : ℝ) *
          (∫ ω, ‖Z ω‖ ^ 3 ∂P) ^ (2 / 3 : ℝ) +
      3 * Real.sqrt (∫ ω, ‖J ω‖ ^ 2 ∂P) *
          Real.sqrt (∫ ω, ‖Z ω‖ ^ 2 ∂P) := by
  have hDZZ := fp81s21_mixed_DZZ_holder hD hZ
  have hJZ := fp81s21_mixed_JZ_holder hJ hZ
  have hi3 := hDZZ.1
  have hi21 := hJZ.1
  have hkappa := HRS.MS.S21E.s21e_kappa_norm_le P
    (κ₀ := κ0) (D := D) (Z := Z) (J := J)
    hD.aestronglyMeasurable hZ.aestronglyMeasurable hJ.aestronglyMeasurable hi3 hi21
  have hDscaled := mul_le_mul_of_nonneg_left hDZZ.2 (by norm_num : (0 : ℝ) ≤ 3)
  have hJscaled := mul_le_mul_of_nonneg_left hJZ.2 (by norm_num : (0 : ℝ) ≤ 3)
  refine ⟨hi3, hi21, ?_⟩
  calc
    ‖HRS.MS.S21E.s21eKappa P κ0 D Z J‖ ≤
        ‖κ0‖ + 3 * (∫ ω, ‖D ω‖ * ‖Z ω‖ * ‖Z ω‖ ∂P) +
          3 * (∫ ω, ‖J ω‖ * ‖Z ω‖ ∂P) := hkappa
    _ ≤ ‖κ0‖ +
        3 * ((∫ ω, ‖D ω‖ ^ 3 ∂P) ^ (1 / 3 : ℝ) *
          (∫ ω, ‖Z ω‖ ^ 3 ∂P) ^ (2 / 3 : ℝ)) +
        3 * (Real.sqrt (∫ ω, ‖J ω‖ ^ 2 ∂P) *
          Real.sqrt (∫ ω, ‖Z ω‖ ^ 2 ∂P)) := by
      calc
        ‖κ0‖ + 3 * (∫ ω, ‖D ω‖ * ‖Z ω‖ * ‖Z ω‖ ∂P) +
            3 * (∫ ω, ‖J ω‖ * ‖Z ω‖ ∂P) =
          (3 * (∫ ω, ‖D ω‖ * ‖Z ω‖ * ‖Z ω‖ ∂P) +
            3 * (∫ ω, ‖J ω‖ * ‖Z ω‖ ∂P)) + ‖κ0‖ := by ring
        _ ≤ (3 * ((∫ ω, ‖D ω‖ ^ 3 ∂P) ^ (1 / 3 : ℝ) *
            (∫ ω, ‖Z ω‖ ^ 3 ∂P) ^ (2 / 3 : ℝ)) +
            3 * (Real.sqrt (∫ ω, ‖J ω‖ ^ 2 ∂P) *
              Real.sqrt (∫ ω, ‖Z ω‖ ^ 2 ∂P))) + ‖κ0‖ := by
          exact add_le_add_left (add_le_add hDscaled hJscaled) _
        _ = ‖κ0‖ +
            3 * ((∫ ω, ‖D ω‖ ^ 3 ∂P) ^ (1 / 3 : ℝ) *
              (∫ ω, ‖Z ω‖ ^ 3 ∂P) ^ (2 / 3 : ℝ)) +
            3 * (Real.sqrt (∫ ω, ‖J ω‖ ^ 2 ∂P) *
              Real.sqrt (∫ ω, ‖Z ω‖ ^ 2 ∂P)) := by ring
    _ = ‖κ0‖ +
        3 * (∫ ω, ‖D ω‖ ^ 3 ∂P) ^ (1 / 3 : ℝ) *
          (∫ ω, ‖Z ω‖ ^ 3 ∂P) ^ (2 / 3 : ℝ) +
        3 * Real.sqrt (∫ ω, ‖J ω‖ ^ 2 ∂P) *
          Real.sqrt (∫ ω, ‖Z ω‖ ^ 2 ∂P) := by ring

end HRS.Fp81.S21

#print axioms HRS.Fp81.S21.fp81s21_kappa_bound_of_moments
