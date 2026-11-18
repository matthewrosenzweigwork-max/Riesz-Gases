import HRS.MS.Fp81S21MixedMoments

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

/-- The individual cubic mixed-moment bound used by the drift part of `κ`. -/
theorem fp81s21_mixed_DZZ_holder_of_moments
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
  have hZsq : MemLp (fun ω => ‖Z ω‖ ^ (2 : ℝ)) (ENNReal.ofReal (3 / 2)) P := by
    have h := hZ.norm_rpow_div (ENNReal.ofReal 2)
    convert h using 1
    · norm_num
    · rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
      norm_num
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

/-- The individual quadratic mixed-moment bound used by the covariance part of `κ`. -/
theorem fp81s21_mixed_JZ_holder_of_moments
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

private theorem fp81s21_probability_moment_three_le_four
    {B Ω : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
    [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Z : Ω → B} (hZ : MemLp Z 4 P) :
    (∫ ω, ‖Z ω‖ ^ 3 ∂P) ≤
      (∫ ω, ‖Z ω‖ ^ 4 ∂P) ^ (3 / 4 : ℝ) := by
  have hpow : MemLp (fun ω => ‖Z ω‖ ^ (3 : ℝ)) (ENNReal.ofReal (4 / 3)) P := by
    have h := hZ.norm_rpow_div (ENNReal.ofReal 3)
    convert h using 1
    · norm_num
    · rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 3)]
      norm_num
  have hconj : (4 / 3 : ℝ).HolderConjugate 4 := by
    rw [Real.holderConjugate_iff]
    constructor <;> norm_num
  letI : ENNReal.HolderConjugate (ENNReal.ofReal (4 / 3)) (ENNReal.ofReal 4) :=
    hconj.ennrealOfReal
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := P) (p := 4 / 3) (q := 4)
    hconj
    (ae_of_all _ fun ω => Real.rpow_nonneg (norm_nonneg (Z ω)) _)
    (ae_of_all _ fun _ => (by norm_num : (0 : ℝ) ≤ 1))
    hpow (memLp_const 1)
  have hleft :
      (∫ ω, ‖Z ω‖ ^ (3 : ℝ) * (1 : ℝ) ∂P) = ∫ ω, ‖Z ω‖ ^ (3 : ℝ) ∂P := by
    simp
  have hpower :
      (∫ ω, (‖Z ω‖ ^ (3 : ℝ)) ^ (4 / 3 : ℝ) ∂P) =
        ∫ ω, ‖Z ω‖ ^ 4 ∂P := by
    apply integral_congr_ae
    filter_upwards [] with ω
    rw [← Real.rpow_mul (norm_nonneg (Z ω))]
    norm_num
  have hconst : (∫ _ω : Ω, (1 : ℝ) ^ (4 : ℝ) ∂P) = 1 := by simp
  rw [hleft, hpower, hconst] at hholder
  convert hholder using 1 <;> norm_num

private theorem fp81s21_probability_moment_two_le_four
    {B Ω : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
    [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Z : Ω → B} (hZ : MemLp Z 4 P) :
    (∫ ω, ‖Z ω‖ ^ 2 ∂P) ≤
      (∫ ω, ‖Z ω‖ ^ 4 ∂P) ^ (1 / 2 : ℝ) := by
  have hpow : MemLp (fun ω => ‖Z ω‖ ^ (2 : ℝ)) (ENNReal.ofReal 2) P := by
    have h := hZ.norm_rpow_div (ENNReal.ofReal 2)
    convert h using 1
    · norm_num
    · rw [show (4 : ℝ≥0∞) = ENNReal.ofReal (4 : ℝ) by norm_num,
        ← ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
      norm_num
  letI : ENNReal.HolderConjugate (ENNReal.ofReal 2) (ENNReal.ofReal 2) :=
    Real.HolderConjugate.two_two.ennrealOfReal
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := P) (p := 2) (q := 2)
    Real.HolderConjugate.two_two
    (ae_of_all _ fun ω => Real.rpow_nonneg (norm_nonneg (Z ω)) _)
    (ae_of_all _ fun _ => (by norm_num : (0 : ℝ) ≤ 1))
    hpow (memLp_const 1)
  have hleft :
      (∫ ω, ‖Z ω‖ ^ (2 : ℝ) * (1 : ℝ) ∂P) = ∫ ω, ‖Z ω‖ ^ (2 : ℝ) ∂P := by
    simp
  have hpower :
      (∫ ω, (‖Z ω‖ ^ (2 : ℝ)) ^ (2 : ℝ) ∂P) =
        ∫ ω, ‖Z ω‖ ^ 4 ∂P := by
    apply integral_congr_ae
    filter_upwards [] with ω
    rw [← Real.rpow_mul (norm_nonneg (Z ω))]
    norm_num
  have hconst : (∫ _ω : Ω, (1 : ℝ) ^ (2 : ℝ) ∂P) = 1 := by simp
  rw [hleft, hpower, hconst] at hholder
  convert hholder using 1 <;> norm_num

/-- Individual integrability and Hölder bounds for the two mixed corrections.
The fourth moment of `Z` supplies the third moment needed by the drift term. -/
theorem fp81s21_gaussian_correction_integral_certificate
    {B Ω : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
    [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (D Z : Ω → B) (J : Ω → TensorDual B 2)
    (hD : MemLp D 3 P) (hZ : MemLp Z 4 P) (hJ : MemLp J 2 P) :
    Integrable (fun ω => ‖D ω‖) P ∧
    Integrable (fun ω => ‖(J ω : TensorDual B 2)‖) P ∧
    Integrable (fun ω => ‖D ω‖ * ‖Z ω‖ * ‖Z ω‖) P ∧
    Integrable (fun ω => ‖J ω‖ * ‖Z ω‖) P ∧
    (∫ ω, ‖D ω‖ * ‖Z ω‖ * ‖Z ω‖ ∂P) ≤
      (∫ ω, ‖D ω‖ ^ 3 ∂P) ^ (1 / 3 : ℝ) *
        (∫ ω, ‖Z ω‖ ^ 3 ∂P) ^ (2 / 3 : ℝ) ∧
    (∫ ω, ‖J ω‖ * ‖Z ω‖ ∂P) ≤
      Real.sqrt (∫ ω, ‖J ω‖ ^ 2 ∂P) * Real.sqrt (∫ ω, ‖Z ω‖ ^ 2 ∂P) := by
  have hZ3 : MemLp Z 3 P := hZ.mono_exponent (by norm_num : (3 : ℝ≥0∞) ≤ 4)
  have hD1 : Integrable (fun ω => ‖D ω‖) P :=
    MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 3) hD.norm
  letI hJSpace : NormedAddCommGroup (TensorDual B 2) := inferInstance
  letI : Norm (TensorDual B 2) := hJSpace.toNorm
  have hJnorm : MemLp (fun ω => ‖(J ω : TensorDual B 2)‖) 2 P := by
    simpa using hJ.norm
  have hJ1 : Integrable (fun ω => ‖(J ω : TensorDual B 2)‖) P :=
    MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2) hJnorm
  have hDmix := fp81s21_mixed_DZZ_holder_of_moments hD hZ3
  have hJmix := fp81s21_mixed_JZ_holder_of_moments hJ hZ3
  exact ⟨hD1, hJ1, hDmix.1, hJmix.1, hDmix.2, hJmix.2⟩

/-- Uniform mixed-moment sum, with its constant fixed before the horizon parameter.
The chosen bound is `MD^(1/3) MZ^(1/2) + MJ^(1/2) MZ^(1/4)`. -/
theorem fp81s21_uniform_gaussian_correction_mixed_moments
    {B Ω : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
    [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D Z : ℝ → Ω → B) (J : ℝ → Ω → TensorDual B 2) :
    ∀ MD MJ MZ : ℝ, 0 ≤ MD → 0 ≤ MJ → 0 ≤ MZ →
      (∀ a : ℝ, 0 ≤ a →
        MemLp (D a) 3 P ∧
        (∫ ω, ‖D a ω‖ ^ 3 ∂P) ≤ MD ∧
        MemLp (J a) 2 P ∧
        (∫ ω, ‖J a ω‖ ^ 2 ∂P) ≤ MJ ∧
        MemLp (Z a) 4 P ∧
        (∫ ω, ‖Z a ω‖ ^ 4 ∂P) ≤ MZ) →
      ∃ Kb : ℝ, 0 ≤ Kb ∧
        ∀ a : ℝ, 0 ≤ a →
          (∫ ω, ‖D a ω‖ * ‖Z a ω‖ * ‖Z a ω‖ ∂P) +
            (∫ ω, ‖J a ω‖ * ‖Z a ω‖ ∂P) ≤ Kb := by
  intro MD MJ MZ hMD hMJ hMZ hMom
  let Kb : ℝ := MD ^ (1 / 3 : ℝ) * MZ ^ (1 / 2 : ℝ) +
    MJ ^ (1 / 2 : ℝ) * MZ ^ (1 / 4 : ℝ)
  refine ⟨Kb, ?_, ?_⟩
  · dsimp [Kb]
    positivity
  · intro a ha
    rcases hMom a ha with ⟨hD, hDle, hJ, hJle, hZ, hZle⟩
    have hZ3 : MemLp (Z a) 3 P := hZ.mono_exponent (by norm_num : (3 : ℝ≥0∞) ≤ 4)
    have hDmix := fp81s21_mixed_DZZ_holder_of_moments hD hZ3
    have hJmix := fp81s21_mixed_JZ_holder_of_moments hJ hZ3
    let mD : ℝ := ∫ ω, ‖D a ω‖ ^ 3 ∂P
    let mJ : ℝ := ∫ ω, ‖J a ω‖ ^ 2 ∂P
    let mZ3 : ℝ := ∫ ω, ‖Z a ω‖ ^ 3 ∂P
    let mZ2 : ℝ := ∫ ω, ‖Z a ω‖ ^ 2 ∂P
    let mZ4 : ℝ := ∫ ω, ‖Z a ω‖ ^ 4 ∂P
    have hmDnonneg : 0 ≤ mD := by
      dsimp [mD]
      exact integral_nonneg fun ω => by positivity
    have hmJnonneg : 0 ≤ mJ := by
      dsimp [mJ]
      exact integral_nonneg fun ω => by positivity
    have hmZ3nonneg : 0 ≤ mZ3 := by
      dsimp [mZ3]
      exact integral_nonneg fun ω => by positivity
    have hmZ2nonneg : 0 ≤ mZ2 := by
      dsimp [mZ2]
      exact integral_nonneg fun ω => by positivity
    have hmZ4nonneg : 0 ≤ mZ4 := by
      dsimp [mZ4]
      exact integral_nonneg fun ω => by positivity
    have hmDle : mD ≤ MD := hDle
    have hmJle : mJ ≤ MJ := hJle
    have hmZ4le : mZ4 ≤ MZ := hZle
    have hmZ3le : mZ3 ≤ mZ4 ^ (3 / 4 : ℝ) :=
      fp81s21_probability_moment_three_le_four hZ
    have hmZ2le : mZ2 ≤ mZ4 ^ (1 / 2 : ℝ) :=
      fp81s21_probability_moment_two_le_four hZ
    have hDterm : mD ^ (1 / 3 : ℝ) * mZ3 ^ (2 / 3 : ℝ) ≤
        MD ^ (1 / 3 : ℝ) * MZ ^ (1 / 2 : ℝ) := by
      have hDp : mD ^ (1 / 3 : ℝ) ≤ MD ^ (1 / 3 : ℝ) :=
        Real.rpow_le_rpow hmDnonneg hmDle (by norm_num)
      have hZp : mZ3 ^ (2 / 3 : ℝ) ≤ MZ ^ (1 / 2 : ℝ) := by
        calc
          mZ3 ^ (2 / 3 : ℝ) ≤ (mZ4 ^ (3 / 4 : ℝ)) ^ (2 / 3 : ℝ) :=
            Real.rpow_le_rpow hmZ3nonneg hmZ3le (by norm_num)
          _ = mZ4 ^ (1 / 2 : ℝ) := by
            rw [← Real.rpow_mul hmZ4nonneg]
            congr 1 <;> norm_num
          _ ≤ MZ ^ (1 / 2 : ℝ) := Real.rpow_le_rpow hmZ4nonneg hmZ4le (by norm_num)
      exact mul_le_mul hDp hZp (Real.rpow_nonneg hmZ3nonneg _) (Real.rpow_nonneg hMD _)
    have hJterm : Real.sqrt mJ * Real.sqrt mZ2 ≤
        MJ ^ (1 / 2 : ℝ) * MZ ^ (1 / 4 : ℝ) := by
      have hJp : Real.sqrt mJ ≤ MJ ^ (1 / 2 : ℝ) := by
        simpa [Real.sqrt_eq_rpow] using
          (Real.rpow_le_rpow hmJnonneg hmJle (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ)))
      have hZp : Real.sqrt mZ2 ≤ MZ ^ (1 / 4 : ℝ) := by
        calc
          Real.sqrt mZ2 ≤ Real.sqrt (mZ4 ^ (1 / 2 : ℝ)) := Real.sqrt_le_sqrt hmZ2le
          _ = mZ4 ^ (1 / 4 : ℝ) := by
            rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hmZ4nonneg]
            congr 1 <;> norm_num
          _ ≤ MZ ^ (1 / 4 : ℝ) := Real.rpow_le_rpow hmZ4nonneg hmZ4le (by norm_num)
      exact mul_le_mul hJp hZp (Real.sqrt_nonneg _) (Real.rpow_nonneg hMJ _)
    have hDbound :
        (∫ ω, ‖D a ω‖ * ‖Z a ω‖ * ‖Z a ω‖ ∂P) ≤
          MD ^ (1 / 3 : ℝ) * MZ ^ (1 / 2 : ℝ) := by
      calc
        (∫ ω, ‖D a ω‖ * ‖Z a ω‖ * ‖Z a ω‖ ∂P) ≤
            (∫ ω, ‖D a ω‖ ^ 3 ∂P) ^ (1 / 3 : ℝ) *
              (∫ ω, ‖Z a ω‖ ^ 3 ∂P) ^ (2 / 3 : ℝ) := hDmix.2
        _ = mD ^ (1 / 3 : ℝ) * mZ3 ^ (2 / 3 : ℝ) := by rfl
        _ ≤ _ := hDterm
    have hJbound :
        (∫ ω, ‖J a ω‖ * ‖Z a ω‖ ∂P) ≤
          MJ ^ (1 / 2 : ℝ) * MZ ^ (1 / 4 : ℝ) := by
      calc
        (∫ ω, ‖J a ω‖ * ‖Z a ω‖ ∂P) ≤
            Real.sqrt (∫ ω, ‖J a ω‖ ^ 2 ∂P) *
              Real.sqrt (∫ ω, ‖Z a ω‖ ^ 2 ∂P) := hJmix.2
        _ = Real.sqrt mJ * Real.sqrt mZ2 := by rfl
        _ ≤ _ := hJterm
    change (∫ ω, ‖D a ω‖ * ‖Z a ω‖ * ‖Z a ω‖ ∂P) +
        (∫ ω, ‖J a ω‖ * ‖Z a ω‖ ∂P) ≤ Kb
    dsimp [Kb]
    exact add_le_add hDbound hJbound

end HRS.Fp81.S21

#print axioms HRS.Fp81.S21.fp81s21_mixed_DZZ_holder_of_moments
#print axioms HRS.Fp81.S21.fp81s21_mixed_JZ_holder_of_moments
#print axioms HRS.Fp81.S21.fp81s21_gaussian_correction_integral_certificate
#print axioms HRS.Fp81.S21.fp81s21_uniform_gaussian_correction_mixed_moments
