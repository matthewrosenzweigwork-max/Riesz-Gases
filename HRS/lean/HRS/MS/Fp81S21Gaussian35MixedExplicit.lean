import HRS.MS.Fp81S21GaussianCorrectionCert

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

private theorem fp81s21_gaussian35_probability_moment_three_le_four
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

private theorem fp81s21_gaussian35_probability_moment_two_le_four
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

/-- Explicit, horizon-uniform mixed correction bound from separate moment bounds.
The projective covariance is included in the ambient tensor dual for its norm
and mixed integral. -/
theorem fp81s21_gaussian35_mixed_explicit
    {B Ω : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
    [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : ℝ → Ω → B) (J : ℝ → Ω → projTensor B 2) (Z : ℝ → Ω → B)
    (MD MJ MZ : ℝ)
    (hMom : ∀ a : ℝ, 0 ≤ a →
      MemLp (D a) 3 P ∧
      (∫ ω, ‖D a ω‖ ^ 3 ∂P) ≤ MD ∧
      MemLp (J a) 2 P ∧
      (∫ ω, ‖J a ω‖ ^ 2 ∂P) ≤ MJ ∧
      MemLp (Z a) 4 P ∧
      (∫ ω, ‖Z a ω‖ ^ 4 ∂P) ≤ MZ) :
    ∀ a : ℝ, 0 ≤ a →
      (∫ ω, ‖D a ω‖ * ‖Z a ω‖ * ‖Z a ω‖ ∂P) +
          (∫ ω, ‖(J a ω : TensorDual B 2)‖ * ‖Z a ω‖ ∂P) ≤
        MD ^ (1 / 3 : ℝ) * MZ ^ (1 / 2 : ℝ) +
          MJ ^ (1 / 2 : ℝ) * MZ ^ (1 / 4 : ℝ) := by
  intro a ha
  rcases hMom a ha with ⟨hD, hDle, hJ, hJle, hZ, hZle⟩
  -- The subtype inclusion preserves the inherited norm, so its L² moment
  -- hypothesis transports to the ambient TensorDual used by the certificate.
  have hJmeas : AEStronglyMeasurable
      (fun ω => (J a ω : TensorDual B 2)) P :=
    continuous_subtype_val.comp_aestronglyMeasurable hJ.aestronglyMeasurable
  have hJval : MemLp (fun ω => (J a ω : TensorDual B 2)) 2 P := by
    refine MemLp.of_le (f := fun ω => (J a ω : TensorDual B 2))
      (g := J a) hJ hJmeas ?_
    filter_upwards [] with ω
    exact le_of_eq rfl
  have hmJle : (∫ ω, ‖(J a ω : TensorDual B 2)‖ ^ 2 ∂P) ≤ MJ := by
    calc
      (∫ ω, ‖(J a ω : TensorDual B 2)‖ ^ 2 ∂P) =
          ∫ ω, ‖J a ω‖ ^ 2 ∂P := by
        apply integral_congr_ae
        filter_upwards [] with ω
        rfl
      _ ≤ MJ := hJle
  rcases fp81s21_gaussian_correction_integral_certificate
      (D a) (Z a) (fun ω => (J a ω : TensorDual B 2)) hD hZ hJval with
    ⟨_hDint, _hJint, _hDmixint, _hJmixint, hDmix, hJmix⟩
  let mD : ℝ := ∫ ω, ‖D a ω‖ ^ 3 ∂P
  let mJ : ℝ := ∫ ω, ‖(J a ω : TensorDual B 2)‖ ^ 2 ∂P
  let mZ3 : ℝ := ∫ ω, ‖Z a ω‖ ^ 3 ∂P
  let mZ2 : ℝ := ∫ ω, ‖Z a ω‖ ^ 2 ∂P
  let mZ4 : ℝ := ∫ ω, ‖Z a ω‖ ^ 4 ∂P
  have hMD : 0 ≤ MD := by
    rcases hMom 0 le_rfl with ⟨_, hD0, _, _, _, _⟩
    exact (integral_nonneg fun ω => by positivity).trans hD0
  have hMJ : 0 ≤ MJ := by
    rcases hMom 0 le_rfl with ⟨_, _, _, hJ0, _, _⟩
    exact (integral_nonneg fun ω => by positivity).trans hJ0
  have hMZ : 0 ≤ MZ := by
    rcases hMom 0 le_rfl with ⟨_, _, _, _, _, hZ0⟩
    exact (integral_nonneg fun ω => by positivity).trans hZ0
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
  have hmZ4le : mZ4 ≤ MZ := hZle
  have hmJle' : mJ ≤ MJ := by simpa [mJ] using hmJle
  have hmZ3le : mZ3 ≤ mZ4 ^ (3 / 4 : ℝ) :=
    fp81s21_gaussian35_probability_moment_three_le_four hZ
  have hmZ2le : mZ2 ≤ mZ4 ^ (1 / 2 : ℝ) :=
    fp81s21_gaussian35_probability_moment_two_le_four hZ
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
        _ ≤ MZ ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow hmZ4nonneg hmZ4le (by norm_num)
    exact mul_le_mul hDp hZp (Real.rpow_nonneg hmZ3nonneg _) (Real.rpow_nonneg hMD _)
  have hJterm : Real.sqrt mJ * Real.sqrt mZ2 ≤
      MJ ^ (1 / 2 : ℝ) * MZ ^ (1 / 4 : ℝ) := by
    have hJp : Real.sqrt mJ ≤ MJ ^ (1 / 2 : ℝ) := by
      simpa [Real.sqrt_eq_rpow] using
        (Real.rpow_le_rpow hmJnonneg hmJle' (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ)))
    have hZp : Real.sqrt mZ2 ≤ MZ ^ (1 / 4 : ℝ) := by
      calc
        Real.sqrt mZ2 ≤ Real.sqrt (mZ4 ^ (1 / 2 : ℝ)) := Real.sqrt_le_sqrt hmZ2le
        _ = mZ4 ^ (1 / 4 : ℝ) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hmZ4nonneg]
          congr 1 <;> norm_num
        _ ≤ MZ ^ (1 / 4 : ℝ) :=
          Real.rpow_le_rpow hmZ4nonneg hmZ4le (by norm_num)
    exact mul_le_mul hJp hZp (Real.sqrt_nonneg _) (Real.rpow_nonneg hMJ _)
  have hDbound :
      (∫ ω, ‖D a ω‖ * ‖Z a ω‖ * ‖Z a ω‖ ∂P) ≤
        MD ^ (1 / 3 : ℝ) * MZ ^ (1 / 2 : ℝ) := by
    calc
      (∫ ω, ‖D a ω‖ * ‖Z a ω‖ * ‖Z a ω‖ ∂P) ≤
          (∫ ω, ‖D a ω‖ ^ 3 ∂P) ^ (1 / 3 : ℝ) *
            (∫ ω, ‖Z a ω‖ ^ 3 ∂P) ^ (2 / 3 : ℝ) := hDmix
      _ = mD ^ (1 / 3 : ℝ) * mZ3 ^ (2 / 3 : ℝ) := by rfl
      _ ≤ _ := hDterm
  have hJbound :
      (∫ ω, ‖(J a ω : TensorDual B 2)‖ * ‖Z a ω‖ ∂P) ≤
        MJ ^ (1 / 2 : ℝ) * MZ ^ (1 / 4 : ℝ) := by
    calc
      (∫ ω, ‖(J a ω : TensorDual B 2)‖ * ‖Z a ω‖ ∂P) ≤
          Real.sqrt (∫ ω, ‖(J a ω : TensorDual B 2)‖ ^ 2 ∂P) *
            Real.sqrt (∫ ω, ‖Z a ω‖ ^ 2 ∂P) := hJmix
      _ = Real.sqrt mJ * Real.sqrt mZ2 := by rfl
      _ ≤ _ := hJterm
  exact add_le_add hDbound hJbound

end HRS.Fp81.S21

#print axioms HRS.Fp81.S21.fp81s21_gaussian35_mixed_explicit
