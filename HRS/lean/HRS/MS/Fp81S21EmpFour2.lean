import HRS.MS.Fp81S21EmpFour
import HRS.MS.Fp81S21CoeffMoments2

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory
open scoped ENNReal RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.MS.R26T6

/-- On a probability space, a sixth-moment certificate gives the convenient
fourth-moment bound `1 + M`; this avoids introducing fractional powers. -/
theorem fp81s21_empFour_Moment6_to_fourth
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    [MeasurableSpace E] [OpensMeasurableSpace E] [SecondCountableTopology E]
    [BorelSpace E] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : Ω → E) (M : ℝ) (hX : fp81s21_Moment6 P X M) :
    Integrable (fun ω => ‖X ω‖ ^ 4) P ∧
      (∫ ω, ‖X ω‖ ^ 4 ∂P) ≤ 1 + M := by
  have hfour : Integrable (fun ω => ‖X ω‖ ^ 4) P :=
    integrable_norm_pow_of_le hX.1.aestronglyMeasurable
      (by norm_num : 4 ≤ 6) hX.2.1
  have hsum : Integrable (fun ω => (1 : ℝ) + ‖X ω‖ ^ 6) P :=
    (integrable_const 1).add hX.2.1
  have hpoint : ∀ ω, ‖X ω‖ ^ 4 ≤ 1 + ‖X ω‖ ^ 6 := by
    intro ω
    let x := ‖X ω‖
    have hx : 0 ≤ x := norm_nonneg _
    by_cases hle : x ≤ 1
    · have hx4 : x ^ 4 ≤ 1 := by
        calc
          x ^ 4 ≤ 1 ^ 4 := by gcongr
          _ = 1 := by norm_num
      change x ^ 4 ≤ 1 + x ^ 6
      nlinarith [sq_nonneg x]
    · have hx1 : 1 ≤ x := le_of_not_ge hle
      have hx2 : 1 ≤ x ^ 2 := by nlinarith [sq_nonneg (x - 1)]
      have hx4 : x ^ 4 ≤ x ^ 6 := by
        calc
          x ^ 4 = x ^ 4 * 1 := by ring
          _ ≤ x ^ 4 * x ^ 2 := by gcongr
          _ = x ^ 6 := by ring
      change x ^ 4 ≤ 1 + x ^ 6
      linarith
  refine ⟨hfour, ?_⟩
  calc
    (∫ ω, ‖X ω‖ ^ 4 ∂P) ≤ ∫ ω, (1 : ℝ) + ‖X ω‖ ^ 6 ∂P :=
      integral_mono_ae hfour hsum (Filter.Eventually.of_forall hpoint)
    _ = 1 + ∫ ω, ‖X ω‖ ^ 6 ∂P := by
      rw [integral_add (integrable_const 1) hX.2.1]
      simp
    _ ≤ 1 + M := by linarith [hX.2.2]

private theorem fp81s21_empFour_norm_add_fourth
    {E : Type*} [NormedAddCommGroup E] (x y : E) :
    ‖x + y‖ ^ 4 ≤ 8 * (‖x‖ ^ 4 + ‖y‖ ^ 4) := by
  calc
    ‖x + y‖ ^ 4 ≤ (‖x‖ + ‖y‖) ^ 4 := by
      gcongr
      exact norm_add_le x y
    _ ≤ (2 : ℝ) ^ 3 * (‖x‖ ^ 4 + ‖y‖ ^ 4) :=
      add_pow_le (norm_nonneg x) (norm_nonneg y) 4
    _ = 8 * (‖x‖ ^ 4 + ‖y‖ ^ 4) := by norm_num

/-- The B3 operator bound and sixth-moment certificates control the empirical
vector drift's fourth moment at every fixed nonnegative time. -/
theorem fp81s21_empFour_drift_fixedTime_fourth
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (N : ℕ) (hN : 2 ≤ N)
    (qs qB0 : ℝ → Ω → r26t6_Coeff)
    (L : ℝ → r26t6_Coeff →L[ℝ] r26t6_Coeff)
    (M6 CL : ℝ) (hM6 : 0 ≤ M6) (hCL : 0 ≤ CL)
    (hL : ∀ u, 0 ≤ u → ‖L u‖ ≤ CL)
    (hqs : fp81s21_Six P qs M6) (hB0 : fp81s21_Six P qB0 M6) :
    ∀ u, 0 ≤ u →
      Integrable (fun ω => ‖fp81s21_empFour_drift N L qs qB0 u ω‖ ^ 4) P ∧
      (∫ ω, ‖fp81s21_empFour_drift N L qs qB0 u ω‖ ^ 4 ∂P) ≤
        8 * (CL ^ 4 + 1) * (1 + M6) := by
  intro u hu
  have hqs6 := hqs u hu
  have hB06 := hB0 u hu
  have hqs4 := fp81s21_empFour_Moment6_to_fourth (qs u) M6 hqs6
  have hB04 := fp81s21_empFour_Moment6_to_fourth (qB0 u) M6 hB06
  have hNreal : 1 ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N from le_trans (by decide) hN)
  have hsqrt : 1 ≤ Real.sqrt (N : ℝ) := by
    simpa using Real.sqrt_le_sqrt hNreal
  have hsqrtpos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 (by positivity)
  have hinv : (Real.sqrt (N : ℝ))⁻¹ ≤ 1 := (inv_le_one₀ hsqrtpos).2 hsqrt
  have hcinv : |(Real.sqrt (N : ℝ))⁻¹| ≤ 1 := by
    rw [abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
    exact hinv
  have hDmeas : AEMeasurable (fun ω =>
      fp81s21_empFour_drift N L qs qB0 u ω) P := by
    have hq : AEMeasurable (fun ω => qs u ω) P := hqs6.1
    have hb : AEMeasurable (fun ω => qB0 u ω) P := hB06.1
    have hLpart : AEMeasurable (fun ω => L u (qs u ω)) P :=
      (L u).continuous.measurable.comp_aemeasurable hq
    have hcconst : Continuous (fun _ : r26t6_Coeff => (Real.sqrt (N : ℝ))⁻¹) :=
      continuous_const
    have hcsmul : Continuous (fun z : r26t6_Coeff =>
        (Real.sqrt (N : ℝ))⁻¹ • z) := hcconst.smul continuous_id
    have hBpart : AEMeasurable (fun ω =>
        (Real.sqrt (N : ℝ))⁻¹ • qB0 u ω) P :=
      hcsmul.measurable.comp_aemeasurable hb
    have heq : (fun ω => fp81s21_empFour_drift N L qs qB0 u ω) =ᵐ[P]
        ((fun ω => L u (qs u ω)) - (fun ω =>
          (Real.sqrt (N : ℝ))⁻¹ • qB0 u ω)) :=
      Filter.Eventually.of_forall fun _ => rfl
    exact (hLpart.sub hBpart).congr heq.symm
  have hD4meas : AEStronglyMeasurable (fun ω =>
      ‖fp81s21_empFour_drift N L qs qB0 u ω‖ ^ 4) P := by
    exact ((measurable_norm.pow_const 4).comp_aemeasurable hDmeas).aestronglyMeasurable
  have hRhsInt : Integrable (fun ω => 8 * (
      CL ^ 4 * ‖qs u ω‖ ^ 4 + ‖qB0 u ω‖ ^ 4)) P := by
    exact ((hqs4.1.const_mul (CL ^ 4)).add hB04.1).const_mul 8
  have hpoint : ∀ ω, ‖fp81s21_empFour_drift N L qs qB0 u ω‖ ^ 4 ≤
      8 * (CL ^ 4 * ‖qs u ω‖ ^ 4 + ‖qB0 u ω‖ ^ 4) := by
    intro ω
    have hLnorm : ‖L u (qs u ω)‖ ≤ CL * ‖qs u ω‖ := by
      calc
        _ ≤ ‖L u‖ * ‖qs u ω‖ := (L u).le_opNorm _
        _ ≤ CL * ‖qs u ω‖ := mul_le_mul_of_nonneg_right (hL u hu) (norm_nonneg _)
    have hLfour : ‖L u (qs u ω)‖ ^ 4 ≤ CL ^ 4 * ‖qs u ω‖ ^ 4 := by
      calc
        _ ≤ (CL * ‖qs u ω‖) ^ 4 := by gcongr
        _ = CL ^ 4 * ‖qs u ω‖ ^ 4 := by ring
    have hBnorm : ‖(Real.sqrt (N : ℝ))⁻¹ • qB0 u ω‖ ≤ ‖qB0 u ω‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      calc
        |(Real.sqrt (N : ℝ))⁻¹| * ‖qB0 u ω‖ ≤ 1 * ‖qB0 u ω‖ :=
          mul_le_mul_of_nonneg_right hcinv (norm_nonneg _)
        _ = ‖qB0 u ω‖ := one_mul _
    have hBfour : ‖(Real.sqrt (N : ℝ))⁻¹ • qB0 u ω‖ ^ 4 ≤ ‖qB0 u ω‖ ^ 4 :=
      pow_le_pow_left₀ (norm_nonneg _) hBnorm 4
    have htriangle := fp81s21_empFour_norm_add_fourth
      (L u (qs u ω)) (-(Real.sqrt (N : ℝ))⁻¹ • qB0 u ω)
    change ‖L u (qs u ω) - (Real.sqrt (N : ℝ))⁻¹ • qB0 u ω‖ ^ 4 ≤ _
    calc
      _ = ‖L u (qs u ω) + (-(Real.sqrt (N : ℝ))⁻¹ • qB0 u ω)‖ ^ 4 := by
        congr 1
        rw [sub_eq_add_neg]
        simp [neg_smul]
      _ ≤ 8 * (‖L u (qs u ω)‖ ^ 4 +
          ‖-(Real.sqrt (N : ℝ))⁻¹ • qB0 u ω‖ ^ 4) := htriangle
      _ ≤ 8 * (CL ^ 4 * ‖qs u ω‖ ^ 4 + ‖qB0 u ω‖ ^ 4) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact add_le_add hLfour (by simpa using hBfour)
  have hDint : Integrable (fun ω =>
      ‖fp81s21_empFour_drift N L qs qB0 u ω‖ ^ 4) P :=
    hRhsInt.mono' hD4meas (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) 4)]
      exact hpoint ω)
  have hDbound : (∫ ω, ‖fp81s21_empFour_drift N L qs qB0 u ω‖ ^ 4 ∂P) ≤
      8 * (CL ^ 4 + 1) * (1 + M6) := by
    calc
      _ ≤ ∫ ω, 8 * (CL ^ 4 * ‖qs u ω‖ ^ 4 + ‖qB0 u ω‖ ^ 4) ∂P :=
        integral_mono_ae hDint hRhsInt (Filter.Eventually.of_forall hpoint)
      _ = 8 * (CL ^ 4 * (∫ ω, ‖qs u ω‖ ^ 4 ∂P) +
          (∫ ω, ‖qB0 u ω‖ ^ 4 ∂P)) := by
        rw [integral_const_mul]
        rw [integral_add (hqs4.1.const_mul (CL ^ 4)) hB04.1]
        rw [integral_const_mul]
      _ ≤ 8 * (CL ^ 4 * (1 + M6) + (1 + M6)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact add_le_add
          (mul_le_mul_of_nonneg_left hqs4.2 (by positivity)) hB04.2
      _ = 8 * (CL ^ 4 + 1) * (1 + M6) := by ring
  exact ⟨hDint, hDbound⟩

#print axioms HRS.Fp81.S21.fp81s21_empFour_Moment6_to_fourth
#print axioms HRS.Fp81.S21.fp81s21_empFour_drift_fixedTime_fourth

end HRS.Fp81.S21
