import HRS.MS.Fp81S21Lifting

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace HRS.Fp81.V01

private theorem fp81v01_integrable_norm_of_sixth
    {Ω X : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X] [BorelSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P] (U : Ω → X) (hU : Measurable U)
    (hU6 : Integrable (fun ω => ‖U ω‖ ^ 6) P) :
    Integrable (fun ω => ‖U ω‖) P := by
  have hmajor : Integrable (fun ω => 1 + ‖U ω‖ ^ 6) P :=
    (integrable_const (1 : ℝ)).add hU6
  refine hmajor.mono' ((measurable_norm.comp hU).aestronglyMeasurable) ?_
  exact Filter.Eventually.of_forall fun ω => by
    have hx : 0 ≤ ‖U ω‖ := norm_nonneg _
    have hpoint : ‖U ω‖ ≤ 1 + ‖U ω‖ ^ 6 := by
      by_cases hle : ‖U ω‖ ≤ 1
      · nlinarith [sq_nonneg (‖U ω‖ ^ 3)]
      · have hge : 1 ≤ ‖U ω‖ := le_of_not_ge hle
        have hx2 : 1 ≤ ‖U ω‖ ^ 2 := by
          calc
            1 = 1 * 1 := by ring
            _ ≤ ‖U ω‖ * ‖U ω‖ := mul_le_mul hge hge (by norm_num) hx
            _ = ‖U ω‖ ^ 2 := by ring
        have hx4 : 1 ≤ ‖U ω‖ ^ 4 := by
          calc
            1 = 1 * 1 := by ring
            _ ≤ ‖U ω‖ ^ 2 * ‖U ω‖ ^ 2 := mul_le_mul hx2 hx2 (by norm_num) (by positivity)
            _ = ‖U ω‖ ^ 4 := by ring
        have hpow : 1 ≤ ‖U ω‖ ^ 5 := by
          calc
            1 = 1 * 1 := by ring
            _ ≤ ‖U ω‖ * ‖U ω‖ ^ 4 := mul_le_mul hge hx4 (by norm_num) hx
            _ = ‖U ω‖ ^ 5 := by ring
        calc
          ‖U ω‖ = ‖U ω‖ * 1 := by ring
          _ ≤ ‖U ω‖ * ‖U ω‖ ^ 5 := mul_le_mul_of_nonneg_left hpow hx
          _ = ‖U ω‖ ^ 6 := by ring
          _ ≤ 1 + ‖U ω‖ ^ 6 := le_add_of_nonneg_left (by norm_num)
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (U ω)),
      abs_of_nonneg (by positivity : 0 ≤ 1 + ‖U ω‖ ^ 6)] using hpoint

private theorem fp81v01_integrable_quadratic_envelope
    {Ω X : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X] [BorelSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P] (U : Ω → X) (hU : Measurable U)
    (hU6 : Integrable (fun ω => ‖U ω‖ ^ 6) P) :
    Integrable (fun ω => (1 + ‖U ω‖ ^ 2) ^ 2) P := by
  have hmajor0 : Integrable (fun ω => 4 + 4 * ‖U ω‖ ^ 6) P :=
    (integrable_const (4 : ℝ)).add (hU6.const_mul 4)
  have hmajor : Integrable (fun ω => 4 * (1 + ‖U ω‖ ^ 6)) P := by
    convert hmajor0 using 1 <;> ext ω <;> ring
  have hmeasNorm : Measurable (fun ω => ‖U ω‖) := measurable_norm.comp hU
  have hmeas : Measurable (fun ω => (1 + ‖U ω‖ ^ 2) ^ 2) := by
    exact (measurable_const.add (hmeasNorm.pow_const 2)).pow_const 2
  refine hmajor.mono' hmeas.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun ω => by
    let x : ℝ := ‖U ω‖
    have hx : 0 ≤ x := norm_nonneg _
    have hx2 : x ^ 2 ≤ 1 + x ^ 6 := by
      by_cases hle : x ≤ 1
      · have hx2one : x ^ 2 ≤ 1 := by
          calc
            x ^ 2 = x * x := by ring
            _ ≤ 1 * 1 := mul_le_mul hle hle hx (by norm_num)
            _ = 1 := by ring
        nlinarith [sq_nonneg (x ^ 3)]
      · have hge : 1 ≤ x := le_of_not_ge hle
        have hx2one : 1 ≤ x ^ 2 := by
          calc
            1 = 1 * 1 := by ring
            _ ≤ x * x := mul_le_mul hge hge (by norm_num) hx
            _ = x ^ 2 := by ring
        have hx4one : 1 ≤ x ^ 4 := by
          calc
            1 = 1 * 1 := by ring
            _ ≤ x ^ 2 * x ^ 2 := mul_le_mul hx2one hx2one (by norm_num) (by positivity)
            _ = x ^ 4 := by ring
        have hx26 : x ^ 2 ≤ x ^ 6 := by
          calc
            x ^ 2 = x ^ 2 * 1 := by ring
            _ ≤ x ^ 2 * x ^ 4 := mul_le_mul_of_nonneg_left hx4one (sq_nonneg x)
            _ = x ^ 6 := by ring
        linarith
    have hx4 : x ^ 4 ≤ 1 + x ^ 6 := by
      by_cases hle : x ≤ 1
      · have hx2one : x ^ 2 ≤ 1 := by
          calc
            x ^ 2 = x * x := by ring
            _ ≤ 1 * 1 := mul_le_mul hle hle hx (by norm_num)
            _ = 1 := by ring
        have hx42 : x ^ 4 ≤ x ^ 2 := by
          calc
            x ^ 4 = x ^ 2 * x ^ 2 := by ring
            _ ≤ 1 * x ^ 2 := mul_le_mul_of_nonneg_right hx2one (sq_nonneg x)
            _ = x ^ 2 := by ring
        linarith
      · have hge : 1 ≤ x := le_of_not_ge hle
        have hx2one : 1 ≤ x ^ 2 := by
          calc
            1 = 1 * 1 := by ring
            _ ≤ x * x := mul_le_mul hge hge (by norm_num) hx
            _ = x ^ 2 := by ring
        have hx24 : x ^ 2 ≤ x ^ 4 := by
          calc
            x ^ 2 = x ^ 2 * 1 := by ring
            _ ≤ x ^ 2 * x ^ 2 := mul_le_mul_of_nonneg_left hx2one (sq_nonneg x)
            _ = x ^ 4 := by ring
        have hx46 : x ^ 4 ≤ x ^ 6 := by
          calc
            x ^ 4 = x ^ 2 * x ^ 2 := by ring
            _ ≤ x ^ 2 * x ^ 4 := mul_le_mul_of_nonneg_left hx24 (sq_nonneg x)
            _ = x ^ 6 := by ring
        linarith
    have hpoly : (1 + x ^ 2) ^ 2 ≤ 4 * (1 + x ^ 6) := by nlinarith
    simpa [x, Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ (1 + ‖U ω‖ ^ 2) ^ 2), abs_of_nonneg (by positivity :
      0 ≤ 4 * (1 + ‖U ω‖ ^ 6))] using hpoly

private theorem fp81v01_growth_difference_le
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (F : X → Y) (K : ℝ)
    (hgrowth : ∀ x, ‖F x‖ ≤ K * (1 + ‖x‖ ^ 2)) (x y : X) :
    ‖F x - F y‖ ^ 2 ≤
      2 * K ^ 2 * ((1 + ‖x‖ ^ 2) ^ 2 + (1 + ‖y‖ ^ 2) ^ 2) := by
  set a : ℝ := ‖F x‖
  set b : ℝ := ‖F y‖
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ b := norm_nonneg _
  have hdiff : ‖F x - F y‖ ≤ a + b := by
    simpa [a, b] using norm_sub_le (F x) (F y)
  have hdiffsq : ‖F x - F y‖ ^ 2 ≤ (a + b) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hdiff)
      (add_nonneg (norm_nonneg (F x - F y)) (add_nonneg ha hb))]
  have hab : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
    nlinarith [sq_nonneg (a - b)]
  have haG : a ^ 2 ≤ (K * (1 + ‖x‖ ^ 2)) ^ 2 := by
    have hg := hgrowth x
    dsimp [a]
    nlinarith [mul_nonneg (sub_nonneg.mpr hg)
      (add_nonneg (norm_nonneg (F x)) (le_trans (norm_nonneg (F x)) hg))]
  have hbG : b ^ 2 ≤ (K * (1 + ‖y‖ ^ 2)) ^ 2 := by
    have hg := hgrowth y
    dsimp [b]
    nlinarith [mul_nonneg (sub_nonneg.mpr hg)
      (add_nonneg (norm_nonneg (F y)) (le_trans (norm_nonneg (F y)) hg))]
  calc
    ‖F x - F y‖ ^ 2 ≤ (a + b) ^ 2 := hdiffsq
    _ ≤ 2 * (a ^ 2 + b ^ 2) := hab
    _ ≤ 2 * ((K * (1 + ‖x‖ ^ 2)) ^ 2 + (K * (1 + ‖y‖ ^ 2)) ^ 2) := by gcongr
    _ = 2 * K ^ 2 * ((1 + ‖x‖ ^ 2) ^ 2 + (1 + ‖y‖ ^ 2) ^ 2) := by ring

private theorem fp81v01_lift_side_integrability
    {Ω X Y : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasurableSpace Y] [BorelSpace Y]
    [SecondCountableTopology Y]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : X → Y) (U V : Ω → X)
    (K : ℝ) (hF : Measurable F) (hU : Measurable U) (hV : Measurable V)
    (hgrowth : ∀ x, ‖F x‖ ≤ K * (1 + ‖x‖ ^ 2))
    (hU6 : Integrable (fun ω => ‖U ω‖ ^ 6) P)
    (hV6 : Integrable (fun ω => ‖V ω‖ ^ 6) P) :
    Integrable (fun ω => ‖F (U ω) - F (V ω)‖ ^ 2) P ∧
      Integrable (fun ω => ‖U ω - V ω‖) P := by
  have hUq := fp81v01_integrable_quadratic_envelope P U hU hU6
  have hVq := fp81v01_integrable_quadratic_envelope P V hV hV6
  have hOutMajor0 : Integrable
      (fun ω => 2 * K ^ 2 * ((1 + ‖U ω‖ ^ 2) ^ 2 + (1 + ‖V ω‖ ^ 2) ^ 2)) P := by
    convert (hUq.add hVq).const_mul (2 * K ^ 2) using 1 <;> ext ω <;> ring
  have hFUmeas : Measurable (fun ω => F (U ω)) := hF.comp hU
  have hFVmeas : Measurable (fun ω => F (V ω)) := hF.comp hV
  have hdiffMeas : Measurable (fun ω => F (U ω) - F (V ω)) := hFUmeas.sub hFVmeas
  have hOutMeas : Measurable (fun ω => ‖F (U ω) - F (V ω)‖ ^ 2) := by
    exact (measurable_norm.comp hdiffMeas).pow_const 2
  have hOut : Integrable (fun ω => ‖F (U ω) - F (V ω)‖ ^ 2) P := by
    refine hOutMajor0.mono' hOutMeas.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun ω => by
      have hpt := fp81v01_growth_difference_le F K hgrowth (U ω) (V ω)
      simpa only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) 2),
        abs_of_nonneg (by positivity : 0 ≤ 2 * K ^ 2 *
          ((1 + ‖U ω‖ ^ 2) ^ 2 + (1 + ‖V ω‖ ^ 2) ^ 2))] using hpt
  have hUnorm := fp81v01_integrable_norm_of_sixth P U hU hU6
  have hVnorm := fp81v01_integrable_norm_of_sixth P V hV hV6
  have hUVdiffMeas : Measurable (fun ω => U ω - V ω) := hU.sub hV
  have hUVMeas : Measurable (fun ω => ‖U ω - V ω‖) := measurable_norm.comp hUVdiffMeas
  have hUV : Integrable (fun ω => ‖U ω - V ω‖) P := by
    refine (hUnorm.add hVnorm).mono' hUVMeas.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun ω => by
      have hpt : ‖U ω - V ω‖ ≤ ‖U ω‖ + ‖V ω‖ := norm_sub_le _ _
      simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (U ω - V ω)),
        abs_of_nonneg (by positivity : 0 ≤ ‖U ω‖ + ‖V ω‖), Pi.add_apply] using hpt
  exact ⟨hOut, hUV⟩

theorem fp81_s21_lift_L2'
    {Ω X Y : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasurableSpace Y] [BorelSpace Y]
    [SecondCountableTopology Y]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : X → Y) (U V : Ω → X)
    (K M δ R : ℝ) (hK : 0 ≤ K) (hR : 1 ≤ R)
    (hF : Measurable F) (hU : Measurable U) (hV : Measurable V)
    (hgrowth : ∀ x, ‖F x‖ ≤ K * (1 + ‖x‖ ^ 2))
    (hlip : ∀ x y, ‖F x - F y‖ ≤ K * (1 + ‖x‖ + ‖y‖) * ‖x - y‖)
    (hU6 : Integrable (fun ω => ‖U ω‖ ^ 6) P)
    (hV6 : Integrable (fun ω => ‖V ω‖ ^ 6) P)
    (hUmom : ∫ ω, ‖U ω‖ ^ 6 ∂P ≤ M)
    (hVmom : ∫ ω, ‖V ω‖ ^ 6 ∂P ≤ M)
    (hUV : ∫ ω, ‖U ω - V ω‖ ∂P ≤ δ) :
    ∫ ω, ‖F (U ω) - F (V ω)‖ ^ 2 ∂P ≤
      K ^ 2 * ((1 + 2 * R) ^ 2 * (2 * R) * δ + 64 * (1 + M) / R ^ 2) := by
  obtain ⟨hOut, hUVint⟩ :=
    fp81v01_lift_side_integrability P F U V K hF hU hV hgrowth hU6 hV6
  exact HRS.Fp81.S21.fp81_s21_lift_L2 P F U V K M δ R hK hR hF hU hV
    hgrowth hlip hU6 hV6 hUmom hVmom hUVint hUV hOut

theorem fp81_s21_lift_wasserstein'
    {Ω X Y : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasurableSpace Y] [BorelSpace Y]
    [SecondCountableTopology Y]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : X → Y) (U V : Ω → X)
    (K M δ R : ℝ) (hK : 0 ≤ K) (hR : 1 ≤ R)
    (hF : Measurable F) (hU : Measurable U) (hV : Measurable V)
    (hgrowth : ∀ x, ‖F x‖ ≤ K * (1 + ‖x‖ ^ 2))
    (hlip : ∀ x y, ‖F x - F y‖ ≤ K * (1 + ‖x‖ + ‖y‖) * ‖x - y‖)
    (hU6 : Integrable (fun ω => ‖U ω‖ ^ 6) P)
    (hV6 : Integrable (fun ω => ‖V ω‖ ^ 6) P)
    (hUmom : ∫ ω, ‖U ω‖ ^ 6 ∂P ≤ M)
    (hVmom : ∫ ω, ‖V ω‖ ^ 6 ∂P ≤ M)
    (hUV : ∫ ω, ‖U ω - V ω‖ ∂P ≤ δ) :
    wassersteinE 2 (law P (fun ω => F (U ω))) (law P (fun ω => F (V ω))) ≤
      ENNReal.ofReal (Real.sqrt
        (K ^ 2 * ((1 + 2 * R) ^ 2 * (2 * R) * δ + 64 * (1 + M) / R ^ 2))) := by
  obtain ⟨hOut, hUVint⟩ :=
    fp81v01_lift_side_integrability P F U V K hF hU hV hgrowth hU6 hV6
  exact HRS.Fp81.S21.fp81_s21_lift_wasserstein P F U V K M δ R hK hR hF hU hV
    hgrowth hlip hU6 hV6 hUmom hVmom hUVint hUV hOut

theorem fp81_s21_lift_L2_expectation_form
    {Ω X Y : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasurableSpace Y] [BorelSpace Y]
    [SecondCountableTopology Y]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : X → Y) (U V : Ω → X)
    (K M δ R : ℝ) (hK : 0 ≤ K) (hR : 1 ≤ R)
    (hF : Measurable F) (hU : Measurable U) (hV : Measurable V)
    (hgrowth : ∀ x, ‖F x‖ ≤ K * (1 + ‖x‖ ^ 2))
    (hlip : ∀ x y, ‖F x - F y‖ ≤ K * (1 + ‖x‖ + ‖y‖) * ‖x - y‖)
    (hU6 : Integrable (fun ω => ‖U ω‖ ^ 6) P)
    (hV6 : Integrable (fun ω => ‖V ω‖ ^ 6) P)
    (hUmom : ∫ ω, ‖U ω‖ ^ 6 ∂P ≤ M)
    (hVmom : ∫ ω, ‖V ω‖ ^ 6 ∂P ≤ M)
    (hUV : ∫ ω, ‖U ω - V ω‖ ∂P ≤ δ) :
    ∫⁻ ω, ENNReal.ofReal (‖F (U ω) - F (V ω)‖ ^ 2) ∂P ≤
      ENNReal.ofReal
        (K ^ 2 * ((1 + 2 * R) ^ 2 * (2 * R) * δ + 64 * (1 + M) / R ^ 2)) := by
  have hbound := fp81_s21_lift_L2' P F U V K M δ R hK hR hF hU hV
    hgrowth hlip hU6 hV6 hUmom hVmom hUV
  obtain ⟨hOut, _hUVint⟩ :=
    fp81v01_lift_side_integrability P F U V K hF hU hV hgrowth hU6 hV6
  rw [← ofReal_integral_eq_lintegral_ofReal hOut
    (ae_of_all P fun ω => by positivity)]
  exact ENNReal.ofReal_le_ofReal hbound

private theorem fp81v01_w2_of_lintegral_sq
    {Ω Y : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasurableSpace Y] [BorelSpace Y]
    {P : Measure Ω} [IsProbabilityMeasure P] (A B : Ω → Y)
    (hA : Measurable A) (hB : Measurable B) (τ : ℝ) (hτ : 0 ≤ τ)
    (hbound : ∫⁻ ω, ENNReal.ofReal (‖A ω - B ω‖ ^ 2) ∂P ≤ ENNReal.ofReal (τ ^ 2)) :
    wassersteinE 2 (law P A) (law P B) ≤ ENNReal.ofReal τ := by
  have hcouple := wassersteinE_le_of_coupling P 2 (by norm_num) A B
    hA.aemeasurable hB.aemeasurable
  have hcost : ∫⁻ ω, ENNReal.ofReal (‖A ω - B ω‖ ^ ((2 : ℕ) : ℝ)) ∂P =
      ∫⁻ ω, ENNReal.ofReal (‖A ω - B ω‖ ^ 2) ∂P := by
    apply lintegral_congr
    intro ω
    congr 1
    rw [Real.rpow_natCast]
  calc
    wassersteinE 2 (law P A) (law P B) ≤
        (∫⁻ ω, ENNReal.ofReal (‖A ω - B ω‖ ^ ((2 : ℕ) : ℝ)) ∂P) ^ (1 / (2 : ℝ)) := hcouple
    _ = (∫⁻ ω, ENNReal.ofReal (‖A ω - B ω‖ ^ 2) ∂P) ^ (1 / (2 : ℝ)) :=
      congrArg (fun z : ℝ≥0∞ => z ^ (1 / (2 : ℝ))) hcost
    _ ≤ (ENNReal.ofReal (τ ^ 2)) ^ (1 / (2 : ℝ)) :=
      ENNReal.rpow_le_rpow hbound (by norm_num)
    _ = ENNReal.ofReal τ := by
      rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg τ) (by norm_num : 0 ≤ (1 / (2 : ℝ)))]
      congr 1
      rw [← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs, abs_of_nonneg hτ]

private theorem fp81v01_lift_total_triangle
    {Ω Y : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasurableSpace Y] [BorelSpace Y]
    [SecondCountableTopology Y] [CompleteSpace Y]
    {P : Measure Ω} [IsProbabilityMeasure P] (GU FU FV GV : Ω → Y)
    (hGU : Measurable GU) (hFU : Measurable FU) (hFV : Measurable FV) (hGV : Measurable GV)
    (τ σ : ℝ) (hτ : 0 ≤ τ)
    (hErrU : wassersteinE 2 (law P GU) (law P FU) ≤ ENNReal.ofReal τ)
    (hMid : wassersteinE 2 (law P FU) (law P FV) ≤ ENNReal.ofReal σ)
    (hErrV : wassersteinE 2 (law P FV) (law P GV) ≤ ENNReal.ofReal τ) :
    wassersteinE 2 (law P GU) (law P GV) ≤
      ENNReal.ofReal (2 * τ) + ENNReal.ofReal σ := by
  haveI : IsProbabilityMeasure (law P GU) :=
    (Measure.isProbabilityMeasure_map_iff hGU.aemeasurable).2 inferInstance
  haveI : IsProbabilityMeasure (law P FU) :=
    (Measure.isProbabilityMeasure_map_iff hFU.aemeasurable).2 inferInstance
  haveI : IsProbabilityMeasure (law P FV) :=
    (Measure.isProbabilityMeasure_map_iff hFV.aemeasurable).2 inferInstance
  haveI : IsProbabilityMeasure (law P GV) :=
    (Measure.isProbabilityMeasure_map_iff hGV.aemeasurable).2 inferInstance
  have htri1 := wassersteinE_triangle 2 (by norm_num) (law P GU) (law P FU) (law P GV)
  have htri2 := wassersteinE_triangle 2 (by norm_num) (law P FU) (law P FV) (law P GV)
  calc
    wassersteinE 2 (law P GU) (law P GV) ≤
        wassersteinE 2 (law P GU) (law P FU) + wassersteinE 2 (law P FU) (law P GV) := htri1
    _ ≤ ENNReal.ofReal τ + (wassersteinE 2 (law P FU) (law P FV) +
        wassersteinE 2 (law P FV) (law P GV)) := by gcongr
    _ ≤ ENNReal.ofReal τ + (ENNReal.ofReal σ + ENNReal.ofReal τ) := by gcongr
    _ = ENNReal.ofReal (2 * τ) + ENNReal.ofReal σ := by
      calc
        _ = (ENNReal.ofReal τ + ENNReal.ofReal τ) + ENNReal.ofReal σ := by ac_rfl
        _ = ENNReal.ofReal (2 * τ) + ENNReal.ofReal σ := by
          rw [← ENNReal.ofReal_add hτ hτ]
          rw [show τ + τ = 2 * τ by ring]

private theorem fp81v01_lift_total_core
    {Ω X Y : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasurableSpace Y] [BorelSpace Y]
    [SecondCountableTopology Y] [CompleteSpace Y]
    (P : Measure Ω) [IsProbabilityMeasure P] (F G : X → Y) (U V : Ω → X)
    (K M δ R τ : ℝ) (hK : 0 ≤ K) (hR : 1 ≤ R) (hτ : 0 ≤ τ)
    (hF : Measurable F) (hG : Measurable G) (hU : Measurable U) (hV : Measurable V)
    (hgrowth : ∀ x, ‖F x‖ ≤ K * (1 + ‖x‖ ^ 2))
    (hlip : ∀ x y, ‖F x - F y‖ ≤ K * (1 + ‖x‖ + ‖y‖) * ‖x - y‖)
    (hU6 : Integrable (fun ω => ‖U ω‖ ^ 6) P)
    (hV6 : Integrable (fun ω => ‖V ω‖ ^ 6) P)
    (hUmom : ∫ ω, ‖U ω‖ ^ 6 ∂P ≤ M)
    (hVmom : ∫ ω, ‖V ω‖ ^ 6 ∂P ≤ M)
    (hUV : ∫ ω, ‖U ω - V ω‖ ∂P ≤ δ)
    (hGUapprox : ∫⁻ ω, ENNReal.ofReal (‖F (U ω) - G (U ω)‖ ^ 2) ∂P ≤
      ENNReal.ofReal (τ ^ 2))
    (hGVapprox : ∫⁻ ω, ENNReal.ofReal (‖F (V ω) - G (V ω)‖ ^ 2) ∂P ≤
      ENNReal.ofReal (τ ^ 2)) :
    wassersteinE 2 (law P (fun ω => G (U ω))) (law P (fun ω => G (V ω))) ≤
      ENNReal.ofReal (2 * τ) + ENNReal.ofReal (Real.sqrt
        (K ^ 2 * ((1 + 2 * R) ^ 2 * (2 * R) * δ + 64 * (1 + M) / R ^ 2))) := by
  let FU : Ω → Y := fun ω => F (U ω)
  let FV : Ω → Y := fun ω => F (V ω)
  let GU : Ω → Y := fun ω => G (U ω)
  let GV : Ω → Y := fun ω => G (V ω)
  have hFUm : Measurable FU := hF.comp hU
  have hFVm : Measurable FV := hF.comp hV
  have hGUm : Measurable GU := hG.comp hU
  have hGVm : Measurable GV := hG.comp hV
  have hGUapprox' : ∫⁻ ω, ENNReal.ofReal (‖GU ω - FU ω‖ ^ 2) ∂P ≤
      ENNReal.ofReal (τ ^ 2) := by
    simpa [GU, FU, norm_sub_rev] using hGUapprox
  have hErrU := fp81v01_w2_of_lintegral_sq (P := P) GU FU hGUm hFUm τ hτ hGUapprox'
  have hErrV := fp81v01_w2_of_lintegral_sq (P := P) FV GV hFVm hGVm τ hτ
    (by simpa [FV, GV] using hGVapprox)
  have hMid := fp81_s21_lift_wasserstein' P F U V K M δ R hK hR hF hU hV
    hgrowth hlip hU6 hV6 hUmom hVmom hUV
  have hMid' : wassersteinE 2 (law P FU) (law P FV) ≤ ENNReal.ofReal (Real.sqrt
      (K ^ 2 * ((1 + 2 * R) ^ 2 * (2 * R) * δ + 64 * (1 + M) / R ^ 2))) := by
    simpa [FU, FV] using hMid
  exact fp81v01_lift_total_triangle GU FU FV GV hGUm hFUm hFVm hGVm τ
    (Real.sqrt (K ^ 2 * ((1 + 2 * R) ^ 2 * (2 * R) * δ + 64 * (1 + M) / R ^ 2)))
    hτ hErrU hMid' hErrV

theorem fp81_s21_lift_total'
    {Ω X Y : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasurableSpace Y] [BorelSpace Y]
    [SecondCountableTopology Y] [CompleteSpace Y]
    (P : Measure Ω) [IsProbabilityMeasure P] (F G : X → Y) (U V : Ω → X)
    (K M δ R τ : ℝ) (hK : 0 ≤ K) (hR : 1 ≤ R) (hτ : 0 ≤ τ)
    (hF : Measurable F) (hG : Measurable G) (hU : Measurable U) (hV : Measurable V)
    (hgrowth : ∀ x, ‖F x‖ ≤ K * (1 + ‖x‖ ^ 2))
    (hlip : ∀ x y, ‖F x - F y‖ ≤ K * (1 + ‖x‖ + ‖y‖) * ‖x - y‖)
    (hU6 : Integrable (fun ω => ‖U ω‖ ^ 6) P)
    (hV6 : Integrable (fun ω => ‖V ω‖ ^ 6) P)
    (hUmom : ∫ ω, ‖U ω‖ ^ 6 ∂P ≤ M)
    (hVmom : ∫ ω, ‖V ω‖ ^ 6 ∂P ≤ M)
    (hUV : ∫ ω, ‖U ω - V ω‖ ∂P ≤ δ)
    (hOutU : Integrable (fun ω => ‖F (U ω) - G (U ω)‖ ^ 2) P)
    (hOutV : Integrable (fun ω => ‖F (V ω) - G (V ω)‖ ^ 2) P)
    (hGU : ∫ ω, ‖F (U ω) - G (U ω)‖ ^ 2 ∂P ≤ τ ^ 2)
    (hGV : ∫ ω, ‖F (V ω) - G (V ω)‖ ^ 2 ∂P ≤ τ ^ 2) :
    wassersteinE 2 (law P (fun ω => G (U ω))) (law P (fun ω => G (V ω))) ≤
      ENNReal.ofReal (2 * τ) + ENNReal.ofReal (Real.sqrt
        (K ^ 2 * ((1 + 2 * R) ^ 2 * (2 * R) * δ + 64 * (1 + M) / R ^ 2))) := by
  have hGUapprox : ∫⁻ ω, ENNReal.ofReal (‖F (U ω) - G (U ω)‖ ^ 2) ∂P ≤
      ENNReal.ofReal (τ ^ 2) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hOutU
      (ae_of_all P fun ω => by positivity)]
    exact ENNReal.ofReal_le_ofReal hGU
  have hGVapprox : ∫⁻ ω, ENNReal.ofReal (‖F (V ω) - G (V ω)‖ ^ 2) ∂P ≤
      ENNReal.ofReal (τ ^ 2) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hOutV
      (ae_of_all P fun ω => by positivity)]
    exact ENNReal.ofReal_le_ofReal hGV
  exact fp81v01_lift_total_core P F G U V K M δ R τ hK hR hτ hF hG hU hV
    hgrowth hlip hU6 hV6 hUmom hVmom hUV hGUapprox hGVapprox

theorem fp81_s21_lift_total_lintegral
    {Ω X Y : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasurableSpace Y] [BorelSpace Y]
    [SecondCountableTopology Y] [CompleteSpace Y]
    (P : Measure Ω) [IsProbabilityMeasure P] (F G : X → Y) (U V : Ω → X)
    (K M δ R τ : ℝ) (hK : 0 ≤ K) (hR : 1 ≤ R) (hτ : 0 ≤ τ)
    (hF : Measurable F) (hG : Measurable G) (hU : Measurable U) (hV : Measurable V)
    (hgrowth : ∀ x, ‖F x‖ ≤ K * (1 + ‖x‖ ^ 2))
    (hlip : ∀ x y, ‖F x - F y‖ ≤ K * (1 + ‖x‖ + ‖y‖) * ‖x - y‖)
    (hU6 : Integrable (fun ω => ‖U ω‖ ^ 6) P)
    (hV6 : Integrable (fun ω => ‖V ω‖ ^ 6) P)
    (hUmom : ∫ ω, ‖U ω‖ ^ 6 ∂P ≤ M)
    (hVmom : ∫ ω, ‖V ω‖ ^ 6 ∂P ≤ M)
    (hUV : ∫ ω, ‖U ω - V ω‖ ∂P ≤ δ)
    (hGU : ∫⁻ ω, ENNReal.ofReal (‖F (U ω) - G (U ω)‖ ^ 2) ∂P ≤
      ENNReal.ofReal (τ ^ 2))
    (hGV : ∫⁻ ω, ENNReal.ofReal (‖F (V ω) - G (V ω)‖ ^ 2) ∂P ≤
      ENNReal.ofReal (τ ^ 2)) :
    wassersteinE 2 (law P (fun ω => G (U ω))) (law P (fun ω => G (V ω))) ≤
      ENNReal.ofReal (2 * τ) + ENNReal.ofReal (Real.sqrt
        (K ^ 2 * ((1 + 2 * R) ^ 2 * (2 * R) * δ + 64 * (1 + M) / R ^ 2))) := by
  exact fp81v01_lift_total_core P F G U V K M δ R τ hK hR hτ hF hG hU hV
    hgrowth hlip hU6 hV6 hUmom hVmom hUV hGU hGV

theorem fp81_s21_center_L2'
    {Ω Y : Type*} [MeasurableSpace Ω] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [CompleteSpace Y] {P : Measure Ω} [IsProbabilityMeasure P] (A B : Ω → Y)
    (hA : MemLp A 2 P) (hB : MemLp B 2 P) :
    eLpNorm (fun ω => (A ω - ∫ ω', A ω' ∂P) - (B ω - ∫ ω', B ω' ∂P)) 2 P ≤
      2 * eLpNorm (fun ω => A ω - B ω) 2 P := by
  exact HRS.Fp81.S21.fp81_s21_center_L2 A B hA hB
    (hA.integrable one_le_two) (hB.integrable one_le_two)

end HRS.Fp81.V01

#print axioms HRS.Fp81.V01.fp81_s21_lift_L2'
#print axioms HRS.Fp81.V01.fp81_s21_lift_wasserstein'
#print axioms HRS.Fp81.V01.fp81_s21_lift_L2_expectation_form
#print axioms HRS.Fp81.V01.fp81_s21_lift_total'
#print axioms HRS.Fp81.V01.fp81_s21_lift_total_lintegral
#print axioms HRS.Fp81.V01.fp81_s21_center_L2'
