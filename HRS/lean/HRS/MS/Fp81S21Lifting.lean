import Mathlib
import HRS.Prob.Metrics

/-!
# S2.1 packet 7: same-trajectory lifting in quadratic Wasserstein distance

The sixth moments below are stated as integrability of the scalar norm powers together with
their explicit expectation bounds.  This is the real-integral form of `MemLp U 6 P` that is
convenient for the cutoff estimate.

The squared image difference is supplied as an explicit integrability hypothesis.  This keeps
the estimate valid for arbitrary Borel normed output spaces without imposing separability merely
to infer measurability of the pointwise difference.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace HRS.Fp81.S21

private lemma fp81_s21_cross_tail (x y R : ℝ) (hR : 1 ≤ R) (hx : 0 ≤ x)
    (hy : R < y) : R ^ 2 * (1 + x ^ 2) ^ 2 ≤ 4 * (x ^ 6 + y ^ 6) := by
  by_cases hxr : R < x
  · have hR2 : R ^ 2 ≤ x ^ 2 := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ x - R) (by positivity : 0 ≤ x + R)]
    have hx2 : 1 ≤ x ^ 2 := by nlinarith [hR, hxr]
    have hbase : 1 + x ^ 2 ≤ 2 * x ^ 2 := by linarith
    calc
      R ^ 2 * (1 + x ^ 2) ^ 2 ≤ x ^ 2 * (1 + x ^ 2) ^ 2 := by gcongr
      _ ≤ x ^ 2 * (2 * x ^ 2) ^ 2 := by gcongr
      _ = 4 * x ^ 6 := by ring
      _ ≤ 4 * (x ^ 6 + y ^ 6) := by nlinarith [sq_nonneg (y ^ 3)]
  · have hxR : x ≤ R := le_of_not_gt hxr
    have hx2 : x ^ 2 ≤ R ^ 2 := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ R - x) (by positivity : 0 ≤ R + x)]
    have hR2 : 1 ≤ R ^ 2 := by nlinarith [hR]
    have hbase : 1 + x ^ 2 ≤ 2 * R ^ 2 := by linarith
    have hyR : R ≤ y := le_of_lt hy
    have hy6 : R ^ 6 ≤ y ^ 6 := by gcongr
    calc
      R ^ 2 * (1 + x ^ 2) ^ 2 ≤ R ^ 2 * (2 * R ^ 2) ^ 2 := by gcongr
      _ = 4 * R ^ 6 := by ring
      _ ≤ 4 * y ^ 6 := by nlinarith
      _ ≤ 4 * (x ^ 6 + y ^ 6) := by nlinarith [sq_nonneg (x ^ 3)]

private lemma fp81_s21_tail_sum (u v R : ℝ) (hR : 1 ≤ R) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (htail : R < u ∨ R < v) :
    (1 + u ^ 2) ^ 2 + (1 + v ^ 2) ^ 2 ≤ 16 * (u ^ 6 + v ^ 6) / R ^ 2 := by
  have hu' : R ^ 2 * (1 + u ^ 2) ^ 2 ≤ 8 * (u ^ 6 + v ^ 6) := by
    rcases htail with h | h
    · calc
        _ ≤ 4 * (u ^ 6 + u ^ 6) := fp81_s21_cross_tail u u R hR hu h
        _ ≤ 8 * (u ^ 6 + v ^ 6) := by nlinarith [sq_nonneg (v ^ 3)]
    · calc
        _ ≤ 4 * (u ^ 6 + v ^ 6) := fp81_s21_cross_tail u v R hR hu h
        _ ≤ 8 * (u ^ 6 + v ^ 6) := by nlinarith [sq_nonneg (u ^ 3), sq_nonneg (v ^ 3)]
  have hv' : R ^ 2 * (1 + v ^ 2) ^ 2 ≤ 8 * (u ^ 6 + v ^ 6) := by
    rcases htail with h | h
    · calc
        _ ≤ 4 * (v ^ 6 + u ^ 6) := fp81_s21_cross_tail v u R hR hv h
        _ ≤ 8 * (u ^ 6 + v ^ 6) := by nlinarith [sq_nonneg (u ^ 3), sq_nonneg (v ^ 3)]
    · calc
        _ ≤ 4 * (v ^ 6 + v ^ 6) := fp81_s21_cross_tail v v R hR hv h
        _ ≤ 8 * (u ^ 6 + v ^ 6) := by nlinarith [sq_nonneg (u ^ 3)]
  apply (le_div_iff₀ (by positivity : 0 < R ^ 2)).2
  calc
    ((1 + u ^ 2) ^ 2 + (1 + v ^ 2) ^ 2) * R ^ 2 =
        R ^ 2 * (1 + u ^ 2) ^ 2 + R ^ 2 * (1 + v ^ 2) ^ 2 := by ring
    _ ≤ 8 * (u ^ 6 + v ^ 6) + 8 * (u ^ 6 + v ^ 6) := add_le_add hu' hv'
    _ = 16 * (u ^ 6 + v ^ 6) := by ring

private lemma fp81_s21_growth_difference_le
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
    nlinarith [mul_nonneg (sub_nonneg.mpr hdiff) (add_nonneg (norm_nonneg (F x - F y)) (add_nonneg ha hb))]
  have hab : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
    nlinarith [sq_nonneg (a - b)]
  have haG : a ^ 2 ≤ (K * (1 + ‖x‖ ^ 2)) ^ 2 := by
    have hg := hgrowth x
    dsimp [a]
    nlinarith [sq_nonneg (K * (1 + ‖x‖ ^ 2) - ‖F x‖)]
  have hbG : b ^ 2 ≤ (K * (1 + ‖y‖ ^ 2)) ^ 2 := by
    have hg := hgrowth y
    dsimp [b]
    nlinarith [sq_nonneg (K * (1 + ‖y‖ ^ 2) - ‖F y‖)]
  calc
    ‖F x - F y‖ ^ 2 ≤ (a + b) ^ 2 := hdiffsq
    _ ≤ 2 * (a ^ 2 + b ^ 2) := hab
    _ ≤ 2 * ((K * (1 + ‖x‖ ^ 2)) ^ 2 + (K * (1 + ‖y‖ ^ 2)) ^ 2) := by gcongr
    _ = 2 * K ^ 2 * ((1 + ‖x‖ ^ 2) ^ 2 + (1 + ‖y‖ ^ 2) ^ 2) := by ring

private lemma fp81_s21_local_difference_le
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (F : X → Y) (K R : ℝ) (hK : 0 ≤ K)
    (hlip : ∀ x y, ‖F x - F y‖ ≤ K * (1 + ‖x‖ + ‖y‖) * ‖x - y‖)
    (x y : X) (hR : 1 ≤ R) (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) :
    ‖F x - F y‖ ^ 2 ≤ K ^ 2 * (1 + 2 * R) ^ 2 * (2 * R) * ‖x - y‖ := by
  set d : ℝ := ‖x - y‖
  have hd : 0 ≤ d := norm_nonneg _
  have hdR : d ≤ 2 * R := by
    dsimp [d]
    calc
      ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le _ _
      _ ≤ 2 * R := by linarith
  have hcoef : 1 + ‖x‖ + ‖y‖ ≤ 1 + 2 * R := by linarith
  have hLip : ‖F x - F y‖ ≤ K * (1 + 2 * R) * d := by
    calc
      ‖F x - F y‖ ≤ K * (1 + ‖x‖ + ‖y‖) * d := by simpa [d] using hlip x y
      _ ≤ K * (1 + 2 * R) * d := by gcongr
  have hLip0 : 0 ≤ K * (1 + 2 * R) * d := by positivity
  have hLipSq : ‖F x - F y‖ ^ 2 ≤ (K * (1 + 2 * R) * d) ^ 2 := by
    have hprod := mul_nonneg (sub_nonneg.mpr hLip)
      (add_nonneg (norm_nonneg (F x - F y)) hLip0)
    nlinarith [hprod]
  have hdSq : d ^ 2 ≤ 2 * R * d := by nlinarith
  calc
    ‖F x - F y‖ ^ 2 ≤ (K * (1 + 2 * R) * d) ^ 2 := hLipSq
    _ = K ^ 2 * (1 + 2 * R) ^ 2 * d ^ 2 := by ring
    _ ≤ K ^ 2 * (1 + 2 * R) ^ 2 * (2 * R * d) := by gcongr
    _ = K ^ 2 * (1 + 2 * R) ^ 2 * (2 * R) * d := by ring

theorem fp81_s21_lift_L2
    {Ω X Y : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasurableSpace Y] [BorelSpace Y]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : X → Y) (U V : Ω → X)
    (K M δ R : ℝ) (hK : 0 ≤ K) (hR : 1 ≤ R)
    (hF : Measurable F) (hU : Measurable U) (hV : Measurable V)
    (hgrowth : ∀ x, ‖F x‖ ≤ K * (1 + ‖x‖ ^ 2))
    (hlip : ∀ x y, ‖F x - F y‖ ≤ K * (1 + ‖x‖ + ‖y‖) * ‖x - y‖)
    (hU6 : Integrable (fun ω => ‖U ω‖ ^ 6) P)
    (hV6 : Integrable (fun ω => ‖V ω‖ ^ 6) P)
    (hUmom : ∫ ω, ‖U ω‖ ^ 6 ∂P ≤ M)
    (hVmom : ∫ ω, ‖V ω‖ ^ 6 ∂P ≤ M)
    (hUVint : Integrable (fun ω => ‖U ω - V ω‖) P)
    (hUV : ∫ ω, ‖U ω - V ω‖ ∂P ≤ δ)
    (hOut : Integrable (fun ω => ‖F (U ω) - F (V ω)‖ ^ 2) P) :
    ∫ ω, ‖F (U ω) - F (V ω)‖ ^ 2 ∂P ≤
      K ^ 2 * ((1 + 2 * R) ^ 2 * (2 * R) * δ + 64 * (1 + M) / R ^ 2) := by
  have hCoeff0 : 0 ≤ K ^ 2 * (1 + 2 * R) ^ 2 * (2 * R) := by positivity
  have hTail0 : 0 ≤ 32 * K ^ 2 / R ^ 2 := by positivity
  have hPoint : ∀ ω, ‖F (U ω) - F (V ω)‖ ^ 2 ≤
      (K ^ 2 * (1 + 2 * R) ^ 2 * (2 * R)) * ‖U ω - V ω‖ +
          (32 * K ^ 2 / R ^ 2) * (‖U ω‖ ^ 6 + ‖V ω‖ ^ 6) := by
    intro ω
    by_cases hu : ‖U ω‖ ≤ R
    · by_cases hv : ‖V ω‖ ≤ R
      · have hlocal := fp81_s21_local_difference_le F K R hK hlip (U ω) (V ω) hR hu hv
        calc
          _ ≤ (K ^ 2 * (1 + 2 * R) ^ 2 * (2 * R)) * ‖U ω - V ω‖ := hlocal
          _ ≤ (K ^ 2 * (1 + 2 * R) ^ 2 * (2 * R)) * ‖U ω - V ω‖ +
              (32 * K ^ 2 / R ^ 2) * (‖U ω‖ ^ 6 + ‖V ω‖ ^ 6) :=
            le_add_of_nonneg_right (mul_nonneg hTail0 (by positivity))
      · have htail : R < ‖U ω‖ ∨ R < ‖V ω‖ := Or.inr (lt_of_not_ge hv)
        have ht := fp81_s21_tail_sum ‖U ω‖ ‖V ω‖ R hR
          (norm_nonneg _) (norm_nonneg _) htail
        calc
          _ ≤ 2 * K ^ 2 * ((1 + ‖U ω‖ ^ 2) ^ 2 + (1 + ‖V ω‖ ^ 2) ^ 2) :=
            fp81_s21_growth_difference_le F K hgrowth _ _
          _ ≤ 2 * K ^ 2 * (16 * (‖U ω‖ ^ 6 + ‖V ω‖ ^ 6) / R ^ 2) := by gcongr
          _ = (32 * K ^ 2 / R ^ 2) * (‖U ω‖ ^ 6 + ‖V ω‖ ^ 6) := by ring
          _ ≤ _ := le_add_of_nonneg_left (mul_nonneg hCoeff0 (norm_nonneg _))
    · have htail : R < ‖U ω‖ ∨ R < ‖V ω‖ := Or.inl (lt_of_not_ge hu)
      have ht := fp81_s21_tail_sum ‖U ω‖ ‖V ω‖ R hR
        (norm_nonneg _) (norm_nonneg _) htail
      calc
        _ ≤ 2 * K ^ 2 * ((1 + ‖U ω‖ ^ 2) ^ 2 + (1 + ‖V ω‖ ^ 2) ^ 2) :=
          fp81_s21_growth_difference_le F K hgrowth _ _
        _ ≤ 2 * K ^ 2 * (16 * (‖U ω‖ ^ 6 + ‖V ω‖ ^ 6) / R ^ 2) := by gcongr
        _ = (32 * K ^ 2 / R ^ 2) * (‖U ω‖ ^ 6 + ‖V ω‖ ^ 6) := by ring
        _ ≤ _ := le_add_of_nonneg_left (mul_nonneg hCoeff0 (norm_nonneg _))
  have hUpperInt : Integrable (fun ω =>
      (K ^ 2 * (1 + 2 * R) ^ 2 * (2 * R)) * ‖U ω - V ω‖ +
        (32 * K ^ 2 / R ^ 2) * (‖U ω‖ ^ 6 + ‖V ω‖ ^ 6)) P := by
    exact (hUVint.const_mul _).add ((hU6.add hV6).const_mul _)
  have hmono := integral_mono hOut hUpperInt hPoint
  have hmomSum : ∫ ω, ‖U ω‖ ^ 6 + ‖V ω‖ ^ 6 ∂P ≤ 2 * M := by
    rw [integral_add hU6 hV6]
    linarith
  have hcalc : ∫ ω,
      (K ^ 2 * (1 + 2 * R) ^ 2 * (2 * R)) * ‖U ω - V ω‖ +
        (32 * K ^ 2 / R ^ 2) * (‖U ω‖ ^ 6 + ‖V ω‖ ^ 6) ∂P =
      (K ^ 2 * (1 + 2 * R) ^ 2 * (2 * R)) *
        (∫ ω, ‖U ω - V ω‖ ∂P) +
        (32 * K ^ 2 / R ^ 2) *
        (∫ ω, ‖U ω‖ ^ 6 + ‖V ω‖ ^ 6 ∂P) := by
    calc
      _ = (∫ ω, (K ^ 2 * (1 + 2 * R) ^ 2 * (2 * R)) * ‖U ω - V ω‖ ∂P) +
          (∫ ω, (32 * K ^ 2 / R ^ 2) * (‖U ω‖ ^ 6 + ‖V ω‖ ^ 6) ∂P) :=
        integral_add (hUVint.const_mul _) ((hU6.add hV6).const_mul _)
      _ = (K ^ 2 * (1 + 2 * R) ^ 2 * (2 * R)) *
            (∫ ω, ‖U ω - V ω‖ ∂P) +
          (32 * K ^ 2 / R ^ 2) * (∫ ω, ‖U ω‖ ^ 6 + ‖V ω‖ ^ 6 ∂P) := by
        rw [integral_const_mul, integral_const_mul, integral_add hU6 hV6]
  have hMδ := add_le_add
    (mul_le_mul_of_nonneg_left hUV hCoeff0)
    (mul_le_mul_of_nonneg_left hmomSum hTail0)
  rw [hcalc] at hmono
  have hKR : 0 ≤ K ^ 2 / R ^ 2 := div_nonneg (sq_nonneg K) (by positivity)
  have htailCompare : (32 * K ^ 2 / R ^ 2) * (2 * M) ≤
      K ^ 2 * (64 * (1 + M) / R ^ 2) := by
    calc
      (32 * K ^ 2 / R ^ 2) * (2 * M) = 64 * (K ^ 2 / R ^ 2) * M := by ring
      _ = (K ^ 2 / R ^ 2) * (64 * M) := by ring
      _ ≤ (K ^ 2 / R ^ 2) * (64 * (1 + M)) := by
        have hM : 64 * M ≤ 64 * (1 + M) := by linarith
        exact mul_le_mul_of_nonneg_left hM hKR
      _ = 64 * (K ^ 2 / R ^ 2) * (1 + M) := by ring
      _ = K ^ 2 * (64 * (1 + M) / R ^ 2) := by ring
  calc
    _ ≤ (K ^ 2 * (1 + 2 * R) ^ 2 * (2 * R)) * δ +
        (32 * K ^ 2 / R ^ 2) * (2 * M) := hmono.trans hMδ
    _ ≤ (K ^ 2 * (1 + 2 * R) ^ 2 * (2 * R)) * δ +
        K ^ 2 * (64 * (1 + M) / R ^ 2) := add_le_add le_rfl htailCompare
    _ = K ^ 2 * ((1 + 2 * R) ^ 2 * (2 * R) * δ + 64 * (1 + M) / R ^ 2) := by ring

private theorem fp81_s21_w2_of_integral_sq
    {Ω Y : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasurableSpace Y] [BorelSpace Y]
    {P : Measure Ω} [IsProbabilityMeasure P] (A B : Ω → Y)
    (hA : Measurable A) (hB : Measurable B) (τ : ℝ) (hτ : 0 ≤ τ)
    (hint : Integrable (fun ω => ‖A ω - B ω‖ ^ 2) P)
    (hbound : ∫ ω, ‖A ω - B ω‖ ^ 2 ∂P ≤ τ ^ 2) :
    wassersteinE 2 (law P A) (law P B) ≤ ENNReal.ofReal τ := by
  have hcouple := wassersteinE_le_of_coupling P 2 (by norm_num) A B hA.aemeasurable hB.aemeasurable
  have hcost : ∫⁻ ω, ENNReal.ofReal (‖A ω - B ω‖ ^ 2) ∂P =
      ENNReal.ofReal (∫ ω, ‖A ω - B ω‖ ^ 2 ∂P) :=
    (ofReal_integral_eq_lintegral_ofReal hint (ae_of_all P fun ω => by positivity)).symm
  have hcostReal : ∫⁻ ω, ENNReal.ofReal (‖A ω - B ω‖ ^ ((2 : ℕ) : ℝ)) ∂P =
      ENNReal.ofReal (∫ ω, ‖A ω - B ω‖ ^ 2 ∂P) := by
    calc
      _ = ∫⁻ ω, ENNReal.ofReal (‖A ω - B ω‖ ^ (2 : ℕ)) ∂P := by
        apply lintegral_congr
        intro ω
        congr 1
        rw [Real.rpow_natCast]
      _ = _ := hcost
  have hI0 : 0 ≤ ∫ ω, ‖A ω - B ω‖ ^ 2 ∂P := integral_nonneg (fun ω => by positivity)
  have hsqrt : Real.sqrt (∫ ω, ‖A ω - B ω‖ ^ 2 ∂P) ≤ τ := by
    nlinarith [Real.sq_sqrt hI0, Real.sqrt_nonneg (∫ ω, ‖A ω - B ω‖ ^ 2 ∂P), hbound]
  calc
    wassersteinE 2 (law P A) (law P B) ≤
        (∫⁻ ω, ENNReal.ofReal (‖A ω - B ω‖ ^ 2) ∂P) ^ (1 / (2 : ℝ)) := hcouple
    _ = (ENNReal.ofReal (∫ ω, ‖A ω - B ω‖ ^ 2 ∂P)) ^ (1 / (2 : ℝ)) :=
      congrArg (fun z : ℝ≥0∞ => z ^ (1 / (2 : ℝ))) hcostReal
    _ = ENNReal.ofReal (Real.sqrt (∫ ω, ‖A ω - B ω‖ ^ 2 ∂P)) := by
      rw [ENNReal.ofReal_rpow_of_nonneg hI0 (by norm_num : 0 ≤ (1 / (2 : ℝ)))]
      rw [Real.sqrt_eq_rpow]
    _ ≤ ENNReal.ofReal τ := ENNReal.ofReal_le_ofReal hsqrt

theorem fp81_s21_lift_wasserstein
    {Ω X Y : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasurableSpace Y] [BorelSpace Y]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : X → Y) (U V : Ω → X)
    (K M δ R : ℝ) (hK : 0 ≤ K) (hR : 1 ≤ R)
    (hF : Measurable F) (hU : Measurable U) (hV : Measurable V)
    (hgrowth : ∀ x, ‖F x‖ ≤ K * (1 + ‖x‖ ^ 2))
    (hlip : ∀ x y, ‖F x - F y‖ ≤ K * (1 + ‖x‖ + ‖y‖) * ‖x - y‖)
    (hU6 : Integrable (fun ω => ‖U ω‖ ^ 6) P)
    (hV6 : Integrable (fun ω => ‖V ω‖ ^ 6) P)
    (hUmom : ∫ ω, ‖U ω‖ ^ 6 ∂P ≤ M)
    (hVmom : ∫ ω, ‖V ω‖ ^ 6 ∂P ≤ M)
    (hUVint : Integrable (fun ω => ‖U ω - V ω‖) P)
    (hUV : ∫ ω, ‖U ω - V ω‖ ∂P ≤ δ)
    (hOut : Integrable (fun ω => ‖F (U ω) - F (V ω)‖ ^ 2) P) :
    wassersteinE 2 (law P (fun ω => F (U ω))) (law P (fun ω => F (V ω))) ≤
      ENNReal.ofReal (Real.sqrt
        (K ^ 2 * ((1 + 2 * R) ^ 2 * (2 * R) * δ + 64 * (1 + M) / R ^ 2))) := by
  let A : Ω → Y := fun ω => F (U ω)
  let B : Ω → Y := fun ω => F (V ω)
  have hA : Measurable A := hF.comp hU
  have hB : Measurable B := hF.comp hV
  have hLift := fp81_s21_lift_L2 P F U V K M δ R hK hR hF hU hV hgrowth hlip
    hU6 hV6 hUmom hVmom hUVint hUV hOut
  have hI0 : 0 ≤ ∫ ω, ‖A ω - B ω‖ ^ 2 ∂P := integral_nonneg (fun ω => by positivity)
  have hcost : ∫⁻ ω, ENNReal.ofReal (‖A ω - B ω‖ ^ 2) ∂P =
      ENNReal.ofReal (∫ ω, ‖A ω - B ω‖ ^ 2 ∂P) :=
    (ofReal_integral_eq_lintegral_ofReal hOut
      (ae_of_all P fun ω => by positivity)).symm
  have hcostReal : ∫⁻ ω, ENNReal.ofReal (‖A ω - B ω‖ ^ ((2 : ℕ) : ℝ)) ∂P =
      ENNReal.ofReal (∫ ω, ‖A ω - B ω‖ ^ 2 ∂P) := by
    calc
      _ = ∫⁻ ω, ENNReal.ofReal (‖A ω - B ω‖ ^ (2 : ℕ)) ∂P := by
        apply lintegral_congr
        intro ω
        congr 1
        rw [Real.rpow_natCast]
      _ = _ := hcost
  have hprobA : IsProbabilityMeasure (law P A) :=
    (Measure.isProbabilityMeasure_map_iff hA.aemeasurable).2 inferInstance
  have hprobB : IsProbabilityMeasure (law P B) :=
    (Measure.isProbabilityMeasure_map_iff hB.aemeasurable).2 inferInstance
  have hcouple := wassersteinE_le_of_coupling P 2 (by norm_num) A B
    hA.aemeasurable hB.aemeasurable
  calc
    wassersteinE 2 (law P A) (law P B) ≤
        (∫⁻ ω, ENNReal.ofReal (‖A ω - B ω‖ ^ 2) ∂P) ^ (1 / (2 : ℝ)) := hcouple
    _ = (ENNReal.ofReal (∫ ω, ‖A ω - B ω‖ ^ 2 ∂P)) ^ (1 / (2 : ℝ)) :=
      congrArg (fun z : ℝ≥0∞ => z ^ (1 / (2 : ℝ))) hcostReal
    _ = ENNReal.ofReal (Real.sqrt (∫ ω, ‖A ω - B ω‖ ^ 2 ∂P)) := by
      rw [ENNReal.ofReal_rpow_of_nonneg hI0 (by norm_num : 0 ≤ (1 / (2 : ℝ)))]
      rw [Real.sqrt_eq_rpow]
    _ ≤ ENNReal.ofReal (Real.sqrt
        (K ^ 2 * ((1 + 2 * R) ^ 2 * (2 * R) * δ + 64 * (1 + M) / R ^ 2))) := by
      exact ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt hLift)

theorem fp81_s21_lift_total
    {Ω X Y : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X] [BorelSpace X]
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
    (hUVint : Integrable (fun ω => ‖U ω - V ω‖) P)
    (hUV : ∫ ω, ‖U ω - V ω‖ ∂P ≤ δ)
    (hOut : Integrable (fun ω => ‖F (U ω) - F (V ω)‖ ^ 2) P)
    (hGUerr : Integrable (fun ω => ‖F (U ω) - G (U ω)‖ ^ 2) P)
    (hGVerr : Integrable (fun ω => ‖F (V ω) - G (V ω)‖ ^ 2) P)
    (hGU : ∫ ω, ‖F (U ω) - G (U ω)‖ ^ 2 ∂P ≤ τ ^ 2)
    (hGV : ∫ ω, ‖F (V ω) - G (V ω)‖ ^ 2 ∂P ≤ τ ^ 2) :
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
  haveI : IsProbabilityMeasure (law P FU) :=
    (Measure.isProbabilityMeasure_map_iff hFUm.aemeasurable).2 inferInstance
  haveI : IsProbabilityMeasure (law P FV) :=
    (Measure.isProbabilityMeasure_map_iff hFVm.aemeasurable).2 inferInstance
  haveI : IsProbabilityMeasure (law P GU) :=
    (Measure.isProbabilityMeasure_map_iff hGUm.aemeasurable).2 inferInstance
  haveI : IsProbabilityMeasure (law P GV) :=
    (Measure.isProbabilityMeasure_map_iff hGVm.aemeasurable).2 inferInstance
  have hGUerr' : Integrable (fun ω => ‖GU ω - FU ω‖ ^ 2) P := by
    convert hGUerr using 1 <;> ext ω <;> simp [GU, FU, norm_sub_rev]
  have hGU' : ∫ ω, ‖GU ω - FU ω‖ ^ 2 ∂P ≤ τ ^ 2 := by
    simpa [GU, FU, norm_sub_rev] using hGU
  have hErrU := fp81_s21_w2_of_integral_sq (P := P) GU FU hGUm hFUm τ hτ hGUerr' hGU'
  have hErrV := fp81_s21_w2_of_integral_sq (P := P) FV GV hFVm hGVm τ hτ hGVerr
    (by simpa [FV, GV] using hGV)
  have hMid := fp81_s21_lift_wasserstein P F U V K M δ R hK hR hF hU hV
    hgrowth hlip hU6 hV6 hUmom hVmom hUVint hUV hOut
  have htri1 := wassersteinE_triangle 2 (by norm_num) (law P GU) (law P FU) (law P GV)
  have htri2 := wassersteinE_triangle 2 (by norm_num) (law P FU) (law P FV) (law P GV)
  calc
    wassersteinE 2 (law P GU) (law P GV) ≤
        wassersteinE 2 (law P GU) (law P FU) + wassersteinE 2 (law P FU) (law P GV) := htri1
    _ ≤ ENNReal.ofReal τ + (wassersteinE 2 (law P FU) (law P FV) +
        wassersteinE 2 (law P FV) (law P GV)) := by
      gcongr
    _ ≤ ENNReal.ofReal τ + (ENNReal.ofReal (Real.sqrt
        (K ^ 2 * ((1 + 2 * R) ^ 2 * (2 * R) * δ + 64 * (1 + M) / R ^ 2))) +
        ENNReal.ofReal τ) := by gcongr
    _ = ENNReal.ofReal (2 * τ) + ENNReal.ofReal (Real.sqrt
        (K ^ 2 * ((1 + 2 * R) ^ 2 * (2 * R) * δ + 64 * (1 + M) / R ^ 2))) := by
      calc
        _ = (ENNReal.ofReal τ + ENNReal.ofReal τ) + ENNReal.ofReal (Real.sqrt
            (K ^ 2 * ((1 + 2 * R) ^ 2 * (2 * R) * δ + 64 * (1 + M) / R ^ 2))) := by ac_rfl
        _ = ENNReal.ofReal (2 * τ) + ENNReal.ofReal (Real.sqrt
            (K ^ 2 * ((1 + 2 * R) ^ 2 * (2 * R) * δ + 64 * (1 + M) / R ^ 2))) := by
          rw [← ENNReal.ofReal_add hτ hτ]
          rw [show τ + τ = 2 * τ by ring]

theorem fp81_s21_center_L2
    {Ω Y : Type*} [MeasurableSpace Ω] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [CompleteSpace Y] {P : Measure Ω} [IsProbabilityMeasure P] (A B : Ω → Y)
    (hA : MemLp A 2 P) (hB : MemLp B 2 P)
    (hAi : Integrable A P) (hBi : Integrable B P) :
    eLpNorm (fun ω => (A ω - ∫ ω', A ω' ∂P) - (B ω - ∫ ω', B ω' ∂P)) 2 P ≤
      2 * eLpNorm (fun ω => A ω - B ω) 2 P := by
  let D : Ω → Y := fun ω => A ω - B ω
  have hD : MemLp D 2 P := hA.sub hB
  have hDi : Integrable D P := hAi.sub hBi
  have hmean : (∫ ω, A ω ∂P) - (∫ ω, B ω ∂P) = ∫ ω, D ω ∂P := by
    exact (integral_sub hAi hBi).symm
  have heq : (fun ω => (A ω - ∫ ω', A ω' ∂P) - (B ω - ∫ ω', B ω' ∂P)) =
      fun ω => D ω - ∫ ω', D ω' ∂P := by
    funext ω
    simp only [D]
    rw [← hmean]
    abel
  have hmeanBound : ‖∫ ω, D ω ∂P‖ₑ ≤ eLpNorm D 2 P := by
    calc
      ‖∫ ω, D ω ∂P‖ₑ ≤ ∫⁻ ω, ‖D ω‖ₑ ∂P := enorm_integral_le_lintegral_enorm D
      _ = eLpNorm D 1 P := (eLpNorm_one_eq_lintegral_enorm hD.aestronglyMeasurable).symm
      _ ≤ eLpNorm D 2 P := eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
  have hconst : eLpNorm (fun _ : Ω => ∫ ω, D ω ∂P) 2 P ≤ eLpNorm D 2 P := by
    rw [eLpNorm_const _ (by norm_num : (2 : ℝ≥0∞) ≠ 0) (IsProbabilityMeasure.ne_zero P)]
    simp only [measure_univ, ENNReal.one_rpow, mul_one]
    exact hmeanBound
  rw [heq]
  calc
    eLpNorm (fun ω => D ω - ∫ ω', D ω' ∂P) 2 P ≤
        eLpNorm D 2 P + eLpNorm (fun _ : Ω => ∫ ω, D ω ∂P) 2 P :=
      eLpNorm_sub_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    _ ≤ eLpNorm D 2 P + eLpNorm D 2 P := add_le_add le_rfl hconst
    _ = 2 * eLpNorm D 2 P := by ring

end HRS.Fp81.S21

#print axioms HRS.Fp81.S21.fp81_s21_lift_L2
#print axioms HRS.Fp81.S21.fp81_s21_lift_wasserstein
#print axioms HRS.Fp81.S21.fp81_s21_lift_total
#print axioms HRS.Fp81.S21.fp81_s21_center_L2
