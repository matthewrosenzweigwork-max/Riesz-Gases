import HRS.MS.Fp81S21RSValue4

/-! The expected signed correction derived from a `WindowRS` record. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter
open scoped BigOperators

namespace HRS.Fp81.S21

/-- Generic expected correction `-∫ dval + (1/2) * ∫ jval`. -/
def fp81s21_WindowRS_corr
    {Ω ED EJ : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup ED] [NormedSpace ℝ ED] [CompleteSpace ED]
    [NormedAddCommGroup EJ] [NormedSpace ℝ EJ] [CompleteSpace EJ]
    {μ : Measure Ω} {T : ℝ}
    {Ad : Ω → ℝ → ED →L[ℝ] ℝ} {Fd : Ω → ℝ → ED}
    {Aj : Ω → ℝ → EJ →L[ℝ] ℝ} {Fj : Ω → ℝ → EJ}
    (W : fp81s21_WindowRS μ T Ad Fd Aj Fj) (q r : ℝ) : ℝ :=
  -(∫ ω, W.drift.value q r ω ∂μ) +
    (1 / 2 : ℝ) * (∫ ω, W.covariance.value q r ω ∂μ)

/-- The pointwise sum of the drift and half covariance variation majorants. -/
def fp81s21_WindowRS_corr_majorant
    {Ω ED EJ : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup ED] [NormedSpace ℝ ED] [CompleteSpace ED]
    [NormedAddCommGroup EJ] [NormedSpace ℝ EJ] [CompleteSpace EJ]
    {μ : Measure Ω} {T : ℝ}
    {Ad : Ω → ℝ → ED →L[ℝ] ℝ} {Fd : Ω → ℝ → ED}
    {Aj : Ω → ℝ → EJ →L[ℝ] ℝ} {Fj : Ω → ℝ → EJ}
    (W : fp81s21_WindowRS μ T Ad Fd Aj Fj) (q r : ℝ) (ω : Ω) : ℝ :=
  W.drift.majorant q r ω + (1 / 2 : ℝ) * W.covariance.majorant q r ω

/-- The majorant defining the signed correction is integrable on each window. -/
theorem fp81s21_WindowRS_corr_majorant_integrable
    {Ω ED EJ : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup ED] [NormedSpace ℝ ED] [CompleteSpace ED]
    [NormedAddCommGroup EJ] [NormedSpace ℝ EJ] [CompleteSpace EJ]
    {μ : Measure Ω} {T : ℝ}
    {Ad : Ω → ℝ → ED →L[ℝ] ℝ} {Fd : Ω → ℝ → ED}
    {Aj : Ω → ℝ → EJ →L[ℝ] ℝ} {Fj : Ω → ℝ → EJ}
    (W : fp81s21_WindowRS μ T Ad Fd Aj Fj)
    {q r : ℝ} (hq : 0 ≤ q) (hqr : q ≤ r) (hr : r ≤ T) :
    Integrable (fp81s21_WindowRS_corr_majorant W q r) μ := by
  exact (W.drift.majorant_integrable q r hq hqr hr).add
    ((W.covariance.majorant_integrable q r hq hqr hr).const_mul (1 / 2 : ℝ))

/-- Additivity of the expected signed correction over adjacent windows. -/
theorem fp81s21_WindowRS_corr_add
    {Ω ED EJ : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup ED] [NormedSpace ℝ ED] [CompleteSpace ED]
    [NormedAddCommGroup EJ] [NormedSpace ℝ EJ] [CompleteSpace EJ]
    {μ : Measure Ω} {T : ℝ}
    {Ad : Ω → ℝ → ED →L[ℝ] ℝ} {Fd : Ω → ℝ → ED}
    {Aj : Ω → ℝ → EJ →L[ℝ] ℝ} {Fj : Ω → ℝ → EJ}
    (W : fp81s21_WindowRS μ T Ad Fd Aj Fj)
    {q s r : ℝ} (hq : 0 ≤ q) (hqs : q ≤ s) (hsr : s ≤ r) (hr : r ≤ T) :
    fp81s21_WindowRS_corr W q r =
      fp81s21_WindowRS_corr W q s + fp81s21_WindowRS_corr W s r := by
  have hd : (∫ ω, W.drift.value q r ω ∂μ) =
      (∫ ω, W.drift.value q s ω ∂μ) + (∫ ω, W.drift.value s r ω ∂μ) := by
    calc
      (∫ ω, W.drift.value q r ω ∂μ) =
          ∫ ω, W.drift.value q s ω + W.drift.value s r ω ∂μ :=
        integral_congr_ae (W.drift.value_add q s r hq hqs hsr hr)
      _ = _ := integral_add
        (W.drift.value_integrable q s hq hqs (hsr.trans hr))
        (W.drift.value_integrable s r (le_trans hq hqs) hsr hr)
  have hj : (∫ ω, W.covariance.value q r ω ∂μ) =
      (∫ ω, W.covariance.value q s ω ∂μ) + (∫ ω, W.covariance.value s r ω ∂μ) := by
    calc
      (∫ ω, W.covariance.value q r ω ∂μ) =
          ∫ ω, W.covariance.value q s ω + W.covariance.value s r ω ∂μ :=
        integral_congr_ae (W.covariance.value_add q s r hq hqs hsr hr)
      _ = _ := integral_add
        (W.covariance.value_integrable q s hq hqs (hsr.trans hr))
        (W.covariance.value_integrable s r (le_trans hq hqs) hsr hr)
  simp only [fp81s21_WindowRS_corr, hd, hj]
  ring

/-- The signed correction vanishes on a zero-length interval. -/
theorem fp81s21_WindowRS_corr_zero
    {Ω ED EJ : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup ED] [NormedSpace ℝ ED] [CompleteSpace ED]
    [NormedAddCommGroup EJ] [NormedSpace ℝ EJ] [CompleteSpace EJ]
    {μ : Measure Ω} {T : ℝ}
    {Ad : Ω → ℝ → ED →L[ℝ] ℝ} {Fd : Ω → ℝ → ED}
    {Aj : Ω → ℝ → EJ →L[ℝ] ℝ} {Fj : Ω → ℝ → EJ}
    (W : fp81s21_WindowRS μ T Ad Fd Aj Fj)
    {q : ℝ} (hq : 0 ≤ q) (hqT : q ≤ T) :
    fp81s21_WindowRS_corr W q q = 0 := by
  have hd : (∫ ω, W.drift.value q q ω ∂μ) = 0 := by
    calc
      (∫ ω, W.drift.value q q ω ∂μ) = ∫ _ω, (0 : ℝ) ∂μ :=
        integral_congr_ae (W.drift.value_zero q hq hqT)
      _ = 0 := by simp
  have hj : (∫ ω, W.covariance.value q q ω ∂μ) = 0 := by
    calc
      (∫ ω, W.covariance.value q q ω ∂μ) = ∫ _ω, (0 : ℝ) ∂μ :=
        integral_congr_ae (W.covariance.value_zero q hq hqT)
      _ = 0 := by simp
  simp [fp81s21_WindowRS_corr, hd, hj]

/-- Bound the correction by the integral of the two exact BV majorants. -/
theorem fp81s21_WindowRS_corr_bound
    {Ω ED EJ : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup ED] [NormedSpace ℝ ED] [CompleteSpace ED]
    [NormedAddCommGroup EJ] [NormedSpace ℝ EJ] [CompleteSpace EJ]
    {μ : Measure Ω} {T : ℝ}
    {Ad : Ω → ℝ → ED →L[ℝ] ℝ} {Fd : Ω → ℝ → ED}
    {Aj : Ω → ℝ → EJ →L[ℝ] ℝ} {Fj : Ω → ℝ → EJ}
    (W : fp81s21_WindowRS μ T Ad Fd Aj Fj)
    {q r : ℝ} (hq : 0 ≤ q) (hqr : q ≤ r) (hr : r ≤ T) :
    |fp81s21_WindowRS_corr W q r| ≤
      ∫ ω, fp81s21_WindowRS_corr_majorant W q r ω ∂μ := by
  let md := W.drift.majorant q r
  let mj := W.covariance.majorant q r
  have hId := W.drift.value_integrable q r hq hqr hr
  have hIj := W.covariance.value_integrable q r hq hqr hr
  have hMd := W.drift.majorant_integrable q r hq hqr hr
  have hMj := W.covariance.majorant_integrable q r hq hqr hr
  have hAd : Integrable (fun ω => |W.drift.value q r ω|) μ := by
    simpa only [Real.norm_eq_abs] using hId.norm
  have hAj : Integrable (fun ω => |W.covariance.value q r ω|) μ := by
    simpa only [Real.norm_eq_abs] using hIj.norm
  have hd : |∫ ω, W.drift.value q r ω ∂μ| ≤ ∫ ω, md ω ∂μ := by
    exact (abs_integral_le_integral_abs (f := W.drift.value q r)).trans
      (integral_mono_ae hAd hMd (W.drift.value_bound q r hq hqr hr))
  have hj : |∫ ω, W.covariance.value q r ω ∂μ| ≤ ∫ ω, mj ω ∂μ := by
    exact (abs_integral_le_integral_abs (f := W.covariance.value q r)).trans
      (integral_mono_ae hAj hMj (W.covariance.value_bound q r hq hqr hr))
  have hMjHalf : Integrable (fun ω => (1 / 2 : ℝ) * mj ω) μ := hMj.const_mul _
  have hsum : Integrable (fun ω => md ω + (1 / 2 : ℝ) * mj ω) μ := hMd.add hMjHalf
  have hMajorantIntegral :
      (∫ ω, md ω + (1 / 2 : ℝ) * mj ω ∂μ) =
        (∫ ω, md ω ∂μ) + (1 / 2 : ℝ) * (∫ ω, mj ω ∂μ) := by
    rw [integral_add hMd hMjHalf, integral_const_mul]
  calc
    |fp81s21_WindowRS_corr W q r| ≤
        |∫ ω, W.drift.value q r ω ∂μ| +
          (1 / 2 : ℝ) * |∫ ω, W.covariance.value q r ω ∂μ| := by
      calc
        |-(∫ ω, W.drift.value q r ω ∂μ) +
            (1 / 2 : ℝ) * (∫ ω, W.covariance.value q r ω ∂μ)|
            ≤ |-(∫ ω, W.drift.value q r ω ∂μ)| +
              |(1 / 2 : ℝ) * (∫ ω, W.covariance.value q r ω ∂μ)| := abs_add_le _ _
        _ = |∫ ω, W.drift.value q r ω ∂μ| +
              (1 / 2 : ℝ) * |∫ ω, W.covariance.value q r ω ∂μ| := by simp
    _ ≤ (∫ ω, md ω ∂μ) + (1 / 2 : ℝ) * (∫ ω, mj ω ∂μ) := by
      exact add_le_add hd (mul_le_mul_of_nonneg_left hj (by norm_num))
    _ = ∫ ω, fp81s21_WindowRS_corr_majorant W q r ω ∂μ := by
      simpa [fp81s21_WindowRS_corr_majorant, md, mj] using hMajorantIntegral.symm

#print axioms fp81s21_WindowRS_corr_majorant_integrable
#print axioms fp81s21_WindowRS_corr_add
#print axioms fp81s21_WindowRS_corr_zero
#print axioms fp81s21_WindowRS_corr_bound

end HRS.Fp81.S21

end
