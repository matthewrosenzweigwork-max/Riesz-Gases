import Mathlib

/-!
# S8.2 observed-time layer, packet T8A.C14: normalization and absorption of the unpinned `L^∞` error

A probability density `f ≤ K` with `log f = ℓ + v`, `|v| ≤ αD + ε` (`D = ‖f - 1‖_∞`) satisfies `|ℓ| ≤ αD + ε` and
`‖f - 1‖_∞ ≤ 2Kε/(1 - 2Kα)` once `2Kα < 1`.  Statement of the packet `R26-T8A.C14`, which is self-contained.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T8A

theorem r26t8a_c14_lip (K y : ℝ) (hK : 1 ≤ K) (hy : 0 < y) (hyK : y ≤ K) :
    |y - 1| ≤ K * |Real.log y| := by
  rcases le_total 1 y with h1 | h1
  · have h2 : y - 1 ≤ y * Real.log y := by
      have := Real.one_sub_inv_le_log_of_pos hy
      have h3 : y * (1 - y⁻¹) = y - 1 := by field_simp
      calc y - 1 = y * (1 - y⁻¹) := h3.symm
        _ ≤ y * Real.log y := mul_le_mul_of_nonneg_left this hy.le
    have hl : 0 ≤ Real.log y := Real.log_nonneg h1
    rw [abs_of_nonneg (by linarith), abs_of_nonneg hl]
    calc y - 1 ≤ y * Real.log y := h2
      _ ≤ K * Real.log y := mul_le_mul_of_nonneg_right hyK hl
  · have h2 := Real.log_le_sub_one_of_pos hy
    have hl : Real.log y ≤ 0 := Real.log_nonpos hy.le h1
    rw [abs_of_nonpos (by linarith), abs_of_nonpos hl]
    nlinarith [neg_nonneg.2 hl]

theorem r26t8a_log_absorption {E : Type*} [MeasurableSpace E]
    (mu : Measure E) [IsProbabilityMeasure mu] (f v : E → ℝ) (ell D eps K alpha : ℝ)
    (hD : 0 ≤ D) (heps : 0 ≤ eps) (hK : 0 < K) (halpha : 0 ≤ alpha)
    (hsmall : 2*K*alpha < 1) (hfm : Measurable f) (hfi : Integrable f mu)
    (hf1 : ∫ x, f x ∂mu = 1)
    (hDdef : D = (eLpNorm (fun x => f x-1) ∞ mu).toReal)
    (hfb : ∀ᵐ x ∂mu, 0 < f x ∧ f x ≤ K ∧ |f x-1| ≤ D)
    (hv : ∀ᵐ x ∂mu, |v x| ≤ alpha*D+eps ∧ Real.log (f x)=ell+v x) :
    |ell| ≤ alpha*D+eps ∧
      eLpNorm (fun x => f x-1) ∞ mu ≤ ENNReal.ofReal (2*K*eps/(1-2*K*alpha)) := by
  set m : ℝ := alpha * D + eps with hm
  have hm0 : 0 ≤ m := by positivity
  have hfexp : ∀ᵐ x ∂mu, f x = Real.exp (ell + v x) := by
    filter_upwards [hfb, hv] with x h1 h2
    rw [← h2.2, Real.exp_log h1.1]
  -- two-sided bound on `ell`
  have hup : ∀ᵐ x ∂mu, f x ≤ Real.exp (ell + m) := by
    filter_upwards [hfexp, hv] with x h1 h2
    rw [h1]
    exact Real.exp_le_exp.2 (by linarith [(abs_le.1 h2.1).2])
  have hlo : ∀ᵐ x ∂mu, Real.exp (ell - m) ≤ f x := by
    filter_upwards [hfexp, hv] with x h1 h2
    rw [h1]
    exact Real.exp_le_exp.2 (by linarith [(abs_le.1 h2.1).1])
  have hint1 : 1 ≤ Real.exp (ell + m) := by
    have := integral_mono_ae hfi (integrable_const (Real.exp (ell + m))) hup
    simpa [hf1] using this
  have hint2 : Real.exp (ell - m) ≤ 1 := by
    have := integral_mono_ae (integrable_const (Real.exp (ell - m))) hfi hlo
    simpa [hf1] using this
  have hell : |ell| ≤ m := by
    rw [abs_le]
    constructor
    · have := Real.exp_le_exp.1 (show Real.exp 0 ≤ Real.exp (ell + m) by simpa using hint1)
      linarith
    · have := Real.exp_le_exp.1 (show Real.exp (ell - m) ≤ Real.exp 0 by simpa using hint2)
      linarith
  have hK1 : 1 ≤ K := by
    have hle : ∀ᵐ x ∂mu, f x ≤ K := hfb.mono fun x h => h.2.1
    have := integral_mono_ae hfi (integrable_const K) hle
    simpa [hf1] using this
  -- pointwise bound on `f - 1`
  have hpt : ∀ᵐ x ∂mu, ‖f x - 1‖ ≤ 2 * K * m := by
    filter_upwards [hfb, hv] with x h1 h2
    have := r26t8a_c14_lip K (f x) hK1 h1.1 h1.2.1
    rw [Real.norm_eq_abs, h2.2] at *
    calc |f x - 1| ≤ K * |ell + v x| := by rw [← h2.2]; exact this
      _ ≤ K * (m + m) := by
          gcongr
          exact (abs_add_le _ _).trans (add_le_add hell h2.1)
      _ = 2 * K * m := by ring
  have hmeas : AEStronglyMeasurable (fun x => f x - 1) mu :=
    ((hfm.sub measurable_const).aestronglyMeasurable)
  have hess : eLpNorm (fun x => f x - 1) ∞ mu ≤ ENNReal.ofReal (2 * K * m) := by
    rw [eLpNorm_exponent_top hmeas]
    exact eLpNormEssSup_le_of_ae_bound hpt
  have hDle : D ≤ 2 * K * m :=
    hDdef ▸ ENNReal.toReal_le_of_le_ofReal (by positivity) hess
  have hD2 : D ≤ 2 * K * eps / (1 - 2 * K * alpha) := by
    have hpos : 0 < 1 - 2 * K * alpha := by linarith
    rw [le_div_iff₀ hpos]
    rw [hm] at hDle
    nlinarith
  refine ⟨hell, ?_⟩
  have hfin : eLpNorm (fun x => f x - 1) ∞ mu ≤ ENNReal.ofReal D := by
    rw [eLpNorm_exponent_top hmeas]
    exact eLpNormEssSup_le_of_ae_bound (hfb.mono fun x h => by rw [Real.norm_eq_abs]; exact h.2.2)
  exact hfin.trans (ENNReal.ofReal_le_ofReal hD2)

end HRS.MS.R26T8A

end
