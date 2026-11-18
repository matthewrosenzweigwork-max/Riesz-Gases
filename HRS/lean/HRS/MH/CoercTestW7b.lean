import Mathlib
import HRS.Whole.AppendixALemmas
import HRS.MH.CoercLowerDefs
import HRS.MH.CoercLowerFinal
import HRS.MH.CoercTestSpecDefs
import HRS.MH.CoercTestW1
import HRS.MH.CoercTestW2
import HRS.MH.CoercTestW3
import HRS.MH.CoercTestW4
import HRS.MH.CoercTestW5
import HRS.MH.CoercTestW7a

/-!
# CoercTest W7b: `pair_le_qform_gTs`

Statement copied verbatim from `HRS/MH/CoercTestSpec.lean`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators FourierTransform

namespace HRS.MH.CoercTest

open HRS.MH.CoercLower

variable {d N : ℕ}

/-- Key estimate: the dual pairing with `uMol (2t)` is bounded by the spectral quantity. -/
lemma p_wt7b_key (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {c : ℝ} (hc : 0 < c)
    (hM : ∀ T : ℝ, 0 < T → ∀ ξ : Euc d, ξ ≠ 0 →
      c * (2 * Real.pi * ‖ξ‖) ^ (-((d : ℝ) - s)) * Real.exp (-2 * Real.pi ^ 2 * ‖ξ‖ ^ 2 / T) ≤
        Mhat d s T ξ)
    {t : ℝ} (ht : 0 < t) (ht1 : 1 ≤ 2 * t) {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ)
    (hlog : s = 0 → Integrable (fun x : Euc d => Real.log (2 + ‖x‖)) (HRS.Whole.withDensityReal ρ))
    (hN : 1 ≤ N) (X : HRS.Whole.EucConfig d N) {ψ : Euc d → ℝ}
    (hψ : HRS.Whole.AppendixALemmas.HasFiniteHomSobolevRd (((d : ℝ) - s) / 2) ψ) :
    |∫ z, ψ z * uMol (2 * t) X ρ z| ≤
      HRS.Whole.AppendixALemmas.homSobolevRd (((d : ℝ) - s) / 2) ψ *
        Real.sqrt (c⁻¹ * Qform (gTs d s (2 * t)) X ρ) := by
  have ha : 0 < ((d : ℝ) - s) / 2 := by
    have : (s : ℝ) < d := hsd
    linarith
  obtain ⟨⟨hint, hmem⟩, hF⟩ := fourierL2_gaussU hd ht hρ X
  obtain ⟨hspecI, hspecQ⟩ := qform_spectral hd hs0 hsd ht1 hρ hlog hN X
  have hνc := continuous_nuHat hρ X
  set U := gaussU t X ρ with hU
  set r : ℝ := (Real.pi / (2 * t)) ^ ((d : ℝ) / 2) with hr
  have hr0 : 0 < r := by positivity
  set E : Euc d → ℝ := fun ξ => Real.exp (-Real.pi ^ 2 * ‖ξ‖ ^ 2 / (2 * t)) with hE
  set w : Euc d → ℝ := fun ξ => (2 * Real.pi * ‖ξ‖) ^ (-(2 * (((d : ℝ) - s) / 2))) with hw
  set g0 : Euc d → ℝ := fun ξ => w ξ * (E ξ ^ 2 * ‖nuHat X ρ ξ‖ ^ 2) with hg0
  have hexp : ∀ ξ : Euc d, E ξ ^ 2 = Real.exp (-2 * Real.pi ^ 2 * ‖ξ‖ ^ 2 / (2 * t)) := by
    intro ξ
    simp only [hE]
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hw0 : ∀ ξ, 0 ≤ w ξ := fun ξ => Real.rpow_nonneg (by positivity) _
  have hdpos : (d : ℝ) - s ≠ 0 := by
    have : (s : ℝ) < d := hsd
    linarith
  -- pointwise bound
  have hbound : ∀ ξ : Euc d, g0 ξ ≤ c⁻¹ * (‖nuHat X ρ ξ‖ ^ 2 * Mhat d s (2 * t) ξ) := by
    intro ξ
    by_cases hξ : ξ = 0
    · subst hξ
      have : w 0 = 0 := by
        simp only [hw, norm_zero, mul_zero]
        apply Real.zero_rpow
        intro h
        apply hdpos
        linarith
      simp only [hg0, this, zero_mul]
      have := Mhat_nonneg (d := d) hs0 (2 * t) 0
      positivity
    · have h1 := hM (2 * t) (by positivity) ξ hξ
      have h2 : -(2 * (((d : ℝ) - s) / 2)) = -((d : ℝ) - s) := by ring
      have h3 : w ξ * E ξ ^ 2 ≤ c⁻¹ * Mhat d s (2 * t) ξ := by
        have h5 : c * (w ξ * E ξ ^ 2) ≤ Mhat d s (2 * t) ξ := by
          rw [hexp]
          simp only [hw, h2]
          calc c * ((2 * Real.pi * ‖ξ‖) ^ (-((d : ℝ) - s)) *
                Real.exp (-2 * Real.pi ^ 2 * ‖ξ‖ ^ 2 / (2 * t)))
              = c * (2 * Real.pi * ‖ξ‖) ^ (-((d : ℝ) - s)) *
                Real.exp (-2 * Real.pi ^ 2 * ‖ξ‖ ^ 2 / (2 * t)) := by ring
            _ ≤ _ := h1
        rw [inv_mul_eq_div, le_div_iff₀ hc, mul_comm _ c]
        exact h5
      have h4 := mul_le_mul_of_nonneg_right h3 (sq_nonneg ‖nuHat X ρ ξ‖)
      calc g0 ξ = w ξ * E ξ ^ 2 * ‖nuHat X ρ ξ‖ ^ 2 := by simp only [hg0]; ring
        _ ≤ c⁻¹ * Mhat d s (2 * t) ξ * ‖nuHat X ρ ξ‖ ^ 2 := h4
        _ = _ := by ring
  have hg0m : Measurable g0 := by
    have hn : Measurable (nuHat X ρ) := hνc.measurable
    simp only [hg0, hw, hE]
    fun_prop
  have hg0nn : ∀ ξ, 0 ≤ g0 ξ := fun ξ => by
    simp only [hg0]
    have := hw0 ξ
    positivity
  have hg0I : Integrable g0 := by
    refine Integrable.mono' (hspecI.const_mul c⁻¹) hg0m.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_of_nonneg (hg0nn ξ)]
    exact hbound ξ
  have hae : ∀ᵐ ξ : Euc d ∂volume, r ^ 2 * g0 ξ =
      w ξ * ‖HRS.PDE.ToolboxRd.fourierL2 U ξ‖ ^ 2 := by
    filter_upwards [hF] with ξ hξ
    rw [hξ, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    simp only [hg0]
    ring
  have hI : Integrable fun ξ : Euc d =>
      (2 * Real.pi * ‖ξ‖) ^ (-(2 * (((d : ℝ) - s) / 2))) *
        ‖HRS.PDE.ToolboxRd.fourierL2 U ξ‖ ^ 2 := (hg0I.const_mul (r ^ 2)).congr hae
  have hdual := duality_hom hd ha hψ hmem hI
  have hint_eq : ∫ ξ : Euc d, (2 * Real.pi * ‖ξ‖) ^ (-(2 * (((d : ℝ) - s) / 2))) *
      ‖HRS.PDE.ToolboxRd.fourierL2 U ξ‖ ^ 2 = r ^ 2 * ∫ ξ, g0 ξ := by
    rw [← integral_const_mul]
    exact (integral_congr_ae hae).symm
  have hle : ∫ ξ, g0 ξ ≤ c⁻¹ * Qform (gTs d s (2 * t)) X ρ := by
    rw [hspecQ, ← integral_const_mul]
    exact integral_mono hg0I (hspecI.const_mul c⁻¹) hbound
  -- scaling
  have hK : uMol (2 * t) X ρ = fun z => (2 * t / Real.pi) ^ ((d : ℝ) / 2) * U z :=
    uMol_eq_gaussU ht X ρ
  have hKr : (2 * t / Real.pi) ^ ((d : ℝ) / 2) * r = 1 := by
    rw [hr, ← Real.mul_rpow (by positivity) (by positivity)]
    have : 2 * t / Real.pi * (Real.pi / (2 * t)) = 1 := by
      field_simp
    rw [this, Real.one_rpow]
  have hK0 : 0 ≤ (2 * t / Real.pi) ^ ((d : ℝ) / 2) := by positivity
  have hscale : ∫ z, ψ z * uMol (2 * t) X ρ z =
      (2 * t / Real.pi) ^ ((d : ℝ) / 2) * ∫ z, ψ z * U z := by
    rw [hK, ← integral_const_mul]
    congr 1
    ext z
    ring
  rw [hscale, abs_mul, abs_of_nonneg hK0]
  have hsq : Real.sqrt (r ^ 2 * ∫ ξ, g0 ξ) ≤ r * Real.sqrt (c⁻¹ * Qform (gTs d s (2 * t)) X ρ) := by
    rw [Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr0.le]
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hle) hr0.le
  have hhom0 : 0 ≤ HRS.Whole.AppendixALemmas.homSobolevRd (((d : ℝ) - s) / 2) ψ := Real.sqrt_nonneg _
  rw [hint_eq] at hdual
  calc (2 * t / Real.pi) ^ ((d : ℝ) / 2) * |∫ z, ψ z * U z|
      ≤ (2 * t / Real.pi) ^ ((d : ℝ) / 2) * (HRS.Whole.AppendixALemmas.homSobolevRd
          (((d : ℝ) - s) / 2) ψ * (r * Real.sqrt (c⁻¹ * Qform (gTs d s (2 * t)) X ρ))) :=
        mul_le_mul_of_nonneg_left (hdual.trans (mul_le_mul_of_nonneg_left hsq hhom0)) hK0
    _ = _ := by
        have := hKr
        calc _ = ((2 * t / Real.pi) ^ ((d : ℝ) / 2) * r) * (HRS.Whole.AppendixALemmas.homSobolevRd
          (((d : ℝ) - s) / 2) ψ * Real.sqrt (c⁻¹ * Qform (gTs d s (2 * t)) X ρ)) := by ring
          _ = _ := by rw [this, one_mul]

/-- [W7b] Test bound in terms of `Qform gT` (no energy yet): for `T ≥ 1`,
`|(μ_N - ρ)(ψ)| ≤ C L T^{-1/2} + C ‖ψ‖_{Ḣ^{(d-s)/2}} (Qform gT)^{1/2}`, `C = C(d,s)`.
Route: `u = uMol T X ρ = (T/π)^{d/2} gaussU (T/2)`; W5b with `b = T`; W1b gives `fourierL2 u = e^{-π²‖ξ‖²/T} ν̂` a.e.
and `u ∈ L²`; W3c bounds the weight `(2π‖ξ‖)^{-2a} e^{-2π²‖ξ‖²/T} ≤ c⁻¹ M_T` so `hI` of W4 follows from W7a
(`Integrable.mono'`); W4; W7a identifies the integral with `Qform gT`. -/
theorem pair_le_qform_gTs (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T → ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ →
      (s = 0 → Integrable (fun x : Euc d => Real.log (2 + ‖x‖)) (HRS.Whole.withDensityReal ρ)) →
      ∀ N : ℕ, 1 ≤ N → ∀ X : HRS.Whole.EucConfig d N,
      ∀ (ψ : Euc d → ℝ) (L : ℝ), 0 ≤ L → HRS.PDE.ToolboxRd.IsLipschitz L ψ → HasCompactSupport ψ →
        HRS.Whole.AppendixALemmas.HasFiniteHomSobolevRd (((d : ℝ) - s) / 2) ψ →
          |HRS.Whole.pair (HRS.Whole.empirical X) ψ - HRS.Whole.pair (HRS.Whole.withDensityReal ρ) ψ| ≤
            C * L * T ^ (-(1 / 2 : ℝ)) +
              C * HRS.Whole.AppendixALemmas.homSobolevRd (((d : ℝ) - s) / 2) ψ *
                Real.sqrt (Qform (gTs d s T) X ρ) := by
  obtain ⟨C1, hC1, hmol⟩ := mollify_error (d := d) hd
  obtain ⟨c, hc, hM⟩ := Mhat_lower hd hs0 hsd
  refine ⟨max C1 (Real.sqrt c⁻¹), lt_max_of_lt_left hC1, ?_⟩
  intro T hT ρ hρ hlog N hN X ψ L hL hLip hcs hψ
  have hT0 : 0 < T := by linarith
  have h1 := hmol T hT0 ρ hρ N X hN ψ L hL hLip hcs
  have h2T : 2 * (T / 2) = T := by ring
  have hkey := p_wt7b_key hd hs0 hsd hc hM (t := T / 2) (by positivity) (by rw [h2T]; exact hT)
    hρ hlog hN X hψ
  rw [h2T] at hkey
  set P := HRS.Whole.pair (HRS.Whole.empirical X) ψ - HRS.Whole.pair (HRS.Whole.withDensityReal ρ) ψ
  set I := ∫ z, ψ z * uMol T X ρ z
  have h3 : |P| ≤ |P - I| + |I| := by
    calc |P| = |(P - I) + I| := by ring_nf
      _ ≤ _ := abs_add_le _ _
  have hhom0 : 0 ≤ HRS.Whole.AppendixALemmas.homSobolevRd (((d : ℝ) - s) / 2) ψ := Real.sqrt_nonneg _
  have hT2 : 0 ≤ T ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hT0.le _
  have hQ0 : 0 ≤ Real.sqrt (Qform (gTs d s T) X ρ) := Real.sqrt_nonneg _
  have hsplit : Real.sqrt (c⁻¹ * Qform (gTs d s T) X ρ) =
      Real.sqrt c⁻¹ * Real.sqrt (Qform (gTs d s T) X ρ) := Real.sqrt_mul (inv_nonneg.mpr hc.le) _
  have hA : C1 * L * T ^ (-(1 / 2 : ℝ)) ≤ max C1 (Real.sqrt c⁻¹) * L * T ^ (-(1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hL) hT2
  have hB : Real.sqrt c⁻¹ * Real.sqrt (Qform (gTs d s T) X ρ) *
      HRS.Whole.AppendixALemmas.homSobolevRd (((d : ℝ) - s) / 2) ψ ≤
      max C1 (Real.sqrt c⁻¹) * HRS.Whole.AppendixALemmas.homSobolevRd (((d : ℝ) - s) / 2) ψ *
        Real.sqrt (Qform (gTs d s T) X ρ) := by
    have := mul_le_mul_of_nonneg_right (le_max_right C1 (Real.sqrt c⁻¹))
      (mul_nonneg hhom0 hQ0)
    nlinarith [this]
  rw [hsplit] at hkey
  calc |P| ≤ |P - I| + |I| := h3
    _ ≤ C1 * L * T ^ (-(1 / 2 : ℝ)) + HRS.Whole.AppendixALemmas.homSobolevRd (((d : ℝ) - s) / 2) ψ *
        (Real.sqrt c⁻¹ * Real.sqrt (Qform (gTs d s T) X ρ)) := add_le_add h1 hkey
    _ ≤ _ := by nlinarith [hA, hB]

end HRS.MH.CoercTest
