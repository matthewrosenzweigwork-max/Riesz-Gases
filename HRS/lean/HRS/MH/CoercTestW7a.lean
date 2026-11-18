import Mathlib
import HRS.Whole.AppendixALemmas
import HRS.MH.CoercLowerDefs
import HRS.MH.CoercLowerFinal
import HRS.MH.CoercTestSpecDefs
import HRS.MH.CoercTestW1
import HRS.MH.CoercTestW2
import HRS.MH.CoercTestW3

/-!
# CoercTest W7a: `qform_gauss_spectral`, `qform_spectral`

Statements copied verbatim from `HRS/MH/CoercTestSpec.lean`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators FourierTransform

namespace HRS.MH.CoercTest

open HRS.MH.CoercLower

variable {d N : ℕ}

/-- The integrand of the Tonelli step on `(0,∞) × ℝ^d`: `w_s(t) (π/t)^{d/2} e^{-π²‖ξ‖²/t} ‖ν̂(ξ)‖²`. -/
def p_wt7a_F (s : ℝ) (X : HRS.Whole.EucConfig d N) (ρ : Euc d → ℝ) (p : ℝ × Euc d) : ℝ :=
  (wS s p.1 * (Real.pi / p.1) ^ ((d : ℝ) / 2)) *
    (Real.exp (-Real.pi ^ 2 * ‖p.2‖ ^ 2 / p.1) * ‖nuHat X ρ p.2‖ ^ 2)

lemma p_wt7a_F_measurable (s : ℝ) (X : HRS.Whole.EucConfig d N) (ρ : Euc d → ℝ)
    (hν : Measurable (nuHat X ρ)) : Measurable (p_wt7a_F s X ρ) := by
  unfold p_wt7a_F
  have hw : Measurable (fun p : ℝ × Euc d => wS s p.1) := by
    by_cases h : s = 0
    · simp only [wS, h, ite_true]
      fun_prop
    · simp only [wS, h, ite_false]
      fun_prop
  have hn : Measurable (fun p : ℝ × Euc d => ‖nuHat X ρ p.2‖ ^ 2) :=
    ((hν.comp measurable_snd).norm).pow_const 2
  have he : Measurable (fun p : ℝ × Euc d => Real.exp (-Real.pi ^ 2 * ‖p.2‖ ^ 2 / p.1)) := by
    fun_prop
  have hp : Measurable (fun p : ℝ × Euc d => (Real.pi / p.1) ^ ((d : ℝ) / 2)) := by
    fun_prop
  exact (hw.mul hp).mul (he.mul hn)

lemma p_wt7a_F_nonneg {s : ℝ} (hs0 : 0 ≤ s) (X : HRS.Whole.EucConfig d N) (ρ : Euc d → ℝ)
    (t : ℝ) (ξ : Euc d) (ht : 0 < t) : 0 ≤ p_wt7a_F s X ρ (t, ξ) := by
  unfold p_wt7a_F
  exact mul_nonneg (mul_nonneg (p_wt3_wS_nonneg hs0 ht)
      (Real.rpow_nonneg (div_nonneg Real.pi_pos.le ht.le) _))
    (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))

/-- [W2a] Spectral form of the Gaussian quadratic form: `Qform (gaussK t) X ρ = (π/t)^{d/2} ∫ e^{-π²‖ξ‖²/t} |ν̂|² dξ`,
with the integrand integrable.  Proof: `p_wt2_gauss_spectral_of_W1` applied to `fourierL2_gaussU` (W1b). -/
theorem qform_gauss_spectral (hd : 1 ≤ d) {t : ℝ} (ht : 0 < t) {ρ : Euc d → ℝ}
    (hρ : HRS.Whole.IsProbDensity ρ) (hN : 1 ≤ N) (X : HRS.Whole.EucConfig d N) :
    Integrable (fun ξ : Euc d => Real.exp (-Real.pi ^ 2 * ‖ξ‖ ^ 2 / t) * ‖nuHat X ρ ξ‖ ^ 2) ∧
      Qform (HRS.MH.CoercLower.gaussK t) X ρ =
        (Real.pi / t) ^ ((d : ℝ) / 2) * ∫ ξ : Euc d, Real.exp (-Real.pi ^ 2 * ‖ξ‖ ^ 2 / t) * ‖nuHat X ρ ξ‖ ^ 2 :=
  p_wt2_gauss_spectral_of_W1 hd ht hρ hN X (fourierL2_gaussU hd ht hρ X)

/-- [W7a] Spectral form of the truncated form (Tonelli): `‖ν̂‖² M_T` is integrable and
`Qform gT = ∫ ‖ν̂‖² M_T`.  Route: W2b, then W2a for each `t`, and swap `∫_t ∫_ξ` by `lintegral_lintegral_swap`
(nonnegative, jointly measurable, `ν̂` continuous by W1a); finiteness of the `t`-integral is the integrability
of `t ↦ w_s(t) Qform (gaussK t)` coming from `Qform_mix`/W2b. -/
theorem qform_spectral (hd : 1 ≤ d) {s T : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hT : 1 ≤ T) {ρ : Euc d → ℝ}
    (hρ : HRS.Whole.IsProbDensity ρ)
    (hlog : s = 0 → Integrable (fun x : Euc d => Real.log (2 + ‖x‖)) (HRS.Whole.withDensityReal ρ))
    (hN : 1 ≤ N) (X : HRS.Whole.EucConfig d N) :
    Integrable (fun ξ : Euc d => ‖nuHat X ρ ξ‖ ^ 2 * Mhat d s T ξ) ∧
      Qform (gTs d s T) X ρ = ∫ ξ : Euc d, ‖nuHat X ρ ξ‖ ^ 2 * Mhat d s T ξ := by
  have hmix := qform_gTs_mixture hd hs0 hsd hT hρ hlog hN X
  have hFm : Measurable (p_wt7a_F s X ρ) :=
    p_wt7a_F_measurable s X ρ (continuous_nuHat hρ X).measurable
  -- fibrewise identity: the `ξ`-integral of the integrand is the Gaussian term
  have hfib : ∀ t : ℝ, 0 < t →
      ∫ ξ : Euc d, p_wt7a_F s X ρ (t, ξ) = wS s t * Qform (HRS.MH.CoercLower.gaussK t) X ρ := by
    intro t ht
    rw [(qform_gauss_spectral hd ht hρ hN X).2]
    simp only [p_wt7a_F]
    rw [integral_const_mul]
    ring
  -- pointwise identity in `ξ`: the `t`-integral is `‖ν̂‖² M_T`
  have hpt : ∀ ξ : Euc d,
      ∫ t in Set.Ioc (0 : ℝ) T, p_wt7a_F s X ρ (t, ξ) = ‖nuHat X ρ ξ‖ ^ 2 * Mhat d s T ξ := by
    intro ξ
    unfold Mhat
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
    simp only [p_wt7a_F]
    ring
  -- joint integrability on `(0,T] × ℝ^d`
  have hIprod : Integrable (p_wt7a_F s X ρ)
      ((volume.restrict (Set.Ioc (0 : ℝ) T)).prod (volume : Measure (Euc d))) := by
    rw [integrable_prod_iff hFm.aestronglyMeasurable]
    refine ⟨?_, ?_⟩
    · refine (ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ fun t ht => ?_)
      have ht0 : 0 < t := ht.1
      exact (qform_gauss_spectral hd ht0 hρ hN X).1.const_mul
        (wS s t * (Real.pi / t) ^ ((d : ℝ) / 2))
    · refine Integrable.congr hmix.1 ((ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ fun t ht => ?_))
      have ht0 : 0 < t := ht.1
      dsimp only
      rw [← hfib t ht0]
      refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
      exact (Real.norm_of_nonneg (p_wt7a_F_nonneg hs0 X ρ t ξ ht0)).symm
  refine ⟨?_, ?_⟩
  · exact hIprod.integral_prod_right.congr (ae_of_all _ fun ξ => hpt ξ)
  · calc Qform (gTs d s T) X ρ
        = ∫ t in Set.Ioc (0 : ℝ) T, wS s t * Qform (HRS.MH.CoercLower.gaussK t) X ρ := hmix.2
      _ = ∫ t in Set.Ioc (0 : ℝ) T, ∫ ξ : Euc d, p_wt7a_F s X ρ (t, ξ) :=
          setIntegral_congr_fun measurableSet_Ioc fun t ht => (hfib t ht.1).symm
      _ = ∫ ξ : Euc d, ∫ t in Set.Ioc (0 : ℝ) T, p_wt7a_F s X ρ (t, ξ) :=
          integral_integral_swap (f := fun t ξ => p_wt7a_F s X ρ (t, ξ)) hIprod
      _ = ∫ ξ : Euc d, ‖nuHat X ρ ξ‖ ^ 2 * Mhat d s T ξ := integral_congr_ae (ae_of_all _ hpt)

end HRS.MH.CoercTest
