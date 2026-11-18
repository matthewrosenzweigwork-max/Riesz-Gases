import Mathlib
import HRS.Whole.AppendixALemmas
import HRS.MH.CoercLowerDefs
import HRS.MH.CoercLowerFinal
import HRS.MH.CoercTestSpecDefs

/-!
# W4: junk-guarded `Ḣ^a`-duality (proof of `duality_hom` of `HRS/MH/CoercTestSpec.lean`)
-/

noncomputable section

open MeasureTheory
open scoped BigOperators FourierTransform

namespace HRS.MH.CoercTest

open HRS.MH.CoercLower

variable {d N : ℕ}

/-- Cauchy-Schwarz for nonnegative `L²` functions, in `sqrt` form. -/
theorem p_wt4_cs {f g : Euc d → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    ∫ x, f x * g x ≤ Real.sqrt (∫ x, f x ^ 2) * Real.sqrt (∫ x, g x ^ 2) := by
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := (volume : Measure (Euc d)))
    (p := 2) (q := 2) Real.HolderConjugate.two_two (Filter.Eventually.of_forall hf0)
    (Filter.Eventually.of_forall hg0) (by simpa using hf) (by simpa using hg)
  simpa [Real.sqrt_eq_rpow, Real.rpow_two] using h

/-- The weighted function `(2π‖ξ‖)^c ‖û(ξ)‖`. -/
theorem p_wt4_aesm {U : Euc d → ℝ} (hU : MemLp U 2 volume) (c : ℝ) :
    AEStronglyMeasurable
      (fun ξ : Euc d => (2 * Real.pi * ‖ξ‖) ^ c * ‖HRS.PDE.ToolboxRd.fourierL2 U ξ‖) volume := by
  have h1 : Continuous fun ξ : Euc d => (2 * Real.pi * ‖ξ‖) := by fun_prop
  have h2 : Measurable fun ξ : Euc d => (2 * Real.pi * ‖ξ‖) ^ c :=
    h1.measurable.pow_const c
  exact h2.aestronglyMeasurable.mul
    (HRS.PDE.ToolboxRd.FourierAux.aestronglyMeasurable_fourierL2 hU).norm

theorem p_wt4_memLp {U : Euc d → ℝ} (hU : MemLp U 2 volume) (c : ℝ)
    (hI : Integrable fun ξ : Euc d =>
      (2 * Real.pi * ‖ξ‖) ^ (2 * c) * ‖HRS.PDE.ToolboxRd.fourierL2 U ξ‖ ^ 2) :
    MemLp (fun ξ : Euc d => (2 * Real.pi * ‖ξ‖) ^ c * ‖HRS.PDE.ToolboxRd.fourierL2 U ξ‖) 2 volume := by
  rw [memLp_two_iff_integrable_sq (p_wt4_aesm hU c)]
  refine hI.congr (Filter.Eventually.of_forall fun ξ => ?_)
  have hw : 0 ≤ 2 * Real.pi * ‖ξ‖ := by positivity
  simp only
  rw [mul_pow, ← Real.rpow_natCast ((2 * Real.pi * ‖ξ‖) ^ c) 2, ← Real.rpow_mul hw]
  congr 2
  push_cast; ring

/-- `duality_hom` under the extra hypothesis `1 ≤ d` (the statement of `duality_hom` itself is false for `d = 0`). -/
theorem duality_hom (hd : 1 ≤ d) {a : ℝ} (ha : 0 < a) {ψ U : Euc d → ℝ}
    (hψ : HRS.Whole.AppendixALemmas.HasFiniteHomSobolevRd a ψ) (hU : MemLp U 2 volume)
    (hI : Integrable fun ξ : Euc d =>
      (2 * Real.pi * ‖ξ‖) ^ (-(2 * a)) * ‖HRS.PDE.ToolboxRd.fourierL2 U ξ‖ ^ 2) :
    |∫ x, ψ x * U x| ≤ HRS.Whole.AppendixALemmas.homSobolevRd a ψ *
      Real.sqrt (∫ ξ : Euc d, (2 * Real.pi * ‖ξ‖) ^ (-(2 * a)) * ‖HRS.PDE.ToolboxRd.fourierL2 U ξ‖ ^ 2) := by
  obtain ⟨hψ2, hψI⟩ := hψ
  set F := fun ξ : Euc d => (2 * Real.pi * ‖ξ‖) ^ a * ‖HRS.PDE.ToolboxRd.fourierL2 ψ ξ‖ with hF
  set G := fun ξ : Euc d => (2 * Real.pi * ‖ξ‖) ^ (-a) * ‖HRS.PDE.ToolboxRd.fourierL2 U ξ‖ with hG
  have hFm : MemLp F 2 volume := p_wt4_memLp hψ2 a hψI
  have hGm : MemLp G 2 volume := p_wt4_memLp hU (-a) (by simpa using hI)
  have hF0 : ∀ ξ, 0 ≤ F ξ := fun ξ => by simp only [hF]; positivity
  have hG0 : ∀ ξ, 0 ≤ G ξ := fun ξ => by simp only [hG]; positivity
  have hcs := p_wt4_cs hF0 hG0 hFm hGm
  have e1 : ∀ ξ, F ξ ^ 2 = (2 * Real.pi * ‖ξ‖) ^ (2 * a) * ‖HRS.PDE.ToolboxRd.fourierL2 ψ ξ‖ ^ 2 := by
    intro ξ
    have hw : 0 ≤ 2 * Real.pi * ‖ξ‖ := by positivity
    simp only [hF]
    rw [mul_pow, ← Real.rpow_natCast ((2 * Real.pi * ‖ξ‖) ^ a) 2, ← Real.rpow_mul hw]
    congr 2
    push_cast; ring
  have e2 : ∀ ξ, G ξ ^ 2 = (2 * Real.pi * ‖ξ‖) ^ (-(2 * a)) * ‖HRS.PDE.ToolboxRd.fourierL2 U ξ‖ ^ 2 := by
    intro ξ
    have hw : 0 ≤ 2 * Real.pi * ‖ξ‖ := by positivity
    simp only [hG]
    rw [mul_pow, ← Real.rpow_natCast ((2 * Real.pi * ‖ξ‖) ^ (-a)) 2, ← Real.rpow_mul hw]
    congr 2
    push_cast; ring
  -- Parseval
  have hP := HRS.PDE.ToolboxRd.FourierAux.integral_fourierL2_mul_conj hψ2 hU
  have hint := HRS.PDE.ToolboxRd.FourierAux.integrable_fourierL2_mul_conj hψ2 hU
  have h1 : |∫ x, ψ x * U x| ≤ ∫ ξ, ‖HRS.PDE.ToolboxRd.fourierL2 ψ ξ‖ *
      ‖HRS.PDE.ToolboxRd.fourierL2 U ξ‖ := by
    have := norm_integral_le_integral_norm (μ := (volume : Measure (Euc d)))
      (fun ξ => HRS.PDE.ToolboxRd.fourierL2 ψ ξ * (starRingEnd ℂ) (HRS.PDE.ToolboxRd.fourierL2 U ξ))
    rw [hP, Complex.norm_real, Real.norm_eq_abs] at this
    refine this.trans (le_of_eq ?_)
    congr 1; ext ξ
    rw [norm_mul, Complex.norm_conj]
  have h2 : ∫ ξ, ‖HRS.PDE.ToolboxRd.fourierL2 ψ ξ‖ * ‖HRS.PDE.ToolboxRd.fourierL2 U ξ‖ =
      ∫ ξ, F ξ * G ξ := by
    refine integral_congr_ae ?_
    have : ∀ᵐ ξ : Euc d ∂volume, ξ ≠ 0 := by
      haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
      haveI : Nontrivial (Euc d) := inferInstance
      exact Measure.ae_ne volume 0
    filter_upwards [this] with ξ hξ
    have hw : 0 < 2 * Real.pi * ‖ξ‖ := by
      have := norm_pos_iff.mpr hξ
      positivity
    simp only [hF, hG]
    calc _ = ((2 * Real.pi * ‖ξ‖) ^ a * (2 * Real.pi * ‖ξ‖) ^ (-a)) *
          (‖HRS.PDE.ToolboxRd.fourierL2 ψ ξ‖ * ‖HRS.PDE.ToolboxRd.fourierL2 U ξ‖) := by
          rw [← Real.rpow_add hw]; simp
      _ = _ := by ring
  rw [h2] at h1
  refine h1.trans (hcs.trans (le_of_eq ?_))
  unfold HRS.Whole.AppendixALemmas.homSobolevRd
  simp only [e1, e2]
