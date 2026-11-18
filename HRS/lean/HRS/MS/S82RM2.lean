import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Integral

/-!
# S8.2 R02 (S82R), M2: stability of normalized exponential densities (one-change lemma)
For `Phi_i <= M`, `int Phi_i >= -M2` the normalized densities `exp Phi_i / int exp Phi_i` satisfy
`|k1 - k2| <= e^{M2} D + e^{M + 2 M2} int D`, `D = |exp Phi1 - exp Phi2|`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal BigOperators

namespace HRS.MS.S82R

variable {E : Type*} [MeasurableSpace E]

/-- normalized exponential density -/
def s82r_nd (μ : Measure E) (Φ : E → ℝ) (z : E) : ℝ := Real.exp (Φ z) / ∫ y, Real.exp (Φ y) ∂μ

lemma s82r_expint_lower (μ : Measure E) [IsProbabilityMeasure μ] {Φ : E → ℝ} (hΦm : Measurable Φ)
    (hΦi : Integrable Φ μ) {M M2 : ℝ} (hM : ∀ z, Φ z ≤ M) (h2 : -M2 ≤ ∫ z, Φ z ∂μ) :
    Real.exp (-M2) ≤ ∫ y, Real.exp (Φ y) ∂μ ∧ Integrable (fun y => Real.exp (Φ y)) μ := by
  have hexpi : Integrable (fun y => Real.exp (Φ y)) μ := by
    refine Integrable.of_bound (Real.measurable_exp.comp hΦm).aestronglyMeasurable (Real.exp M)
      (ae_of_all _ fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (hM y)
  refine ⟨?_, hexpi⟩
  have hjen : Real.exp (∫ y, Φ y ∂μ) ≤ ∫ y, Real.exp (Φ y) ∂μ :=
    convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
      (ae_of_all _ fun _ => Set.mem_univ _) hΦi hexpi
  exact (Real.exp_le_exp.2 h2).trans hjen

lemma s82r_nd_diff (μ : Measure E) [IsProbabilityMeasure μ] {Φ₁ Φ₂ : E → ℝ}
    (hm₁ : Measurable Φ₁) (hm₂ : Measurable Φ₂) (hi₁ : Integrable Φ₁ μ) (hi₂ : Integrable Φ₂ μ)
    {M M2 : ℝ} (hM₁ : ∀ z, Φ₁ z ≤ M) (hM₂ : ∀ z, Φ₂ z ≤ M)
    (h₁ : -M2 ≤ ∫ z, Φ₁ z ∂μ) (h₂ : -M2 ≤ ∫ z, Φ₂ z ∂μ) (z : E) :
    |s82r_nd μ Φ₁ z - s82r_nd μ Φ₂ z| ≤
      Real.exp M2 * |Real.exp (Φ₁ z) - Real.exp (Φ₂ z)| +
        Real.exp (M + 2 * M2) * ∫ y, |Real.exp (Φ₁ y) - Real.exp (Φ₂ y)| ∂μ := by
  obtain ⟨hZ₁, he₁⟩ := s82r_expint_lower μ hm₁ hi₁ hM₁ h₁
  obtain ⟨hZ₂, he₂⟩ := s82r_expint_lower μ hm₂ hi₂ hM₂ h₂
  set Z₁ := ∫ y, Real.exp (Φ₁ y) ∂μ with hZ₁d
  set Z₂ := ∫ y, Real.exp (Φ₂ y) ∂μ with hZ₂d
  have hp₁ : 0 < Z₁ := (Real.exp_pos _).trans_le hZ₁
  have hp₂ : 0 < Z₂ := (Real.exp_pos _).trans_le hZ₂
  have hD : |Z₁ - Z₂| ≤ ∫ y, |Real.exp (Φ₁ y) - Real.exp (Φ₂ y)| ∂μ := by
    rw [hZ₁d, hZ₂d, ← integral_sub he₁ he₂]
    exact (abs_integral_le_integral_abs)
  have hinv₁ : 1 / Z₁ ≤ Real.exp M2 := by
    rw [div_le_iff₀ hp₁]
    calc 1 = Real.exp M2 * Real.exp (-M2) := by rw [← Real.exp_add]; simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hZ₁ (Real.exp_pos _).le
  have hinv₂ : 1 / Z₂ ≤ Real.exp M2 := by
    rw [div_le_iff₀ hp₂]
    calc 1 = Real.exp M2 * Real.exp (-M2) := by rw [← Real.exp_add]; simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hZ₂ (Real.exp_pos _).le
  have hκ₂ : Real.exp (Φ₂ z) / Z₂ ≤ Real.exp (M + M2) := by
    rw [Real.exp_add]
    calc Real.exp (Φ₂ z) / Z₂ = Real.exp (Φ₂ z) * (1 / Z₂) := by ring
      _ ≤ Real.exp M * Real.exp M2 :=
        mul_le_mul (Real.exp_le_exp.2 (hM₂ z)) hinv₂ (by positivity) (Real.exp_pos _).le
  unfold s82r_nd
  have e : Real.exp (Φ₁ z) / Z₁ - Real.exp (Φ₂ z) / Z₂ =
      (Real.exp (Φ₁ z) - Real.exp (Φ₂ z)) * (1 / Z₁) +
        (Real.exp (Φ₂ z) / Z₂) * ((Z₂ - Z₁) * (1 / Z₁)) := by
    field_simp
    ring
  rw [e]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / Z₁)]
    calc |Real.exp (Φ₁ z) - Real.exp (Φ₂ z)| * (1 / Z₁) ≤
          |Real.exp (Φ₁ z) - Real.exp (Φ₂ z)| * Real.exp M2 :=
          mul_le_mul_of_nonneg_left hinv₁ (abs_nonneg _)
      _ = _ := mul_comm _ _
  · rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / Z₁),
      abs_of_pos (by positivity : (0 : ℝ) < Real.exp (Φ₂ z) / Z₂)]
    calc Real.exp (Φ₂ z) / Z₂ * (|Z₂ - Z₁| * (1 / Z₁))
        ≤ Real.exp (M + M2) * ((∫ y, |Real.exp (Φ₁ y) - Real.exp (Φ₂ y)| ∂μ) * Real.exp M2) := by
          refine mul_le_mul hκ₂ (mul_le_mul ?_ hinv₁ (by positivity) ?_) (by positivity)
            (Real.exp_pos _).le
          · rw [abs_sub_comm]; exact hD
          · exact integral_nonneg fun y => abs_nonneg _
      _ = Real.exp (M + 2 * M2) * ∫ y, |Real.exp (Φ₁ y) - Real.exp (Φ₂ y)| ∂μ := by
          have : Real.exp (M + 2 * M2) = Real.exp (M + M2) * Real.exp M2 := by
            rw [← Real.exp_add]; ring_nf
          rw [this]; ring

end HRS.MS.S82R

end
