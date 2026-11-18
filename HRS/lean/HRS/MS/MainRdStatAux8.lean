import HRS.MS.MainRdStatAux7

/-!
# SA2, packet 6c: slices, Jensen, and the expected covariance cost

* generic lemmas `sa2_slice`, `sa2_slice_le`: from a finite (bounded) iterated lintegral of a nonnegative jointly measurable function to
  integrability of its time slices and a real bound of the iterated integral;
* `sa2_lint_sqrt`: `E ∫_0^T √(e_σ) dσ ≤ T √E` when `E e_σ ≤ E` for each `σ` (Jensen);
* `sa2_cov_cost`: `covDiscrepancyMatrix ≤ 2 q_N C (∑_a B_a)² T w_N`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open HRS.Whole HRS.Whole.AppendixA HRS.Uniform HRS.GF HRS.Whole.AppendixALemmas
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MainRdStat

variable {d : ℕ}

section Slice

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem sa2_slice {F : Ω → ℝ → ℝ} (hFm : Measurable fun p : Ω × ℝ => F p.1 p.2) (hF0 : ∀ w σ, 0 ≤ F w σ)
    {T : ℝ} (hfin : ∫⁻ w, (∫⁻ σ in Set.Icc (0 : ℝ) T, ENNReal.ofReal (F w σ)) ∂P ≠ ⊤) :
    (∀ᵐ w ∂P, IntegrableOn (F w) (Set.Icc (0 : ℝ) T)) ∧
      Integrable (fun w => ∫ σ in Set.Icc (0 : ℝ) T, F w σ) P := by
  set G : Ω → ℝ≥0∞ := fun w => ∫⁻ σ in Set.Icc (0 : ℝ) T, ENNReal.ofReal (F w σ) with hG
  have hGm : Measurable G := by
    have : Measurable fun p : Ω × ℝ => ENNReal.ofReal (F p.1 p.2) := ENNReal.measurable_ofReal.comp hFm
    exact this.lintegral_prod_right' (ν := volume.restrict (Set.Icc (0 : ℝ) T))
  have hae : ∀ᵐ w ∂P, G w < ⊤ := ae_lt_top hGm hfin
  have hsl : ∀ w, Measurable (F w) := fun w => hFm.comp measurable_prodMk_left
  refine ⟨?_, ?_⟩
  · filter_upwards [hae] with w hw
    refine ⟨(hsl w).aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    have : ∫⁻ σ in Set.Icc (0 : ℝ) T, ‖F w σ‖ₑ = G w := by
      refine lintegral_congr fun σ => ?_
      rw [Real.enorm_eq_ofReal (hF0 w σ)]
    rw [this]; exact hw
  · have h1 : (fun w => ∫ σ in Set.Icc (0 : ℝ) T, F w σ) = fun w => (G w).toReal := by
      funext w
      exact integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun σ => hF0 w σ)
        (hsl w).aestronglyMeasurable
    rw [h1]
    exact integrable_toReal_of_lintegral_ne_top hGm.aemeasurable hfin

theorem sa2_slice_le {F : Ω → ℝ → ℝ} (hFm : Measurable fun p : Ω × ℝ => F p.1 p.2) (hF0 : ∀ w σ, 0 ≤ F w σ)
    {T B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∫⁻ w, (∫⁻ σ in Set.Icc (0 : ℝ) T, ENNReal.ofReal (F w σ)) ∂P ≤ ENNReal.ofReal B) :
    ∫ w, (∫ σ in Set.Icc (0 : ℝ) T, F w σ) ∂P ≤ B := by
  have hfin : ∫⁻ w, (∫⁻ σ in Set.Icc (0 : ℝ) T, ENNReal.ofReal (F w σ)) ∂P ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hB
  set G : Ω → ℝ≥0∞ := fun w => ∫⁻ σ in Set.Icc (0 : ℝ) T, ENNReal.ofReal (F w σ) with hG
  have hGm : Measurable G := by
    have : Measurable fun p : Ω × ℝ => ENNReal.ofReal (F p.1 p.2) := ENNReal.measurable_ofReal.comp hFm
    exact this.lintegral_prod_right' (ν := volume.restrict (Set.Icc (0 : ℝ) T))
  have hae : ∀ᵐ w ∂P, G w < ⊤ := ae_lt_top hGm hfin
  have hsl : ∀ w, Measurable (F w) := fun w => hFm.comp measurable_prodMk_left
  have h1 : (fun w => ∫ σ in Set.Icc (0 : ℝ) T, F w σ) = fun w => (G w).toReal := by
    funext w
    exact integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun σ => hF0 w σ)
      (hsl w).aestronglyMeasurable
  rw [h1, integral_toReal hGm.aemeasurable hae]
  exact ENNReal.toReal_le_of_le_ofReal hB0 hB

theorem sa2_ofReal_sqrt (y : ℝ) : ENNReal.ofReal (Real.sqrt y) = ENNReal.ofReal y ^ (1 / 2 : ℝ) := by
  by_cases hy : 0 ≤ y
  · rw [ENNReal.ofReal_rpow_of_nonneg hy (by norm_num), Real.sqrt_eq_rpow]
  · push Not at hy
    rw [Real.sqrt_eq_zero_of_nonpos hy.le, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos hy.le,
      ENNReal.zero_rpow_of_pos (by norm_num)]

theorem sa2_jensen_sqrt {x : Ω → ℝ} (hx : Measurable x) :
    ∫⁻ w, ENNReal.ofReal (Real.sqrt (x w)) ∂P ≤ (∫⁻ w, ENNReal.ofReal (x w) ∂P) ^ (1 / 2 : ℝ) := by
  have hh : Measurable fun w => ENNReal.ofReal (x w) := ENNReal.measurable_ofReal.comp hx
  have h := lintegral_rpow_mono_meas P hh (p := 1 / 2) (q := 1) (by norm_num) (by norm_num)
  simp only [ENNReal.rpow_one, div_one, one_div, inv_inv, ENNReal.rpow_two] at h
  simp only [sa2_ofReal_sqrt]
  have h2 : ∀ y : ℝ≥0∞, (y ^ (2 : ℝ)) ^ (1 / 2 : ℝ) = y := fun y => by
    rw [← ENNReal.rpow_mul]; norm_num
  calc ∫⁻ w, ENNReal.ofReal (x w) ^ (1 / 2 : ℝ) ∂P
      = ((∫⁻ w, ENNReal.ofReal (x w) ^ (1 / 2 : ℝ) ∂P) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := (h2 _).symm
    _ ≤ (∫⁻ w, ENNReal.ofReal (x w) ∂P) ^ (1 / 2 : ℝ) := by
        gcongr
        simpa using h

theorem sa2_lint_sqrt {e : Ω → ℝ → ℝ} (he : Measurable fun p : Ω × ℝ => e p.1 p.2) {T E : ℝ} (hT : 0 ≤ T)
    (hE : ∀ σ ∈ Set.Icc (0 : ℝ) T, ∫⁻ w, ENNReal.ofReal (e w σ) ∂P ≤ ENNReal.ofReal E) :
    ∫⁻ w, (∫⁻ σ in Set.Icc (0 : ℝ) T, ENNReal.ofReal (Real.sqrt (e w σ))) ∂P ≤
      ENNReal.ofReal (T * Real.sqrt E) := by
  have hm : Measurable fun p : Ω × ℝ => ENNReal.ofReal (Real.sqrt (e p.1 p.2)) :=
    ENNReal.measurable_ofReal.comp (Real.continuous_sqrt.measurable.comp he)
  rw [lintegral_lintegral_swap hm.aemeasurable]
  calc ∫⁻ σ in Set.Icc (0 : ℝ) T, (∫⁻ w, ENNReal.ofReal (Real.sqrt (e w σ)) ∂P)
      ≤ ∫⁻ σ in Set.Icc (0 : ℝ) T, ENNReal.ofReal E ^ (1 / 2 : ℝ) := by
        refine setLIntegral_mono' measurableSet_Icc fun σ hσ => ?_
        refine (sa2_jensen_sqrt (hx := he.comp measurable_prodMk_right)).trans ?_
        gcongr
        exact hE σ hσ
    _ = ENNReal.ofReal (T * Real.sqrt E) := by
        rw [setLIntegral_const, Real.volume_Icc, sub_zero]
        by_cases hE0 : 0 ≤ E
        · rw [ENNReal.ofReal_rpow_of_nonneg hE0 (by norm_num), Real.sqrt_eq_rpow,
            ENNReal.ofReal_mul hT, mul_comm]
        · push Not at hE0
          rw [ENNReal.ofReal_of_nonpos hE0.le, ENNReal.zero_rpow_of_pos (by norm_num),
            Real.sqrt_eq_zero_of_nonpos hE0.le]
          simp

end Slice

end HRS.MS.MainRdStat
