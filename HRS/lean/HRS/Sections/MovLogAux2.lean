import HRS.Sections.MovLogAux1

/-!
# MOVLOG (part 2): exponential tail to `L^r` moment

`movlog_tail_moment`: if `E e^{a|Z|} ≤ e^A` (`A ≥ 1`, `a > 0`) then `‖Z‖_{L^r} ≤ K_r A / a` (`K_r` depends on `r` only).
This is the splitting of `r ∫ z^{r-1} P(Z > z) dz` in the proof of `P:eq:pair-moments` (TeX L6683-6689), in the form
`y^r ≤ 1 + k! e^y`, `y = a|Z|/A`, plus `E e^{a|Z|/A} ≤ (E e^{a|Z|})^{1/A} ≤ e`.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

namespace MovLog

theorem movlog_rpow_le (r : ℝ) (hr : 1 ≤ r) {y : ℝ} (hy : 0 ≤ y) :
    y ^ r ≤ 1 + (Nat.factorial ⌈r⌉₊ : ℝ) * Real.exp y := by
  set k : ℕ := ⌈r⌉₊ with hk
  have hrk : r ≤ (k : ℝ) := Nat.le_ceil r
  have hexp : y ^ k ≤ (k.factorial : ℝ) * Real.exp y := by
    have := Real.pow_div_factorial_le_exp y hy k
    have hf : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
    rw [div_le_iff₀ hf] at this
    linarith
  have hex0 : 0 ≤ (k.factorial : ℝ) * Real.exp y := by positivity
  by_cases h1 : y ≤ 1
  · have : y ^ r ≤ 1 := Real.rpow_le_one hy h1 (by linarith)
    linarith
  · push Not at h1
    have : y ^ r ≤ y ^ (k : ℝ) := Real.rpow_le_rpow_of_exponent_le h1.le hrk
    rw [Real.rpow_natCast] at this
    linarith

theorem movlog_tail_moment (r : ℝ) (hr : 1 ≤ r) : ∃ K : ℝ, 0 ≤ K ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (Z : Ω → ℝ),
      AEMeasurable Z P → ∀ a A : ℝ, 0 < a → 1 ≤ A →
      ∫⁻ ω, ENNReal.ofReal (Real.exp (a * |Z ω|)) ∂P ≤ ENNReal.ofReal (Real.exp A) →
      eLpNorm Z (ENNReal.ofReal r) P ≤ ENNReal.ofReal (K * A / a) := by
  set k : ℕ := ⌈r⌉₊ with hk
  set m : ℝ := (k.factorial : ℝ) with hm
  have hm0 : 0 ≤ m := by positivity
  set w : ℝ := 1 + m * Real.exp 1 with hw
  have hw0 : 0 < w := by positivity
  refine ⟨w ^ (1 / r), Real.rpow_nonneg hw0.le _, ?_⟩
  intro Ω _ P _ Z hZ a A ha hA hint
  have hA0 : 0 < A := by linarith
  have hr0 : 0 < r := by linarith
  set y : Ω → ℝ := fun ω => a * |Z ω| / A with hy
  have hy0 : ∀ ω, 0 ≤ y ω := fun ω => by positivity
  have hymeas : AEMeasurable y P := (hZ.abs.const_mul a).div_const A
  -- step 1: E e^y ≤ e
  have h1 : ∫⁻ ω, ENNReal.ofReal (Real.exp (y ω)) ∂P ≤ ENNReal.ofReal (Real.exp 1) := by
    have hFm : AEStronglyMeasurable (fun ω => Real.exp (y ω)) P :=
      (Real.measurable_exp.comp_aemeasurable hymeas).aestronglyMeasurable
    have hle : eLpNorm (fun ω => Real.exp (y ω)) 1 P ≤
        eLpNorm (fun ω => Real.exp (y ω)) (ENNReal.ofReal A) P :=
      eLpNorm_le_eLpNorm_of_exponent_le (by
        rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hA)
    rw [eLpNorm_one_eq_lintegral_enorm hFm] at hle
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 hA0).ne' ENNReal.ofReal_ne_top hFm,
      ENNReal.toReal_ofReal hA0.le] at hle
    have e1 : ∀ ω, ‖Real.exp (y ω)‖ₑ = ENNReal.ofReal (Real.exp (y ω)) := fun ω => by
      rw [Real.enorm_of_nonneg (Real.exp_pos _).le]
    have e2 : ∀ ω, ‖Real.exp (y ω)‖ₑ ^ A = ENNReal.ofReal (Real.exp (a * |Z ω|)) := fun ω => by
      have hyA : y ω * A = a * |Z ω| := by simp only [hy]; field_simp
      rw [e1, ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le hA0.le, ← Real.exp_mul, hyA]
    simp_rw [e2, e1] at hle
    refine hle.trans ?_
    calc (∫⁻ ω, ENNReal.ofReal (Real.exp (a * |Z ω|)) ∂P) ^ (1 / A)
        ≤ (ENNReal.ofReal (Real.exp A)) ^ (1 / A) :=
          ENNReal.rpow_le_rpow hint (by positivity)
      _ = ENNReal.ofReal (Real.exp 1) := by
          rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (by positivity), ← Real.exp_mul]
          congr 2; field_simp
  -- step 2: pointwise bound
  set c : ℝ := (A / a) ^ r with hc
  have hc0 : 0 ≤ c := by positivity
  have hpt : ∀ ω, |Z ω| ^ r ≤ c * (1 + m * Real.exp (y ω)) := fun ω => by
    have : |Z ω| = (A / a) * y ω := by simp only [hy]; field_simp
    rw [this, Real.mul_rpow (by positivity) (hy0 ω)]
    exact mul_le_mul_of_nonneg_left (movlog_rpow_le r hr (hy0 ω)) hc0
  have h2 : ∫⁻ ω, ‖Z ω‖ₑ ^ r ∂P ≤ ENNReal.ofReal (c * w) := by
    have e3 : ∀ ω, ‖Z ω‖ₑ ^ r = ENNReal.ofReal (|Z ω| ^ r) := fun ω => by
      rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hr0.le]
    simp_rw [e3]
    calc ∫⁻ ω, ENNReal.ofReal (|Z ω| ^ r) ∂P
        ≤ ∫⁻ ω, ENNReal.ofReal c * (1 + ENNReal.ofReal m * ENNReal.ofReal (Real.exp (y ω))) ∂P := by
          refine lintegral_mono fun ω => ?_
          rw [← ENNReal.ofReal_mul hm0, ← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by norm_num)
            (by positivity), ← ENNReal.ofReal_mul hc0]
          exact ENNReal.ofReal_le_ofReal (by simpa using hpt ω)
      _ = ENNReal.ofReal c * (1 + ENNReal.ofReal m * ∫⁻ ω, ENNReal.ofReal (Real.exp (y ω)) ∂P) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left measurable_const,
            lintegral_const, measure_univ, mul_one,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal c * (1 + ENNReal.ofReal m * ENNReal.ofReal (Real.exp 1)) := by
          gcongr
      _ = ENNReal.ofReal (c * w) := by
          rw [← ENNReal.ofReal_mul hm0, ← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by norm_num)
            (by positivity), ← ENNReal.ofReal_mul hc0]
  have h3 : eLpNorm Z (ENNReal.ofReal r) P ≤ ENNReal.ofReal (c * w) ^ (1 / r) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 hr0).ne' ENNReal.ofReal_ne_top
      hZ.aestronglyMeasurable, ENNReal.toReal_ofReal hr0.le]
    exact ENNReal.rpow_le_rpow h2 (by positivity)
  refine h3.trans (le_of_eq ?_)
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
  congr 1
  rw [Real.mul_rpow hc0 hw0.le, hc, ← Real.rpow_mul (by positivity), mul_one_div_cancel hr0.ne',
    Real.rpow_one]
  ring

end MovLog

end HRS

end
