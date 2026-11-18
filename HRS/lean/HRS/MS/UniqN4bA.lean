import HRS.MS.UniqN1cA
import HRS.MS.UniqN0d
import HRS.MS.UniqN4a

/-!
# N4b of `UniqPlan.md`, part A: real-number and Cauchy–Schwarz lemmas

* `n4b_young`: for `0 ≤ κ < 1` and `ε > 0` there is `C` with
  `G A^{1-κ} (A+G)^κ + A^{2-κ} (A+G)^κ ≤ ε G² + C A²` for all `G, A ≥ 0`
  (the total power of `G` is `1 + κ < 2`).
* `n4b_cs`: Cauchy–Schwarz for `∫ w` with `|w| ≤ C |u| (|v₁| + |v₂|)`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace HRS.MS.UniqN4b

open HRS HRS.Whole HRS.Whole.AppendixALemmas HRS.MS.UniqM1 HRS.MS.UniqNDefs HRS.MS.UniqN2b

variable {d : ℕ}

theorem n4b_rpow_split {A κ : ℝ} (hA : 0 ≤ A) (e : ℝ) (he : e ≠ 0) (hκ : 0 ≤ κ) :
    A ^ (e - κ) * A ^ κ = A ^ e := by
  rw [← Real.rpow_add' hA (by simpa using he)]; congr 1; ring

/-- Case `G ≤ M A`. -/
theorem n4b_young_near {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) {M G A : ℝ} (hM : 1 ≤ M)
    (hG : 0 ≤ G) (hA : 0 ≤ A) (h : G ≤ M * A) :
    G * A ^ (1 - κ) * (A + G) ^ κ + A ^ (2 - κ) * (A + G) ^ κ ≤
      ((M + 1) * (1 + M) ^ κ) * A ^ 2 := by
  have h1 : (A + G) ^ κ ≤ ((1 + M) * A) ^ κ :=
    Real.rpow_le_rpow (by linarith) (by nlinarith) hκ0
  rw [Real.mul_rpow (by linarith) hA] at h1
  have e1 : A ^ (1 - κ) * A ^ κ = A := by
    rw [n4b_rpow_split hA 1 one_ne_zero hκ0, Real.rpow_one]
  have e2 : A ^ (2 - κ) * A ^ κ = A ^ 2 := by
    rw [n4b_rpow_split hA 2 two_ne_zero hκ0]
    exact_mod_cast Real.rpow_natCast A 2
  have hp1 : 0 ≤ A ^ (1 - κ) := Real.rpow_nonneg hA _
  have hp2 : 0 ≤ A ^ (2 - κ) := Real.rpow_nonneg hA _
  have hq : 0 ≤ (1 + M) ^ κ := Real.rpow_nonneg (by linarith) _
  calc G * A ^ (1 - κ) * (A + G) ^ κ + A ^ (2 - κ) * (A + G) ^ κ
      ≤ (M * A) * A ^ (1 - κ) * ((1 + M) ^ κ * A ^ κ) + A ^ (2 - κ) * ((1 + M) ^ κ * A ^ κ) := by
        gcongr
    _ = (M * (1 + M) ^ κ) * (A ^ (1 - κ) * A ^ κ) * A + (1 + M) ^ κ * (A ^ (2 - κ) * A ^ κ) := by
        ring
    _ = ((M + 1) * (1 + M) ^ κ) * A ^ 2 := by rw [e1, e2]; ring

/-- Case `M A < G`. -/
theorem n4b_young_far {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) {M G A : ℝ} (hM : 1 ≤ M)
    (hA : 0 ≤ A) (h : M * A < G) :
    G * A ^ (1 - κ) * (A + G) ^ κ + A ^ (2 - κ) * (A + G) ^ κ ≤ 4 * M ^ (κ - 1) * G ^ 2 := by
  have hM0 : 0 < M := by linarith
  have hG : 0 < G := lt_of_le_of_lt (by positivity) h
  have hAG : A ≤ G / M := by rw [le_div_iff₀ hM0]; linarith
  have h1 : (A + G) ^ κ ≤ (2 * G) ^ κ :=
    Real.rpow_le_rpow (by linarith) (by
      have : A ≤ G := by nlinarith
      linarith) hκ0
  rw [Real.mul_rpow (by norm_num) hG.le] at h1
  have h2k : (2 : ℝ) ^ κ ≤ 2 := by
    calc (2 : ℝ) ^ κ ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hκ1.le
      _ = 2 := Real.rpow_one 2
  have h3 : A ^ (1 - κ) ≤ (G / M) ^ (1 - κ) := Real.rpow_le_rpow hA hAG (by linarith)
  have h4 : A ^ (2 - κ) ≤ (G / M) ^ (2 - κ) := Real.rpow_le_rpow hA hAG (by linarith)
  rw [Real.div_rpow hG.le hM0.le] at h3 h4
  have hGk : 0 ≤ G ^ κ := Real.rpow_nonneg hG.le _
  have hMa : 0 < M ^ (1 - κ) := Real.rpow_pos_of_pos hM0 _
  have hMb : M ^ (2 - κ) ≥ M ^ (1 - κ) := Real.rpow_le_rpow_of_exponent_le hM (by linarith)
  have hMc : 0 < M ^ (2 - κ) := Real.rpow_pos_of_pos hM0 _
  have hMe : M ^ (κ - 1) = (M ^ (1 - κ))⁻¹ := by
    rw [← Real.rpow_neg hM0.le]; congr 1; ring
  have hMf : G ^ (2 - κ) / M ^ (2 - κ) ≤ G ^ (2 - κ) / M ^ (1 - κ) :=
    div_le_div_of_nonneg_left (Real.rpow_nonneg hG.le _) hMa hMb
  have eG1 : G * G ^ (1 - κ) * G ^ κ = G ^ 2 := by
    have : G ^ (1 - κ) * G ^ κ = G := by
      rw [n4b_rpow_split hG.le 1 one_ne_zero hκ0, Real.rpow_one]
    calc G * G ^ (1 - κ) * G ^ κ = G * (G ^ (1 - κ) * G ^ κ) := by ring
      _ = G ^ 2 := by rw [this]; ring
  have eG2 : G ^ (2 - κ) * G ^ κ = G ^ 2 := by
    rw [n4b_rpow_split hG.le 2 two_ne_zero hκ0]
    exact_mod_cast Real.rpow_natCast G 2
  have hA1 : 0 ≤ A ^ (1 - κ) := Real.rpow_nonneg hA _
  have hA2 : 0 ≤ A ^ (2 - κ) := Real.rpow_nonneg hA _
  have hAG' : 0 ≤ (A + G) ^ κ := Real.rpow_nonneg (by linarith) _
  have hb : (A + G) ^ κ ≤ 2 * G ^ κ := by
    calc (A + G) ^ κ ≤ 2 ^ κ * G ^ κ := h1
      _ ≤ 2 * G ^ κ := by gcongr
  have hc : G * A ^ (1 - κ) + A ^ (2 - κ) ≤
      2 * (G * G ^ (1 - κ) / M ^ (1 - κ)) := by
    have c1 : G * A ^ (1 - κ) ≤ G * (G ^ (1 - κ) / M ^ (1 - κ)) := by gcongr
    have c2 : A ^ (2 - κ) ≤ G ^ (2 - κ) / M ^ (1 - κ) := h4.trans hMf
    have c3 : G ^ (2 - κ) = G * G ^ (1 - κ) := by
      rw [show (2 - κ) = 1 + (1 - κ) by ring, Real.rpow_add hG, Real.rpow_one]
    rw [c3] at c2
    calc G * A ^ (1 - κ) + A ^ (2 - κ) ≤ G * (G ^ (1 - κ) / M ^ (1 - κ)) + G * G ^ (1 - κ) / M ^ (1 - κ) :=
          add_le_add c1 c2
      _ = 2 * (G * G ^ (1 - κ) / M ^ (1 - κ)) := by ring
  calc G * A ^ (1 - κ) * (A + G) ^ κ + A ^ (2 - κ) * (A + G) ^ κ
      = (G * A ^ (1 - κ) + A ^ (2 - κ)) * (A + G) ^ κ := by ring
    _ ≤ (2 * (G * G ^ (1 - κ) / M ^ (1 - κ))) * (2 * G ^ κ) := by
        gcongr
    _ = 4 * (M ^ (1 - κ))⁻¹ * (G * G ^ (1 - κ) * G ^ κ) := by
        field_simp
        norm_num
    _ = 4 * M ^ (κ - 1) * G ^ 2 := by rw [eG1, hMe]

/-- **The Young step.** -/
theorem n4b_young {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ G A : ℝ, 0 ≤ G → 0 ≤ A →
      G * A ^ (1 - κ) * (A + G) ^ κ + A ^ (2 - κ) * (A + G) ^ κ ≤ ε * G ^ 2 + C * A ^ 2 := by
  set M : ℝ := max 1 ((4 / ε) ^ (1 / (1 - κ))) with hMdef
  have hM : 1 ≤ M := le_max_left _ _
  have hM0 : 0 < M := by linarith
  have h1k : 0 < 1 - κ := by linarith
  have hMg : 4 / ε ≤ M ^ (1 - κ) := by
    calc 4 / ε = ((4 / ε) ^ (1 / (1 - κ))) ^ (1 - κ) := by
          rw [← Real.rpow_mul (by positivity)]
          rw [one_div, inv_mul_cancel₀ h1k.ne', Real.rpow_one]
      _ ≤ M ^ (1 - κ) := Real.rpow_le_rpow (by positivity) (le_max_right _ _) h1k.le
  have hMe : M ^ (κ - 1) = (M ^ (1 - κ))⁻¹ := by
    rw [← Real.rpow_neg hM0.le]; congr 1; ring
  have h4 : 4 * M ^ (κ - 1) ≤ ε := by
    rw [hMe]
    have hp : 0 < M ^ (1 - κ) := Real.rpow_pos_of_pos hM0 _
    have : 4 / ε ≤ M ^ (1 - κ) := hMg
    rw [div_le_iff₀ hε] at this
    rw [← div_eq_mul_inv, div_le_iff₀ hp]
    linarith
  refine ⟨(M + 1) * (1 + M) ^ κ, by positivity, fun G A hG hA => ?_⟩
  by_cases h : G ≤ M * A
  · have := n4b_young_near hκ0 hκ1 hM hG hA h
    have : 0 ≤ ε * G ^ 2 := by positivity
    linarith
  · push Not at h
    have h5 := n4b_young_far hκ0 hκ1 hM hA h
    have : 4 * M ^ (κ - 1) * G ^ 2 ≤ ε * G ^ 2 := by gcongr
    have : 0 ≤ (M + 1) * (1 + M) ^ κ * A ^ 2 := by positivity
    linarith

/-- **Cauchy–Schwarz** for `|w| ≤ C |u| (|v₁| + |v₂|)`. -/
theorem n4b_cs {u v₁ v₂ w : Euc d → ℝ} (hu : AEStronglyMeasurable u volume)
    (hv₁ : AEStronglyMeasurable v₁ volume) (hv₂ : AEStronglyMeasurable v₂ volume)
    {C a b₁ b₂ : ℝ} (hC : 0 ≤ C) (ha : 0 ≤ a) (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂)
    (hw : ∀ y, |w y| ≤ C * |u y| * (|v₁ y| + |v₂ y|))
    (hua : eLpNorm u 2 volume ≤ ENNReal.ofReal a) (hv₁b : eLpNorm v₁ 2 volume ≤ ENNReal.ofReal b₁)
    (hv₂b : eLpNorm v₂ 2 volume ≤ ENNReal.ofReal b₂) :
    |∫ y, w y| ≤ C * a * (b₁ + b₂) := by
  have hpt : ∀ y, ENNReal.ofReal ‖w y‖ ≤
      ENNReal.ofReal C * (‖u y‖ₑ * ‖v₁ y‖ₑ + ‖u y‖ₑ * ‖v₂ y‖ₑ) := by
    intro y
    rw [Real.norm_eq_abs]
    refine (ENNReal.ofReal_le_ofReal (hw y)).trans (le_of_eq ?_)
    rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs,
      ← ENNReal.ofReal_mul (abs_nonneg _), ← ENNReal.ofReal_mul (abs_nonneg _),
      ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul hC]
    congr 1; ring
  have hmeas1 : ∀ v : Euc d → ℝ, AEStronglyMeasurable v volume →
      AEMeasurable (fun y => ‖u y‖ₑ * ‖v y‖ₑ) volume := fun v hv =>
    hu.aemeasurable.enorm.mul hv.aemeasurable.enorm
  have hl : ∫⁻ y, ENNReal.ofReal ‖w y‖ ≤ ENNReal.ofReal (C * a * (b₁ + b₂)) := by
    calc ∫⁻ y, ENNReal.ofReal ‖w y‖
        ≤ ∫⁻ y, ENNReal.ofReal C * (‖u y‖ₑ * ‖v₁ y‖ₑ + ‖u y‖ₑ * ‖v₂ y‖ₑ) := lintegral_mono hpt
      _ = ENNReal.ofReal C * ((∫⁻ y, ‖u y‖ₑ * ‖v₁ y‖ₑ) + ∫⁻ y, ‖u y‖ₑ * ‖v₂ y‖ₑ) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_add_left' (hmeas1 v₁ hv₁)]
      _ ≤ ENNReal.ofReal C * (eLpNorm u 2 volume * eLpNorm v₁ 2 volume +
            eLpNorm u 2 volume * eLpNorm v₂ 2 volume) := by
          gcongr
          · exact n2b_holder hu hv₁
          · exact n2b_holder hu hv₂
      _ ≤ ENNReal.ofReal C * (ENNReal.ofReal a * ENNReal.ofReal b₁ +
            ENNReal.ofReal a * ENNReal.ofReal b₂) := by gcongr
      _ = ENNReal.ofReal (C * a * (b₁ + b₂)) := by
          rw [← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_mul ha,
            ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul hC]
          congr 1; ring
  have hnn : 0 ≤ C * a * (b₁ + b₂) := by positivity
  calc |∫ y, w y| = ‖∫ y, w y‖ := (Real.norm_eq_abs _).symm
    _ ≤ ENNReal.toReal (∫⁻ y, ENNReal.ofReal ‖w y‖) := norm_integral_le_lintegral_norm _
    _ ≤ _ := ENNReal.toReal_le_of_le_ofReal hnn hl

end HRS.MS.UniqN4b
