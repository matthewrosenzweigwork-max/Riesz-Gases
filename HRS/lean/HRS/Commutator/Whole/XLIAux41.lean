import HRS.Commutator.Whole.XLIAux40

/-!
# X-LI part 41: the Carleson endpoint estimate, `r > 2`
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal FourierTransform ContDiff Convolution Topology SchwartzMap

noncomputable section

namespace HRS.Commutator.Whole.XLI

open HRS.Commutator.Whole

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

section Carl

variable (α : ℝ)

lemma Gs_sq_le (ψ : SchwartzMap 𝔼 ℂ) (j : ℤ) (y : 𝔼) :
    Gs ψ j y ^ 2 ≤ 4 * (KP d * (CvP (j + -3) (fun z => ‖ψ z‖ₑ ^ 2) y +
      CvP (j + -2) (fun z => ‖ψ z‖ₑ ^ 2) y + CvP (j + -1) (fun z => ‖ψ z‖ₑ ^ 2) y +
      CvP j (fun z => ‖ψ z‖ₑ ^ 2) y)) := by
  have hm : Measurable (fun z => ‖ψ z‖ₑ) := ψ.continuous.measurable.enorm
  have h : ∀ l : ℤ, Gc ψ l y ^ 2 ≤ KP d * CvP l (fun z => ‖ψ z‖ₑ ^ 2) y := fun l =>
    CvP_sq_le l hm y
  unfold Gs
  set a := Gc ψ (j + -3) y
  set b := Gc ψ (j + -2) y
  set c := Gc ψ (j + -1) y
  set e := Gc ψ j y
  calc (a + b + c + e) ^ 2 = ((a + b) + (c + e)) ^ 2 := by ring
    _ ≤ 2 * ((a + b) ^ 2 + (c + e) ^ 2) := add_sq_le_two _ _
    _ ≤ 2 * (2 * (a ^ 2 + b ^ 2) + 2 * (c ^ 2 + e ^ 2)) := by
        gcongr
        · exact add_sq_le_two _ _
        · exact add_sq_le_two _ _
    _ = 4 * (a ^ 2 + b ^ 2 + c ^ 2 + e ^ 2) := by ring
    _ ≤ 4 * (KP d * CvP (j + -3) (fun z => ‖ψ z‖ₑ ^ 2) y + KP d * CvP (j + -2) (fun z => ‖ψ z‖ₑ ^ 2) y +
          KP d * CvP (j + -1) (fun z => ‖ψ z‖ₑ ^ 2) y + KP d * CvP j (fun z => ‖ψ z‖ₑ ^ 2) y) := by
        gcongr
        · exact h _
        · exact h _
        · exact h _
        · exact h _
    _ = _ := by ring

lemma lintegral_enorm_sq_ne_top (ψ : SchwartzMap 𝔼 ℂ) : ∫⁻ z, ‖ψ z‖ₑ ^ 2 ≠ ⊤ := by
  have h := (schwartz_rpow_integrable ψ (a := 2) two_pos).lintegral_lt_top
  have : ∫⁻ z, ‖ψ z‖ₑ ^ 2 = ∫⁻ z, ENNReal.ofReal (‖ψ z‖ ^ (2 : ℝ)) := by
    refine lintegral_congr fun z => ?_
    rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), ofReal_norm,
      ENNReal.rpow_two]
  rw [this]; exact h.ne

/-- the weighted estimate for the square function majorant -/
lemma Qw_bound (hd : 1 ≤ d) :
    ∃ A0 : ℝ≥0∞, A0 ≠ ⊤ ∧ ∀ (φ ψ : SchwartzMap 𝔼 ℂ) (B : ℝ≥0∞), B ≠ ⊤ →
      (∀ x, ‖Fm α φ x‖ₑ ≤ B) → ∀ w : 𝔼 → ℝ≥0∞, Measurable w →
      ∫⁻ x, QQ α φ ψ x * w x ≤ A0 * B ^ 2 *
        ∫⁻ x, (w x + cmxHLS_Md (cmxHLS_Md w) x) * cmxHLS_Md (fun z => ‖ψ z‖ₑ ^ 2) x := by
  obtain ⟨Cc, hCc, hcar⟩ := carleson_embed hd (isLPRep_Ths (d := d) (-α))
  refine ⟨4 * KP d * (Cc * (2 ^ (d + 1) * KP d)) * 4, ?_, fun φ ψ B hB hFB w hw => ?_⟩
  · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) KP_ne_top)
      (ENNReal.mul_ne_top hCc (ENNReal.mul_ne_top (ENNReal.pow_ne_top (by simp)) KP_ne_top)))
      (by simp)
  set g : 𝔼 → ℝ≥0∞ := fun z => ‖ψ z‖ₑ ^ 2 with hg
  have hgm : Measurable g := ψ.continuous.measurable.enorm.pow_const 2
  have hgi := lintegral_enorm_sq_ne_top ψ
  set K : ℤ → 𝔼 → ℂ := fun j => dK (Ths (-α) : ℤ → 𝔼 → ℂ) j with hKdef
  have hemb : ∀ s : ℤ, s ≤ 0 →
      ∑' j, ∫⁻ x, (‖Fj α φ j x‖ₑ ^ 2 * w x) * CvP (j + s) g x ≤
        Cc * B ^ 2 * ((2 ^ (d + 1) * KP d) *
          ∫⁻ x, (w x + cmxHLS_Md (cmxHLS_Md w) x) * cmxHLS_Md g x) := by
    intro s hs
    have h := hcar (⇑(Fm α φ)) (Fm α φ).continuous.measurable (Fm α φ).integrable B hB hFB g hgm
      hgi (fun j => CvP (j + s) g) (KP d) KP_ne_top (by
        have : (0 : ℝ≥0∞) < KP d := by
          unfold KP
          exact ENNReal.mul_pos (by simp) (measure_closedBall_pos volume _ one_pos).ne'
        exact this.ne')
      (fun j => CvP_measurable _ hgm)
      (fun j x y hxy => CvP_shift (j + s) hgm (lt_of_lt_of_le hxy
        (zpow_le_zpow_right₀ (by norm_num) (by omega))))
      (fun j y => CvP_le _ hgm y) 1 one_pos w hw
    simp only [ENNReal.rpow_one] at h
    exact h
  have hemb0 := hemb 0 le_rfl
  simp only [add_zero] at hemb0
  have hFjm : ∀ j, Measurable (fun x => ‖Fj α φ j x‖ₑ ^ 2 * w x) := fun j =>
    ((Fj_meas α φ j).enorm.pow_const 2).mul hw
  have hQw : ∀ x, QQ α φ ψ x * w x =
      ∑' j, (‖Fj α φ j x‖ₑ ^ 2 * w x) * Gs ψ j x ^ 2 := by
    intro x
    unfold QQ hh
    rw [← ENNReal.tsum_mul_right]
    refine tsum_congr fun j => ?_
    rw [mul_pow]; ring
  have hper : ∀ j, ∫⁻ x, (‖Fj α φ j x‖ₑ ^ 2 * w x) * Gs ψ j x ^ 2 ≤
      4 * KP d * ((∫⁻ x, (‖Fj α φ j x‖ₑ ^ 2 * w x) * CvP (j + -3) g x) +
        (∫⁻ x, (‖Fj α φ j x‖ₑ ^ 2 * w x) * CvP (j + -2) g x) +
        (∫⁻ x, (‖Fj α φ j x‖ₑ ^ 2 * w x) * CvP (j + -1) g x) +
        ∫⁻ x, (‖Fj α φ j x‖ₑ ^ 2 * w x) * CvP j g x) := by
    intro j
    have h1 : ∀ x, (‖Fj α φ j x‖ₑ ^ 2 * w x) * Gs ψ j x ^ 2 ≤
        (4 * KP d) * ((‖Fj α φ j x‖ₑ ^ 2 * w x) * CvP (j + -3) g x +
          (‖Fj α φ j x‖ₑ ^ 2 * w x) * CvP (j + -2) g x +
          (‖Fj α φ j x‖ₑ ^ 2 * w x) * CvP (j + -1) g x +
          (‖Fj α φ j x‖ₑ ^ 2 * w x) * CvP j g x) := by
      intro x
      calc (‖Fj α φ j x‖ₑ ^ 2 * w x) * Gs ψ j x ^ 2
          ≤ (‖Fj α φ j x‖ₑ ^ 2 * w x) * (4 * (KP d * (CvP (j + -3) g x + CvP (j + -2) g x +
              CvP (j + -1) g x + CvP j g x))) := mul_le_mul_right (Gs_sq_le ψ j x) _
        _ = _ := by ring
    have m3 : Measurable (fun x => (‖Fj α φ j x‖ₑ ^ 2 * w x) * CvP (j + -3) g x) :=
      (hFjm j).mul (CvP_measurable (j + -3) hgm)
    have m2 : Measurable (fun x => (‖Fj α φ j x‖ₑ ^ 2 * w x) * CvP (j + -2) g x) :=
      (hFjm j).mul (CvP_measurable (j + -2) hgm)
    have m1 : Measurable (fun x => (‖Fj α φ j x‖ₑ ^ 2 * w x) * CvP (j + -1) g x) :=
      (hFjm j).mul (CvP_measurable (j + -1) hgm)
    have m0 : Measurable (fun x => (‖Fj α φ j x‖ₑ ^ 2 * w x) * CvP j g x) :=
      (hFjm j).mul (CvP_measurable j hgm)
    have m32 : Measurable (fun x => (‖Fj α φ j x‖ₑ ^ 2 * w x) * CvP (j + -3) g x +
        (‖Fj α φ j x‖ₑ ^ 2 * w x) * CvP (j + -2) g x) := m3.add m2
    have m321 : Measurable (fun x => (‖Fj α φ j x‖ₑ ^ 2 * w x) * CvP (j + -3) g x +
        (‖Fj α φ j x‖ₑ ^ 2 * w x) * CvP (j + -2) g x +
        (‖Fj α φ j x‖ₑ ^ 2 * w x) * CvP (j + -1) g x) := m32.add m1
    have m3210 : Measurable (fun x => (‖Fj α φ j x‖ₑ ^ 2 * w x) * CvP (j + -3) g x +
        (‖Fj α φ j x‖ₑ ^ 2 * w x) * CvP (j + -2) g x +
        (‖Fj α φ j x‖ₑ ^ 2 * w x) * CvP (j + -1) g x +
        (‖Fj α φ j x‖ₑ ^ 2 * w x) * CvP j g x) := m321.add m0
    calc ∫⁻ x, (‖Fj α φ j x‖ₑ ^ 2 * w x) * Gs ψ j x ^ 2
        ≤ ∫⁻ x, (4 * KP d) * ((‖Fj α φ j x‖ₑ ^ 2 * w x) * CvP (j + -3) g x +
          (‖Fj α φ j x‖ₑ ^ 2 * w x) * CvP (j + -2) g x +
          (‖Fj α φ j x‖ₑ ^ 2 * w x) * CvP (j + -1) g x +
          (‖Fj α φ j x‖ₑ ^ 2 * w x) * CvP j g x) := lintegral_mono h1
      _ = _ := by
          rw [lintegral_const_mul _ m3210, lintegral_add_left m321, lintegral_add_left m32,
            lintegral_add_left m3]
  have hem3 := hemb (-3) (by norm_num)
  have hem2 := hemb (-2) (by norm_num)
  have hem1 := hemb (-1) (by norm_num)
  calc ∫⁻ x, QQ α φ ψ x * w x
      = ∫⁻ x, ∑' j, (‖Fj α φ j x‖ₑ ^ 2 * w x) * Gs ψ j x ^ 2 := lintegral_congr hQw
    _ = ∑' j, ∫⁻ x, (‖Fj α φ j x‖ₑ ^ 2 * w x) * Gs ψ j x ^ 2 := by
        rw [lintegral_tsum]
        intro j
        exact ((hFjm j).mul ((Gs_meas ψ j).pow_const 2)).aemeasurable
    _ ≤ ∑' j, 4 * KP d * ((∫⁻ x, (‖Fj α φ j x‖ₑ ^ 2 * w x) * CvP (j + -3) g x) +
        (∫⁻ x, (‖Fj α φ j x‖ₑ ^ 2 * w x) * CvP (j + -2) g x) +
        (∫⁻ x, (‖Fj α φ j x‖ₑ ^ 2 * w x) * CvP (j + -1) g x) +
        ∫⁻ x, (‖Fj α φ j x‖ₑ ^ 2 * w x) * CvP j g x) := ENNReal.tsum_le_tsum hper
    _ = 4 * KP d * ((∑' j, ∫⁻ x, (‖Fj α φ j x‖ₑ ^ 2 * w x) * CvP (j + -3) g x) +
        (∑' j, ∫⁻ x, (‖Fj α φ j x‖ₑ ^ 2 * w x) * CvP (j + -2) g x) +
        (∑' j, ∫⁻ x, (‖Fj α φ j x‖ₑ ^ 2 * w x) * CvP (j + -1) g x) +
        ∑' j, ∫⁻ x, (‖Fj α φ j x‖ₑ ^ 2 * w x) * CvP j g x) := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_add]
    _ ≤ 4 * KP d * (Cc * B ^ 2 * ((2 ^ (d + 1) * KP d) *
          ∫⁻ x, (w x + cmxHLS_Md (cmxHLS_Md w) x) * cmxHLS_Md g x) +
        Cc * B ^ 2 * ((2 ^ (d + 1) * KP d) *
          ∫⁻ x, (w x + cmxHLS_Md (cmxHLS_Md w) x) * cmxHLS_Md g x) +
        Cc * B ^ 2 * ((2 ^ (d + 1) * KP d) *
          ∫⁻ x, (w x + cmxHLS_Md (cmxHLS_Md w) x) * cmxHLS_Md g x) +
        Cc * B ^ 2 * ((2 ^ (d + 1) * KP d) *
          ∫⁻ x, (w x + cmxHLS_Md (cmxHLS_Md w) x) * cmxHLS_Md g x)) := by
        gcongr
    _ = _ := by ring

end Carl

end HRS.Commutator.Whole.XLI
