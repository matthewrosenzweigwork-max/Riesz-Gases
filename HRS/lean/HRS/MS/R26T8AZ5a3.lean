import HRS.MS.R26T8AZ5a2
import HRS.MS.R26T8AP01

/-!
# S8.2 T8A Z5a3: bounds on the slice of a supported conormal function of negative order
`r26t8a_Z5a3_slice`: `σ < 0`, `Conormal 1 b M σ A P`, `P(x,y) = 0` for `|x-y| ≥ 1/2`; then `Ψ = midPair P X` satisfies, for `w ≠ 0`,
`|Ψ(w)| ≤ C A jb(X)^{2M}` and `‖DΨ(w)‖ ≤ C A jb(X)^{2M} |w|^{-1}`, with `C` independent of `P, A, X`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_Z5a3_slice (b : ℕ) (M σ : ℝ) (hM : 0 ≤ M) (hσ : σ < 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (A : ℝ), 0 ≤ A → ∀ (P : Euc d → Euc d → ℝ), Conormal 1 b M σ A P →
      (∀ x y : Euc d, 1 / 2 ≤ ‖x - y‖ → P x y = 0) → ∀ X : Euc d,
      (∀ w : Euc d, w ≠ 0 → |midPair P X w| ≤ C * A * jbracket X ^ (2 * M)) ∧
      (∀ w : Euc d, w ≠ 0 → ‖fderiv ℝ (fun w => midPair P X w) w‖ ≤ C * A * jbracket X ^ (2 * M) * ‖w‖ ^ (-(1 : ℝ))) := by
  obtain ⟨c, hc0, hc⟩ := r26t8a_Z5a1_log_bound (a := -σ) (by linarith) b
  refine ⟨3 ^ (2 * M) * (1 + c), mul_nonneg (Real.rpow_nonneg (by norm_num) _) (by linarith), fun A hA P hP hsupp X => ⟨fun w hw => ?_, fun w hw => ?_⟩⟩
  · have hwn : 0 < ‖w‖ := norm_pos_iff.2 hw
    by_cases h2 : 1 / 2 ≤ ‖w‖
    · have : midPair P X w = 0 := hsupp _ _ (by
        have e : (X + (1 / 2 : ℝ) • w) - (X - (1 / 2 : ℝ) • w) = w := by module
        rw [e]; exact h2)
      rw [this, abs_zero]
      have hj : 0 ≤ jbracket X ^ (2 * M) := Real.rpow_nonneg (s83_jb_pos X).le _
      have hC : 0 ≤ 3 ^ (2 * M) * (1 + c) := mul_nonneg (Real.rpow_nonneg (by norm_num) _) (by linarith)
      exact mul_nonneg (mul_nonneg hC hA) hj
    · push Not at h2
      have hb := hP.2 0 0 (by norm_num) X w hw
      have hmin : min 1 ‖w‖ = ‖w‖ := min_eq_right (by linarith)
      have e0 : ‖mixedJet 0 0 P X w‖ = |midPair P X w| := by
        unfold mixedJet; simp [norm_iteratedFDeriv_zero]
      rw [e0, hmin] at hb
      have hpw := r26t8a_p01_weight (d := d) hM (X := X) (z := w) (by linarith)
      have hpw0 := r26t8a_pairWeight_nonneg (d := d) M (X + (1 / 2 : ℝ) • w) (X - (1 / 2 : ℝ) • w)
      have hcc := hc ‖w‖ hwn (by linarith)
      have h1 : 1 + ‖w‖ ^ (-(σ + ((0 : ℕ) : ℝ))) * (1 + |Real.log ‖w‖|) ^ b ≤ 1 + c := by
        simp only [Nat.cast_zero, add_zero, neg_neg] at *
        have : ‖w‖ ^ (-σ) * (1 + |Real.log ‖w‖|) ^ b ≤ c := hcc
        linarith
      calc |midPair P X w| ≤ A * HRS.MS.Phase2S82.pairWeight M (X + (1 / 2 : ℝ) • w) (X - (1 / 2 : ℝ) • w) *
            (1 + ‖w‖ ^ (-(σ + ((0 : ℕ) : ℝ))) * (1 + |Real.log ‖w‖|) ^ b) := hb
        _ ≤ A * (3 ^ (2 * M) * jbracket X ^ (2 * M)) * (1 + c) := by
            have h1' : 0 ≤ 1 + ‖w‖ ^ (-(σ + ((0 : ℕ) : ℝ))) * (1 + |Real.log ‖w‖|) ^ b := by positivity
            exact mul_le_mul (mul_le_mul_of_nonneg_left hpw hA) h1 h1'
              (mul_nonneg hA (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (s83_jb_pos X).le _)))
        _ = _ := by ring
  · have hwn : 0 < ‖w‖ := norm_pos_iff.2 hw
    by_cases h2 : 1 / 2 < ‖w‖
    · have hz0 : (fun w => midPair P X w) =ᶠ[𝓝 w] fun _ => 0 := by
        filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds h2] with u hu
        exact hsupp _ _ (by
          have e : (X + (1 / 2 : ℝ) • u) - (X - (1 / 2 : ℝ) • u) = u := by module
          rw [e]; exact hu.le)
      rw [hz0.fderiv_eq, fderiv_const_apply, norm_zero]
      have := Real.rpow_nonneg hwn.le (-(1 : ℝ))
      have hj : 0 ≤ jbracket X ^ (2 * M) := Real.rpow_nonneg (s83_jb_pos X).le _
      have hC : 0 ≤ 3 ^ (2 * M) * (1 + c) := mul_nonneg (Real.rpow_nonneg (by norm_num) _) (by linarith)
      positivity
    · push Not at h2
      have hb := hP.2 0 1 (by norm_num) X w hw
      have hmin : min 1 ‖w‖ = ‖w‖ := min_eq_right (by linarith)
      have e1 : ‖mixedJet 0 1 P X w‖ = ‖fderiv ℝ (fun w => midPair P X w) w‖ := by
        have h := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := fun w => midPair P X w) (x := w) (n := 0)
        rw [norm_iteratedFDeriv_zero] at h
        unfold mixedJet
        rw [norm_iteratedFDeriv_zero]
        simpa using h.symm
      rw [e1, hmin] at hb
      have hpw := r26t8a_p01_weight (d := d) hM (X := X) (z := w) (by linarith)
      have hpw0 := r26t8a_pairWeight_nonneg (d := d) M (X + (1 / 2 : ℝ) • w) (X - (1 / 2 : ℝ) • w)
      have hcc := hc ‖w‖ hwn (by linarith)
      have hsplit : ‖w‖ ^ (-(σ + ((1 : ℕ) : ℝ))) = ‖w‖ ^ (-σ) * ‖w‖ ^ (-(1 : ℝ)) := by
        rw [← Real.rpow_add hwn]; congr 1; push_cast; ring
      have hr1 : 1 ≤ ‖w‖ ^ (-(1 : ℝ)) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hwn (by linarith) (by norm_num)
      have hr0 : 0 ≤ ‖w‖ ^ (-(1 : ℝ)) := by linarith
      have h1 : 1 + ‖w‖ ^ (-(σ + ((1 : ℕ) : ℝ))) * (1 + |Real.log ‖w‖|) ^ b ≤ (1 + c) * ‖w‖ ^ (-(1 : ℝ)) := by
        rw [hsplit]
        have : ‖w‖ ^ (-σ) * (1 + |Real.log ‖w‖|) ^ b ≤ c := hcc
        nlinarith [mul_le_mul_of_nonneg_right this hr0]
      calc ‖fderiv ℝ (fun w => midPair P X w) w‖ ≤ A * HRS.MS.Phase2S82.pairWeight M (X + (1 / 2 : ℝ) • w) (X - (1 / 2 : ℝ) • w) *
            (1 + ‖w‖ ^ (-(σ + ((1 : ℕ) : ℝ))) * (1 + |Real.log ‖w‖|) ^ b) := hb
        _ ≤ A * (3 ^ (2 * M) * jbracket X ^ (2 * M)) * ((1 + c) * ‖w‖ ^ (-(1 : ℝ))) := by
            have h1' : 0 ≤ 1 + ‖w‖ ^ (-(σ + ((1 : ℕ) : ℝ))) * (1 + |Real.log ‖w‖|) ^ b := by positivity
            exact mul_le_mul (mul_le_mul_of_nonneg_left hpw hA) h1 h1'
              (mul_nonneg hA (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (s83_jb_pos X).le _)))
        _ = _ := by ring

end HRS.MS.R26T8A
