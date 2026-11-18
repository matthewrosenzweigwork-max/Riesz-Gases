import HRS.Commutator.Torus.TKRAux9
import HRS.Commutator.Torus.TPOSAux10

/-!
# T-KR helpers, part 10: Lemma 3.1 on the torus (`kernel_remainder_T`)
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff

namespace HRS.Commutator.TorusNote

open HRS HRS.KernelGrad

variable {d : ℕ} {s : ℝ}

theorem tkr_remainder_c (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ x : Torus d, x ≠ 0 →
      KernelGrad.tdist x 0 * ‖ghiForceT s η x‖ ≤ C * Whole.fTrunc s η (KernelGrad.centeredRep x) := by
  have hd0 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hd2 : 2 ≤ d := by omega
  have hsd1 : s + 1 < (d : ℝ) := by linarith
  obtain ⟨c, C0, hc, hC0, hcmp⟩ := Whole.fcomparison (d := d) (s := s) hd hs0 hsd
  obtain ⟨Kn, hKn0, hKn⟩ := tkr_ghi_near hd2 hs0 hsd1
  have hN : s + 2 ≤ ((2 * d + 5 : ℕ) : ℝ) := by push_cast; linarith
  obtain ⟨Kf, hKf0, hKf⟩ := tkr_ghi_far hd hs0 hsd (2 * d + 5) hN
  set A : ℝ := 2 * Kn + Kf with hA
  refine ⟨(A + 1) / c, by positivity, fun η hη hη1 x hx => ?_⟩
  set r := KernelGrad.tdist x 0 with hr
  have hr0 : 0 < r := tdist_pos hx
  set y : Euc d := KernelGrad.centeredRep x with hy
  have hyn : ‖y‖ = r := (KernelGrad.tdist_zero_right x).symm
  have hy0 : y ≠ 0 := norm_pos_iff.1 (by rw [hyn]; exact hr0)
  have hw0 : η⁻¹ • y ≠ 0 := smul_ne_zero (inv_ne_zero hη.ne') hy0
  have hwn : ‖η⁻¹ • y‖ = r / η := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hη, inv_mul_eq_div, hyn]
  have hscale := tpos_fTrunc_scale (d := d) (s := s) hη y
  have hf0 : 0 ≤ Whole.fTrunc s η y := tpos_fTrunc_nonneg hs0 (by linarith) η y
  -- the key inequality: r ‖ghi‖ ≤ (A / c) η^{-s} f_1(w)
  have key : r * ‖ghiForceT s η x‖ ≤ (A / c) * (η ^ (-s) * Whole.fTrunc s 1 (η⁻¹ • y)) := by
    obtain ⟨h1, h2, h3⟩ := hcmp (η⁻¹ • y) hw0
    by_cases hrη : r ≤ η
    · -- near field
      have hw1 : ‖η⁻¹ • y‖ ≤ 1 := by rw [hwn, div_le_one hη]; exact hrη
      have hlow : c * r ^ (-s) ≤ η ^ (-s) * Whole.fTrunc s 1 (η⁻¹ • y) := by
        by_cases hs : s = 0
        · have h2' := (h2 hs hw1).1
          have : 1 ≤ 1 + |Real.log ‖η⁻¹ • y‖| := by linarith [abs_nonneg (Real.log ‖η⁻¹ • y‖)]
          subst hs
          simp only [neg_zero, Real.rpow_zero, one_mul, mul_one]
          calc c = c * 1 := (mul_one _).symm
            _ ≤ c * (1 + |Real.log ‖η⁻¹ • y‖|) := by gcongr
            _ ≤ _ := h2'
        · have hs' : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
          have h1' := (h1 hs' hw1).1
          rw [hwn] at h1'
          calc c * r ^ (-s) = η ^ (-s) * (c * (r / η) ^ (-s)) := by
                rw [Real.div_rpow hr0.le hη.le, Real.rpow_neg hr0.le, Real.rpow_neg hη.le]
                field_simp
            _ ≤ η ^ (-s) * Whole.fTrunc s 1 (η⁻¹ • y) :=
                mul_le_mul_of_nonneg_left h1' (Real.rpow_nonneg hη.le _)
      have hn := hKn η hη hη1 x hx
      have e1 : r * (r ^ (-s - 1)) = r ^ (-s) := by
        have := Real.rpow_add hr0 1 (-s - 1)
        rw [Real.rpow_one] at this
        rw [← this]; congr 1; ring
      have e2 : r * η ^ (-(s + 1)) ≤ r ^ (-s) := by
        have h5 : r * η ^ (-(s + 1)) ≤ η * η ^ (-(s + 1)) := mul_le_mul_of_nonneg_right hrη (Real.rpow_nonneg hη.le _)
        have h6 : η * η ^ (-(s + 1)) = η ^ (-s) := by
          have := Real.rpow_add hη 1 (-(s + 1))
          rw [Real.rpow_one] at this
          rw [← this]; congr 1; ring
        have h7 : η ^ (-s) ≤ r ^ (-s) := Real.rpow_le_rpow_of_nonpos hr0 hrη (by linarith)
        linarith
      have hA' : r * ‖ghiForceT s η x‖ ≤ 2 * Kn * r ^ (-s) := by
        calc r * ‖ghiForceT s η x‖ ≤ r * (Kn * (r ^ (-s - 1) + η ^ (-(s + 1)))) :=
              mul_le_mul_of_nonneg_left hn hr0.le
          _ = Kn * (r * r ^ (-s - 1)) + Kn * (r * η ^ (-(s + 1))) := by ring
          _ ≤ Kn * r ^ (-s) + Kn * r ^ (-s) := by
              rw [e1]; gcongr
          _ = 2 * Kn * r ^ (-s) := by ring
      calc r * ‖ghiForceT s η x‖ ≤ 2 * Kn * r ^ (-s) := hA'
        _ ≤ A * r ^ (-s) := by
            have : 0 ≤ r ^ (-s) := Real.rpow_nonneg hr0.le _
            nlinarith [hKf0]
        _ = (A / c) * (c * r ^ (-s)) := by field_simp
        _ ≤ (A / c) * (η ^ (-s) * Whole.fTrunc s 1 (η⁻¹ • y)) :=
            mul_le_mul_of_nonneg_left hlow (by positivity)
    · -- far field
      have hrη' : η < r := not_le.1 hrη
      have hw1 : 1 ≤ ‖η⁻¹ • y‖ := by rw [hwn, le_div_iff₀ hη]; linarith
      have h3' := (h3 hw1).1
      rw [hwn] at h3'
      set M : ℕ := 2 * d + 4 with hM
      have hMr : (2 * (d : ℝ) + 4) = (M : ℝ) := by rw [hM]; push_cast; ring
      have hfar := hKf η hη hη1 x hx
      have hexp : ((2 * d + 5 : ℕ) : ℝ) - (s + 1) = (M : ℝ) - s := by rw [hM]; push_cast; ring
      rw [hexp] at hfar
      have hpow : r ^ (2 * d + 5) = r * r ^ M := by rw [hM]; ring
      rw [hpow] at hfar
      have hrM : 0 < r ^ M := pow_pos hr0 M
      have hlow : c * (η ^ M / r ^ M) * η ^ (-s) ≤ η ^ (-s) * Whole.fTrunc s 1 (η⁻¹ • y) := by
        have : c * (r / η) ^ (-(2 * (d : ℝ) + 4)) = c * (η ^ M / r ^ M) := by
          rw [hMr, Real.rpow_neg (by positivity), Real.rpow_natCast, div_pow, inv_div]
        rw [this] at h3'
        rw [mul_comm (η ^ (-s))]
        calc c * (η ^ M / r ^ M) * η ^ (-s) ≤ Whole.fTrunc s 1 (η⁻¹ • y) * η ^ (-s) :=
              mul_le_mul_of_nonneg_right h3' (Real.rpow_nonneg hη.le _)
          _ = _ := by ring
      have hrg : r * ‖ghiForceT s η x‖ ≤ Kf * (η ^ M * η ^ (-s)) / r ^ M := by
        rw [le_div_iff₀ hrM]
        have : η ^ ((M : ℝ) - s) = η ^ M * η ^ (-s) := by
          rw [sub_eq_add_neg, Real.rpow_add hη, Real.rpow_natCast]
        rw [← this]
        calc r * ‖ghiForceT s η x‖ * r ^ M = r ^ M * r * ‖ghiForceT s η x‖ := by ring
          _ = r * r ^ M * ‖ghiForceT s η x‖ := by ring
          _ ≤ _ := hfar
      calc r * ‖ghiForceT s η x‖ ≤ Kf * (η ^ M * η ^ (-s)) / r ^ M := hrg
        _ ≤ A * (η ^ M * η ^ (-s)) / r ^ M := by
            gcongr
            nlinarith [hKn0]
        _ = (A / c) * (c * (η ^ M / r ^ M) * η ^ (-s)) := by field_simp
        _ ≤ (A / c) * (η ^ (-s) * Whole.fTrunc s 1 (η⁻¹ • y)) :=
            mul_le_mul_of_nonneg_left hlow (by positivity)
  calc r * ‖ghiForceT s η x‖ ≤ (A / c) * (η ^ (-s) * Whole.fTrunc s 1 (η⁻¹ • y)) := key
    _ = (A / c) * Whole.fTrunc s η y := by rw [hscale]
    _ ≤ (A + 1) / c * Whole.fTrunc s η y := by
        have : (A + 1) / c = A / c + 1 / c := by ring
        rw [this]
        nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ 1 / c) hf0]

theorem tkr_kernel_remainder (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ x : Torus d, x ≠ 0 →
      KernelGrad.tdist x 0 * ‖ghiForceT s η x‖ ≤ C * tScale s * perio (Whole.fTrunc s η) x := by
  obtain ⟨C, hC, h⟩ := tkr_remainder_c hd hs0 hsd
  have hts := tpos_tScale_pos hs0
  refine ⟨C / tScale s, by positivity, fun η hη hη1 x hx => ?_⟩
  have hge := tpos_perio_ge (d := d) hs0 hsd hη x
  calc KernelGrad.tdist x 0 * ‖ghiForceT s η x‖ ≤ C * Whole.fTrunc s η (KernelGrad.centeredRep x) :=
        h η hη hη1 x hx
    _ ≤ C * perio (Whole.fTrunc s η : Euc d → ℝ) x := mul_le_mul_of_nonneg_left hge hC.le
    _ = C / tScale s * tScale s * perio (Whole.fTrunc s η : Euc d → ℝ) x := by field_simp

end HRS.Commutator.TorusNote
