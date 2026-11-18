import HRS.MS.MovEntAux6
import HRS.MS.LogRegAux1
import HRS.MS.ThmCoreAux1
import HRS.MH.CoercLowerB1

/-!
# S6.6, packet P6 (part 4): the potential of a zero-mass Gaussian-decaying density is bounded

`s66_pot_bdd`: for two probability densities `ρ₁, ρ₂` with Gaussian bounds, `g * ρ₁ - g * ρ₂` is bounded on `ℝ^d` (`g = rieszKernel d s`);
at `s = 0` this is the cancellation of the logarithmic growth by the zero mass of `ρ₁ - ρ₂` (S L4600-4610 "its zero-mass input and finite
moments remove the growth at infinity"); at `s > 0` both potentials are bounded (`convMeasure_bound_of_le`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.MovEnt

open HRS.Whole

variable {d : ℕ}

theorem s66_logk_bound (x y : Euc d) :
    |Real.log (2 + ‖x‖) - Real.log ‖x - y‖| ≤
      Real.log (3 + ‖y‖) + (if ‖x - y‖ < 1 then |Real.log ‖x - y‖| + Real.log (2 + ‖x‖) else 0) := by
  have hX := norm_nonneg x
  have hY := norm_nonneg y
  have hL0 : 0 ≤ Real.log (2 + ‖x‖) := Real.log_nonneg (by linarith)
  have hL3 : 0 ≤ Real.log (3 + ‖y‖) := Real.log_nonneg (by linarith)
  by_cases hr : ‖x - y‖ < 1
  · rw [if_pos hr]
    have : |Real.log (2 + ‖x‖) - Real.log ‖x - y‖| ≤ |Real.log (2 + ‖x‖)| + |Real.log ‖x - y‖| :=
      abs_sub _ _
    rw [abs_of_nonneg hL0] at this
    linarith
  · rw [if_neg hr]
    push Not at hr
    set r := ‖x - y‖ with hrdef
    have h1 : r ≤ ‖x‖ + ‖y‖ := by
      calc r = ‖x - y‖ := rfl
        _ ≤ ‖x‖ + ‖y‖ := norm_sub_le _ _
    have h2 : ‖x‖ ≤ r + ‖y‖ := by
      calc ‖x‖ = ‖(x - y) + y‖ := by congr 1; abel
        _ ≤ ‖x - y‖ + ‖y‖ := norm_add_le _ _
    have hr0 : 0 < r := by linarith
    rw [abs_le]
    constructor
    · -- lower bound: log r ≤ log(2+‖x‖) + log(2+‖y‖)
      have h3 : r ≤ (2 + ‖x‖) * (2 + ‖y‖) := by nlinarith
      have h4 : Real.log r ≤ Real.log (2 + ‖x‖) + Real.log (2 + ‖y‖) := by
        rw [← Real.log_mul (by linarith) (by linarith)]
        exact Real.log_le_log hr0 h3
      have h5 : Real.log (2 + ‖y‖) ≤ Real.log (3 + ‖y‖) :=
        Real.log_le_log (by linarith) (by linarith)
      linarith
    · -- upper bound: log(2+‖x‖) ≤ log r + log(3+‖y‖)
      have h3 : 2 + ‖x‖ ≤ r * (3 + ‖y‖) := by nlinarith
      have h4 : Real.log (2 + ‖x‖) ≤ Real.log r + Real.log (3 + ‖y‖) := by
        rw [← Real.log_mul hr0.ne' (by linarith)]
        exact Real.log_le_log (by linarith) h3
      linarith

/-- `|h| ≤ A e^{-c|y|²}` gives `(1+|y|)^n |h y| ≤ C₀`. -/
theorem s66_poly_decay {A c : ℝ} (hA : 0 ≤ A) (hc : 0 < c) {h : Euc d → ℝ}
    (hb : ∀ y, |h y| ≤ A * Real.exp (-c * ‖y‖ ^ 2)) (n : ℕ) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ y, (1 + ‖y‖) ^ n * |h y| ≤ C₀ := by
  obtain ⟨B, hB0, hB⟩ := s66_poly_gauss (d := d) hc n
  refine ⟨2 ^ n * A * B, by positivity, fun y => ?_⟩
  have h1 : (1 + ‖y‖) ^ n ≤ 2 ^ n * movBracket y ^ n := by
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ n
    have := s66_one_le_bracket y
    unfold movBracket at *
    have h2 : (1 + ‖y‖) ^ 2 ≤ 4 * (1 + ‖y‖ ^ 2) := by nlinarith [norm_nonneg y, sq_nonneg (1 - ‖y‖)]
    have h3 : 1 + ‖y‖ ≤ 2 * Real.sqrt (1 + ‖y‖ ^ 2) := by
      have : (1 + ‖y‖) ^ 2 ≤ (2 * Real.sqrt (1 + ‖y‖ ^ 2)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by positivity)]; nlinarith
      exact abs_le_of_sq_le_sq' this (by positivity) |>.2
    exact h3
  calc (1 + ‖y‖) ^ n * |h y| ≤ (2 ^ n * movBracket y ^ n) * (A * Real.exp (-c * ‖y‖ ^ 2)) :=
        mul_le_mul h1 (hb y) (abs_nonneg _)
          (mul_nonneg (by positivity) (pow_nonneg (by linarith [s66_one_le_bracket y]) _))
    _ = 2 ^ n * A * (movBracket y ^ n * Real.exp (-c * ‖y‖ ^ 2)) := by ring
    _ ≤ 2 ^ n * A * B := mul_le_mul_of_nonneg_left (hB y) (by positivity)

/-- The logarithmic potential of a zero-mass, Gaussian-decaying function is bounded. -/
theorem s66_logpot_bdd (hd : 1 ≤ d) {A c : ℝ} (hA : 0 ≤ A) (hc : 0 < c) {h : Euc d → ℝ}
    (hm : Measurable h) (hint : Integrable h) (h0 : ∫ y, h y = 0)
    (hb : ∀ y, |h y| ≤ A * Real.exp (-c * ‖y‖ ^ 2)) :
    ∃ B : ℝ, ∀ x : Euc d, |∫ y, rieszKernel d 0 (x - y) * h y| ≤ B := by
  obtain ⟨C₀, hC₀0, hC₀⟩ := s66_poly_decay hA hc hb (d + 1)
  obtain ⟨C₁, hC₁0, hC₁⟩ := s66_poly_decay hA hc hb (d + 2)
  have hφ : ∀ y, ‖h y‖ ≤ C₀ * HRS.MS.LogReg.lreg_phi d y := by
    intro y
    have := hC₀ y
    unfold HRS.MS.LogReg.lreg_phi
    have hp : (0 : ℝ) < (1 + ‖y‖) ^ (d + 1) := by positivity
    rw [Real.norm_eq_abs, ← div_eq_mul_inv, le_div_iff₀ hp]
    linarith
  have hφ1 : ∀ y, (1 + ‖y‖) * |h y| ≤ C₁ * HRS.MS.LogReg.lreg_phi d y := by
    intro y
    have := hC₁ y
    unfold HRS.MS.LogReg.lreg_phi
    have hp : (0 : ℝ) < (1 + ‖y‖) ^ (d + 1) := by positivity
    rw [← div_eq_mul_inv, le_div_iff₀ hp]
    calc (1 + ‖y‖) * |h y| * (1 + ‖y‖) ^ (d + 1) = (1 + ‖y‖) ^ (d + 2) * |h y| := by ring
      _ ≤ C₁ := this
  set Iφ : ℝ := ∫ y, HRS.MS.LogReg.lreg_phi d y with hIφ
  have hIφ0 : 0 ≤ Iφ := integral_nonneg fun y => (HRS.MS.LogReg.lreg_phi_pos y).le
  refine ⟨7 * C₁ * Iφ + 2 * (C₀ * HRS.MS.LogReg.lreg_A d (1 / 2)), fun x => ?_⟩
  set L : ℝ := Real.log (2 + ‖x‖) with hL
  have hL0 : 0 ≤ L := Real.log_nonneg (by linarith [norm_nonneg x])
  -- the integrand with the subtracted constant
  set k : Euc d → ℝ := fun y => L - Real.log ‖x - y‖ with hk
  have hgk : ∀ y, rieszKernel d 0 (x - y) * h y = k y * h y - L * h y := by
    intro y
    simp only [rieszKernel, if_true, hk]
    ring
  -- majorant
  set Φ : Euc d → ℝ := fun y => 3 * (C₁ * HRS.MS.LogReg.lreg_phi d y) +
      4 * (C₁ * HRS.MS.LogReg.lreg_phi d y) +
      2 * (‖x - y‖ ^ (-(1 / 2 : ℝ)) * |h y|) with hΦ
  have hphiI : Integrable (HRS.MS.LogReg.lreg_phi d) := HRS.MS.LogReg.lreg_phi_integrable
  have hhm : AEStronglyMeasurable h volume := hm.aestronglyMeasurable
  obtain ⟨hKi, hKb⟩ := HRS.MS.LogReg.lreg_K_dom hd (σ := 1 / 2) (by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith) (by norm_num) hC₀0 hhm hφ x
  have hsing : Integrable (fun y : Euc d => ‖x - y‖ ^ (-(1 / 2 : ℝ)) * |h y|) := by
    have := (hKi.comp_sub_left x)
    refine this.congr (Eventually.of_forall fun y => ?_)
    simp [Real.norm_eq_abs]
  have hsingb : ∫ y, ‖x - y‖ ^ (-(1 / 2 : ℝ)) * |h y| ≤ C₀ * HRS.MS.LogReg.lreg_A d (1 / 2) := by
    have e : ∫ y, ‖x - y‖ ^ (-(1 / 2 : ℝ)) * |h y| = ∫ z, ‖z‖ ^ (-(1 / 2 : ℝ)) * ‖h (x - z)‖ := by
      rw [← integral_sub_left_eq_self (fun z => ‖z‖ ^ (-(1 / 2 : ℝ)) * ‖h (x - z)‖) volume x]
      simp [Real.norm_eq_abs]
    rw [e]; exact hKb
  have hΦi : Integrable Φ := by
    refine (((hphiI.const_mul C₁).const_mul 3).add ((hphiI.const_mul C₁).const_mul 4)).add (hsing.const_mul 2)
  have hkm : Measurable k := by
    simp only [hk]; fun_prop
  have hkhi : Integrable (fun y => k y * h y) ∨ ¬ Integrable (fun y => rieszKernel d 0 (x - y) * h y) := by
    by_cases hI : Integrable (fun y => rieszKernel d 0 (x - y) * h y)
    · left
      have : (fun y => k y * h y) = fun y => rieszKernel d 0 (x - y) * h y + L * h y := by
        funext y; rw [hgk y]; ring
      rw [this]; exact hI.add (hint.const_mul L)
    · right; exact hI
  rcases hkhi with hkI | hnot
  · have hpt : ∀ y, ‖k y * h y‖ ≤ Φ y := by
      intro y
      have hkb := s66_logk_bound x y
      rw [norm_mul, Real.norm_eq_abs]
      have hh0 := abs_nonneg (h y)
      by_cases hr : ‖x - y‖ < 1
      · rw [if_pos hr] at hkb
        have hlogr : |Real.log ‖x - y‖| ≤ 2 * ‖x - y‖ ^ (-(1 / 2 : ℝ)) := by
          rcases (norm_nonneg (x - y)).eq_or_lt with hz | hpos
          · -- at `y = x` the log is the junk value 0
            rw [← hz]; simp [Real.zero_rpow]
          have h1 : -Real.log ‖x - y‖ ≤ 2 * ‖x - y‖ ^ (-(1 / 2 : ℝ)) := by
            have e : -Real.log ‖x - y‖ = 2 * Real.log (‖x - y‖ ^ (-(1 / 2 : ℝ))) := by
              rw [Real.log_rpow hpos]; ring
            rw [e]
            have := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hpos (-(1 / 2 : ℝ)))
            linarith
          have h2 : Real.log ‖x - y‖ ≤ 0 := Real.log_nonpos (norm_nonneg _) hr.le
          rw [abs_of_nonpos h2]
          exact h1
        have hLy : L ≤ 4 * (1 + ‖y‖) := by
          have : L ≤ 2 + ‖x‖ := by
            have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 + ‖x‖ by linarith [norm_nonneg x])
            linarith
          have hxy : ‖x‖ ≤ ‖y‖ + 1 := by
            have : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by
              calc ‖x‖ = ‖(x - y) + y‖ := by congr 1; abel
                _ ≤ _ := norm_add_le _ _
            linarith
          nlinarith [norm_nonneg y]
        have hl3 : Real.log (3 + ‖y‖) ≤ 3 * (1 + ‖y‖) := by
          have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 + ‖y‖ by linarith [norm_nonneg y])
          nlinarith [norm_nonneg y]
        have hb1 := hφ1 y
        calc |k y| * |h y| ≤ (Real.log (3 + ‖y‖) + (|Real.log ‖x - y‖| + L)) * |h y| := by
              refine mul_le_mul_of_nonneg_right ?_ hh0
              simpa [hk] using hkb
          _ ≤ (3 * (1 + ‖y‖) + (2 * ‖x - y‖ ^ (-(1 / 2 : ℝ)) + 4 * (1 + ‖y‖))) * |h y| := by
              refine mul_le_mul_of_nonneg_right ?_ hh0
              linarith
          _ = 3 * ((1 + ‖y‖) * |h y|) + 4 * ((1 + ‖y‖) * |h y|) + 2 * (‖x - y‖ ^ (-(1 / 2 : ℝ)) * |h y|) := by
              ring
          _ ≤ Φ y := by
              simp only [hΦ]
              nlinarith
      · rw [if_neg hr] at hkb
        have hl3 : Real.log (3 + ‖y‖) ≤ 3 * (1 + ‖y‖) := by
          have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 + ‖y‖ by linarith [norm_nonneg y])
          nlinarith [norm_nonneg y]
        have hb1 := hφ1 y
        have hs0 : 0 ≤ ‖x - y‖ ^ (-(1 / 2 : ℝ)) * |h y| :=
          mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) hh0
        have h4 : 0 ≤ C₁ * HRS.MS.LogReg.lreg_phi d y := mul_nonneg hC₁0 (HRS.MS.LogReg.lreg_phi_pos y).le
        calc |k y| * |h y| ≤ (Real.log (3 + ‖y‖) + 0) * |h y| := by
              refine mul_le_mul_of_nonneg_right ?_ hh0
              simpa [hk] using hkb
          _ ≤ 3 * ((1 + ‖y‖) * |h y|) := by nlinarith
          _ ≤ Φ y := by
              simp only [hΦ]
              linarith
    have hbound : ‖∫ y, k y * h y‖ ≤ ∫ y, Φ y := norm_integral_le_of_norm_le hΦi (ae_of_all _ hpt)
    have hΦint : ∫ y, Φ y ≤ 7 * C₁ * Iφ + 2 * (C₀ * HRS.MS.LogReg.lreg_A d (1 / 2)) := by
      have e : ∫ y, Φ y = 3 * (C₁ * Iφ) + 4 * (C₁ * Iφ) + 2 * ∫ y, ‖x - y‖ ^ (-(1 / 2 : ℝ)) * |h y| := by
        have i1 : Integrable (fun y : Euc d => 3 * (C₁ * HRS.MS.LogReg.lreg_phi d y)) :=
          (hphiI.const_mul C₁).const_mul 3
        have i2 : Integrable (fun y : Euc d => 4 * (C₁ * HRS.MS.LogReg.lreg_phi d y)) :=
          (hphiI.const_mul C₁).const_mul 4
        have i3 : Integrable (fun y : Euc d => 2 * (‖x - y‖ ^ (-(1 / 2 : ℝ)) * |h y|)) :=
          hsing.const_mul 2
        have i12 : Integrable (fun y : Euc d => 3 * (C₁ * HRS.MS.LogReg.lreg_phi d y) +
            4 * (C₁ * HRS.MS.LogReg.lreg_phi d y)) := i1.add i2
        simp only [hΦ]
        rw [integral_add i12 i3, integral_add i1 i2,
          integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul]
      rw [e]
      nlinarith
    have hid : ∫ y, rieszKernel d 0 (x - y) * h y = ∫ y, k y * h y := by
      have : ∫ y, k y * h y = ∫ y, (rieszKernel d 0 (x - y) * h y + L * h y) := by
        congr 1; funext y; rw [hgk y]; ring
      rw [this]
      have hI : Integrable (fun y => rieszKernel d 0 (x - y) * h y) := by
        have e : (fun y => rieszKernel d 0 (x - y) * h y) = fun y => k y * h y - L * h y := funext hgk
        rw [e]; exact hkI.sub (hint.const_mul L)
      rw [integral_add hI (hint.const_mul L), integral_const_mul, h0]
      ring
    rw [hid, ← Real.norm_eq_abs]
    exact hbound.trans hΦint
  · rw [integral_undef hnot]
    simp only [abs_zero]
    have := HRS.MS.LogReg.lreg_A_nonneg (d := d) (σ := 1 / 2)
    positivity

end HRS.MS.MovEnt

end
