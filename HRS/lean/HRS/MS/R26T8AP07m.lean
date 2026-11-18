import HRS.MS.R26T8AP07g

/-!
# S8.2 local Newton layer, packet T8A.P07 (part m): termwise nested bound of the annular Newton pieces
`r26t8a_p07_beta` is the dyadic envelope of the `n`-th piece at relative radius `rho`; `r26t8a_p07_term_bound` (`0 <= sigma < d`):
`‖nest p q (annularNewton (1/2)^n) X w‖ <= C A <X>^(2M) beta_q(|w|)` for every `n` (this is the termwise inequality inside `r26t8a_p07_series_bound`).
-/

set_option autoImplicit false
noncomputable section
open Filter Topology
open HRS HRS.Whole HRS.MS.Phase2S82

namespace HRS.MS.R26T8A

variable {d : ℕ}

def r26t8a_p07_beta (d b q : ℕ) (σ rho : ℝ) (n : ℕ) : ℝ :=
  if ((1 : ℝ) / 2) ^ n ≤ rho / 4 then
    ((((1 : ℝ) / 2) ^ n) ^ ((d : ℝ) - σ) * rho ^ (2 - (d : ℝ) - q)) * (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b *
      (if d = 2 ∧ q = 0 then 1 + |Real.log (((1 : ℝ) / 2) ^ n)| + |Real.log rho| else 1)
  else (((1 : ℝ) / 2) ^ n) ^ (2 - σ - q) * (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b *
    (if d = 2 ∧ q = 0 then 1 + |Real.log (((1 : ℝ) / 2) ^ n)| else 1)

theorem r26t8a_p07_term_bound (hd : 2 ≤ d) (k b : ℕ) (nu M σ : ℝ) (hnu : 0 < nu) (hM : 0 ≤ M) (hσd : σ < d) {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 0 ≤ A → ∀ F : Euc d → Euc d → ℝ, ConormalP k b M σ A F →
      ∀ n p q : ℕ, p + q ≤ k → ∀ X w : Euc d, 0 < ‖w‖ →
        ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q
          (r26t8a_annularNewton nu chi (((1 : ℝ) / 2) ^ n) F Y) w) X‖ ≤
          C * A * jbracket X ^ (2 * M) * r26t8a_p07_beta d b q σ ‖w‖ n := by
  obtain ⟨C3, hC30, hC3⟩ := r26t8a_p03P d hd k b nu M σ hnu hM hσd chi hchi
  obtain ⟨C5, hC50, hC5⟩ := r26t8a_conv_boundP (k := k) (b := b) hd hM hchi nu
  refine ⟨C3 + C5, by positivity, fun A hA F hF n p q hpq X w hw => ?_⟩
  set r : ℝ := ‖w‖ with hr
  have hR : 0 < ((1 : ℝ) / 2) ^ n := by positivity
  have hR1 : ((1 : ℝ) / 2) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hjb : 0 ≤ jbracket X ^ (2 * M) := Real.rpow_nonneg (by unfold jbracket; positivity) _
  have hl : 0 ≤ (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b := by positivity
  have hAj : 0 ≤ A * jbracket X ^ (2 * M) := mul_nonneg hA hjb
  by_cases h : ((1 : ℝ) / 2) ^ n ≤ r / 4
  · have := hC3 A hA F hF (((1 : ℝ) / 2) ^ n) hR hR1 X w (norm_pos_iff.1 hw) (by linarith) p q hpq
    simp only [r26t8a_p07_beta, if_pos h]
    refine this.trans ?_
    have hpos : 0 ≤ (((1 : ℝ) / 2) ^ n) ^ ((d : ℝ) - σ) * r ^ (2 - (d : ℝ) - q) *
        (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b *
        (if d = 2 ∧ q = 0 then 1 + |Real.log (((1 : ℝ) / 2) ^ n)| + |Real.log r| else 1) := by
      split_ifs <;> positivity
    calc C3 * A * jbracket X ^ (2 * M) * ((((1 : ℝ) / 2) ^ n) ^ ((d : ℝ) - σ) * ‖w‖ ^ (2 - (d : ℝ) - q)) *
          (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b *
          (if d = 2 ∧ q = 0 then 1 + |Real.log (((1 : ℝ) / 2) ^ n)| + |Real.log ‖w‖| else 1)
        = C3 * (A * jbracket X ^ (2 * M)) * ((((1 : ℝ) / 2) ^ n) ^ ((d : ℝ) - σ) * r ^ (2 - (d : ℝ) - q) *
          (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b *
          (if d = 2 ∧ q = 0 then 1 + |Real.log (((1 : ℝ) / 2) ^ n)| + |Real.log r| else 1)) := by rw [hr]; ring
      _ ≤ (C3 + C5) * (A * jbracket X ^ (2 * M)) * ((((1 : ℝ) / 2) ^ n) ^ ((d : ℝ) - σ) * r ^ (2 - (d : ℝ) - q) *
          (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b *
          (if d = 2 ∧ q = 0 then 1 + |Real.log (((1 : ℝ) / 2) ^ n)| + |Real.log r| else 1)) := by
          refine mul_le_mul_of_nonneg_right ?_ hpos
          nlinarith [mul_nonneg hC50 hAj]
      _ = _ := by ring
  · have := hC5 A hA F hF (((1 : ℝ) / 2) ^ n) hR hR1 w (by rw [← hr]; linarith [not_le.1 h]) p q hpq X
    simp only [r26t8a_p07_beta, if_neg h]
    refine this.trans ?_
    have hpos : 0 ≤ (((1 : ℝ) / 2) ^ n) ^ (2 - σ - (q : ℝ)) * (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b *
        (if d = 2 ∧ q = 0 then 1 + |Real.log (((1 : ℝ) / 2) ^ n)| else 1) := by
      split_ifs <;> positivity
    calc C5 * A * jbracket X ^ (2 * M) * (((1 : ℝ) / 2) ^ n) ^ (2 - σ - (q : ℝ)) *
          (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b * (if d = 2 ∧ q = 0 then 1 + |Real.log (((1 : ℝ) / 2) ^ n)| else 1)
        = C5 * (A * jbracket X ^ (2 * M)) * ((((1 : ℝ) / 2) ^ n) ^ (2 - σ - (q : ℝ)) *
          (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b * (if d = 2 ∧ q = 0 then 1 + |Real.log (((1 : ℝ) / 2) ^ n)| else 1)) := by ring
      _ ≤ (C3 + C5) * (A * jbracket X ^ (2 * M)) * ((((1 : ℝ) / 2) ^ n) ^ (2 - σ - (q : ℝ)) *
          (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b * (if d = 2 ∧ q = 0 then 1 + |Real.log (((1 : ℝ) / 2) ^ n)| else 1)) := by
          refine mul_le_mul_of_nonneg_right ?_ hpos
          nlinarith [mul_nonneg hC30 hAj]
      _ = _ := by ring

end HRS.MS.R26T8A
