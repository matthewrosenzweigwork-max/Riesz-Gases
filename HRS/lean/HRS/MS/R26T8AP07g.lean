import HRS.MS.R26T8AP07f
import HRS.MS.R26T8AP05
import HRS.MS.R26T8AP03P
import HRS.MS.R26T8AP05gP

/-!
# S8.2 local Newton layer, packet T8A.P07 (part g): the dyadic series of nested jets of the annular Newton integrals (case `0 <= sigma < d`)
`r26t8a_p07_series_bound`: for `0 < |w| <= 2` the nested jets of `annularNewton nu chi (1/2)^n F` are absolutely summable in `n`, with
sum `<= C A <X>^(2M) (1 + |w|^(2-sigma-q) (1+|log|w||)^(b+1))`  (P03 for `4 R <= |w|`, `r26t8a_conv_bound` otherwise, then `r26t8a_p07_envI/II`).
-/

set_option autoImplicit false
noncomputable section
open Filter Topology
open HRS HRS.Whole HRS.MS.Phase2S82

namespace HRS.MS.R26T8A

variable {d : ℕ}

theorem r26t8a_p07_series_bound (hd : 2 ≤ d) (k b : ℕ) (nu M σ : ℝ) (hnu : 0 < nu) (hM : 0 ≤ M) (hσd : σ < d) {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 0 ≤ A → ∀ F : Euc d → Euc d → ℝ, ConormalP k b M σ A F →
      ∀ p q : ℕ, p + q ≤ k → ∀ X w : Euc d, 0 < ‖w‖ → ‖w‖ ≤ 4 →
        Summable (fun n : ℕ => ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q
          (r26t8a_annularNewton nu chi (((1 : ℝ) / 2) ^ n) F Y) w) X‖) ∧
        ∑' n : ℕ, ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q
          (r26t8a_annularNewton nu chi (((1 : ℝ) / 2) ^ n) F Y) w) X‖ ≤
          C * A * jbracket X ^ (2 * M) * (1 + ‖w‖ ^ (2 - σ - (q : ℝ)) * (1 + |Real.log ‖w‖|) ^ (b + 1)) := by
  obtain ⟨C3, hC30, hC3⟩ := r26t8a_p03P d hd k b nu M σ hnu hM hσd chi hchi
  obtain ⟨C5, hC50, hC5⟩ := r26t8a_conv_boundP (k := k) (b := b) hd hM hchi nu
  choose CI hCI0 hCI using fun q : ℕ => r26t8a_p07_envI d hd σ hσd q b
  choose CII hCII0 hCII using fun q : ℕ => r26t8a_p07_envII d hd σ hσd q b
  set Ce : ℝ := ∑ q ∈ Finset.range (k + 1), (CI q + CII q) with hCe
  have hCe0 : 0 ≤ Ce := Finset.sum_nonneg fun q _ => add_nonneg (hCI0 q) (hCII0 q)
  refine ⟨2 * ((C3 + C5) * Ce), by positivity, fun A hA F hF p q hpq X w hw hw2 => ?_⟩
  set r : ℝ := ‖w‖ with hr
  have hqk : q ≤ k := by omega
  have hCIq : CI q ≤ Ce := le_trans (le_add_of_nonneg_right (hCII0 q))
    (Finset.single_le_sum (f := fun q => CI q + CII q) (fun i _ => add_nonneg (hCI0 i) (hCII0 i))
      (Finset.mem_range.2 (by omega)))
  have hCIIq : CII q ≤ Ce := le_trans (le_add_of_nonneg_left (hCI0 q))
    (Finset.single_le_sum (f := fun q => CI q + CII q) (fun i _ => add_nonneg (hCI0 i) (hCII0 i))
      (Finset.mem_range.2 (by omega)))
  obtain ⟨sI, hI⟩ := hCI q r hw hw2
  obtain ⟨sII, hII⟩ := hCII q r hw hw2
  set β : ℕ → ℝ := fun n => if ((1 : ℝ) / 2) ^ n ≤ r / 4 then
      ((((1 : ℝ) / 2) ^ n) ^ ((d : ℝ) - σ) * r ^ (2 - (d : ℝ) - q)) * (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b *
        (if d = 2 ∧ q = 0 then 1 + |Real.log (((1 : ℝ) / 2) ^ n)| + |Real.log r| else 1)
    else (((1 : ℝ) / 2) ^ n) ^ (2 - σ - q) * (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b *
        (if d = 2 ∧ q = 0 then 1 + |Real.log (((1 : ℝ) / 2) ^ n)| else 1) with hβ
  have hβsplit : β = fun n => (if ((1 : ℝ) / 2) ^ n ≤ r / 4 then
      ((((1 : ℝ) / 2) ^ n) ^ ((d : ℝ) - σ) * r ^ (2 - (d : ℝ) - q)) * (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b *
        (if d = 2 ∧ q = 0 then 1 + |Real.log (((1 : ℝ) / 2) ^ n)| + |Real.log r| else 1) else 0) +
      (if r / 4 < ((1 : ℝ) / 2) ^ n then
        (((1 : ℝ) / 2) ^ n) ^ (2 - σ - q) * (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b *
          (if d = 2 ∧ q = 0 then 1 + |Real.log (((1 : ℝ) / 2) ^ n)| else 1) else 0) := by
    funext n
    by_cases h : ((1 : ℝ) / 2) ^ n ≤ r / 4
    · simp only [hβ, if_pos h, if_neg (not_lt.2 h), add_zero]
    · simp only [hβ, if_neg h, if_pos (not_le.1 h), zero_add]
  have hβs : Summable β := by rw [hβsplit]; exact sI.add sII
  have hβ0 : ∀ n, 0 ≤ β n := fun n => by
    simp only [hβ]
    have hl : 0 ≤ 1 + |Real.log (((1 : ℝ) / 2) ^ n)| := by positivity
    split_ifs <;> positivity
  have hpt : ∀ n : ℕ, ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q
      (r26t8a_annularNewton nu chi (((1 : ℝ) / 2) ^ n) F Y) w) X‖ ≤ (C3 + C5) * A * jbracket X ^ (2 * M) * β n := by
    intro n
    have hR : 0 < ((1 : ℝ) / 2) ^ n := by positivity
    have hR1 : ((1 : ℝ) / 2) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hjb : 0 ≤ jbracket X ^ (2 * M) := Real.rpow_nonneg (by unfold jbracket; positivity : (0:ℝ) < jbracket X).le _
    have hl : 0 ≤ (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b := by positivity
    by_cases h : ((1 : ℝ) / 2) ^ n ≤ r / 4
    · have := hC3 A hA F hF (((1 : ℝ) / 2) ^ n) hR hR1 X w (norm_pos_iff.1 hw) (by linarith) p q hpq
      simp only [hβ, if_pos h]
      refine this.trans ?_
      have hpos : 0 ≤ (((1 : ℝ) / 2) ^ n) ^ ((d : ℝ) - σ) * r ^ (2 - (d : ℝ) - q) * (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b *
          (if d = 2 ∧ q = 0 then 1 + |Real.log (((1 : ℝ) / 2) ^ n)| + |Real.log r| else 1) := by
        split_ifs <;> positivity
      calc C3 * A * jbracket X ^ (2 * M) * ((((1 : ℝ) / 2) ^ n) ^ ((d : ℝ) - σ) * ‖w‖ ^ (2 - (d : ℝ) - q)) *
            (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b *
            (if d = 2 ∧ q = 0 then 1 + |Real.log (((1 : ℝ) / 2) ^ n)| + |Real.log ‖w‖| else 1)
          = C3 * A * jbracket X ^ (2 * M) * ((((1 : ℝ) / 2) ^ n) ^ ((d : ℝ) - σ) * r ^ (2 - (d : ℝ) - q) *
            (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b *
            (if d = 2 ∧ q = 0 then 1 + |Real.log (((1 : ℝ) / 2) ^ n)| + |Real.log r| else 1)) := by rw [hr]; ring
        _ ≤ (C3 + C5) * A * jbracket X ^ (2 * M) * ((((1 : ℝ) / 2) ^ n) ^ ((d : ℝ) - σ) * r ^ (2 - (d : ℝ) - q) *
            (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b *
            (if d = 2 ∧ q = 0 then 1 + |Real.log (((1 : ℝ) / 2) ^ n)| + |Real.log r| else 1)) := by
            refine mul_le_mul_of_nonneg_right ?_ hpos
            have : 0 ≤ A * jbracket X ^ (2 * M) := mul_nonneg hA hjb
            nlinarith [mul_nonneg hC50 this]
    · have := hC5 A hA F hF (((1 : ℝ) / 2) ^ n) hR hR1 w (by rw [← hr]; linarith [not_le.1 h]) p q hpq X
      simp only [hβ, if_neg h]
      refine this.trans ?_
      have hpos : 0 ≤ (((1 : ℝ) / 2) ^ n) ^ (2 - σ - (q : ℝ)) * (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b *
          (if d = 2 ∧ q = 0 then 1 + |Real.log (((1 : ℝ) / 2) ^ n)| else 1) := by
        split_ifs <;> positivity
      calc C5 * A * jbracket X ^ (2 * M) * (((1 : ℝ) / 2) ^ n) ^ (2 - σ - (q : ℝ)) *
            (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b * (if d = 2 ∧ q = 0 then 1 + |Real.log (((1 : ℝ) / 2) ^ n)| else 1)
          = C5 * A * jbracket X ^ (2 * M) * ((((1 : ℝ) / 2) ^ n) ^ (2 - σ - (q : ℝ)) *
            (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b * (if d = 2 ∧ q = 0 then 1 + |Real.log (((1 : ℝ) / 2) ^ n)| else 1)) := by ring
        _ ≤ (C3 + C5) * A * jbracket X ^ (2 * M) * ((((1 : ℝ) / 2) ^ n) ^ (2 - σ - (q : ℝ)) *
            (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b * (if d = 2 ∧ q = 0 then 1 + |Real.log (((1 : ℝ) / 2) ^ n)| else 1)) := by
            refine mul_le_mul_of_nonneg_right ?_ hpos
            have : 0 ≤ A * jbracket X ^ (2 * M) := mul_nonneg hA hjb
            nlinarith [mul_nonneg hC30 this]
  have hsum : Summable (fun n : ℕ => (C3 + C5) * A * jbracket X ^ (2 * M) * β n) := hβs.mul_left _
  refine ⟨Summable.of_nonneg_of_le (fun n => norm_nonneg _) hpt hsum, ?_⟩
  refine (Summable.of_nonneg_of_le (fun n => norm_nonneg _) hpt hsum).tsum_le_tsum hpt hsum |>.trans ?_
  rw [tsum_mul_left, hβsplit, Summable.tsum_add sI sII]
  have hjb : 0 ≤ jbracket X ^ (2 * M) := Real.rpow_nonneg (by unfold jbracket; positivity : (0:ℝ) < jbracket X).le _
  set E : ℝ := r ^ (2 - σ - (q : ℝ)) * (1 + |Real.log r|) ^ (b + 1) with hEdef
  have hE : 0 ≤ E := mul_nonneg (Real.rpow_nonneg hw.le _) (by positivity)
  have h1 := mul_le_mul_of_nonneg_right hCIq hE
  have h2 := mul_le_mul_of_nonneg_right hCIIq (add_nonneg zero_le_one hE)
  have hS : (∑' n : ℕ, (if ((1 : ℝ) / 2) ^ n ≤ r / 4 then
      ((((1 : ℝ) / 2) ^ n) ^ ((d : ℝ) - σ) * r ^ (2 - (d : ℝ) - q)) * (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b *
        (if d = 2 ∧ q = 0 then 1 + |Real.log (((1 : ℝ) / 2) ^ n)| + |Real.log r| else 1) else 0)) +
      (∑' n : ℕ, (if r / 4 < ((1 : ℝ) / 2) ^ n then
        (((1 : ℝ) / 2) ^ n) ^ (2 - σ - q) * (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b *
          (if d = 2 ∧ q = 0 then 1 + |Real.log (((1 : ℝ) / 2) ^ n)| else 1) else 0)) ≤ 2 * Ce * (1 + E) := by
    nlinarith [hI, hII]
  have hAj : 0 ≤ (C3 + C5) * A * jbracket X ^ (2 * M) := by positivity
  calc (C3 + C5) * A * jbracket X ^ (2 * M) * _ ≤ (C3 + C5) * A * jbracket X ^ (2 * M) * (2 * Ce * (1 + E)) :=
        mul_le_mul_of_nonneg_left hS hAj
    _ = _ := by rw [hEdef]; ring

end HRS.MS.R26T8A
