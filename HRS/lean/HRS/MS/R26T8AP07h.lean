import HRS.MS.R26T8AP11int
import HRS.MS.R26T8AP01
import HRS.MS.R26T8AP05a

/-!
# S8.2 local Newton layer, packet T8A.P07 (part h): pole bound of `midPair F X` at a fixed centre
`r26t8a_p07_midbound`: for `F` conormal of order `sigma < d` there is `s` with `0 < s < d` (depending only on `d, b, sigma`) such that for each centre `X`,
`|midPair F X z| <= c * |z|^(-s)` for `0 < |z| <= 2`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_p07_midbound (hd : 2 ≤ d) (k b : ℕ) (M sigma : ℝ) (hM : 0 ≤ M) (hsd : sigma < d) :
    ∃ s : ℝ, 0 < s ∧ s < d ∧ ∀ A : ℝ, 0 ≤ A → ∀ F : Euc d → Euc d → ℝ, Conormal k b M sigma A F →
      ∀ X : Euc d, ∃ c : ℝ, 0 ≤ c ∧ ∀ z : Euc d, 0 < ‖z‖ → ‖z‖ ≤ 2 → |midPair F X z| ≤ c * ‖z‖ ^ (-s) := by
  set sp : ℝ := max sigma 0 with hsp
  have hsp0 : 0 ≤ sp := le_max_right _ _
  have hspd : sp < d := max_lt hsd (by exact_mod_cast (by omega : 0 < d))
  set s : ℝ := sp + ((d : ℝ) - sp) / 2 with hs
  have hs0 : 0 < s := by rw [hs]; linarith
  have hsd' : s < d := by rw [hs]; linarith
  have hε : 0 < s - sp := by rw [hs]; linarith
  set Mm : ℝ := r26t8a_p06_M (s - sp) b with hMm
  have hMm0 : 0 ≤ Mm := by rw [hMm, r26t8a_p06_M]; have := hε; positivity
  refine ⟨s, hs0, hsd', ?_⟩
  intro A hA F hF X
  have hE : ∀ v : Euc d, 0 < ‖v‖ → ‖v‖ ≤ 2 →
      1 + (min 1 ‖v‖) ^ (-(sigma + ((0 : ℕ) : ℝ))) * (1 + |Real.log (min 1 ‖v‖)|) ^ b ≤
        (1 + Mm + 2 * 2 ^ s) * ‖v‖ ^ (-s) := by
    intro v hv hv2
    have hvs : 0 < ‖v‖ ^ (-s) := Real.rpow_pos_of_pos hv _
    have hL : 1 ≤ (1 + |Real.log (min 1 ‖v‖)|) ^ b :=
      one_le_pow₀ (by linarith [abs_nonneg (Real.log (min 1 ‖v‖))])
    rcases le_total ‖v‖ 1 with h1 | h1
    · rw [min_eq_right h1]
      simp only [Nat.cast_zero, add_zero]
      have hneg : (1 : ℝ) ≤ ‖v‖ ^ (-s) :=
        Real.one_le_rpow_of_pos_of_le_one_of_nonpos hv h1 (by linarith)
      have h2 : ‖v‖ ^ (-sigma) ≤ ‖v‖ ^ (-sp) :=
        Real.rpow_le_rpow_of_exponent_ge hv h1 (by rw [hsp]; linarith [le_max_left sigma 0])
      have h3 : ‖v‖ ^ (-sp) * (1 + |Real.log ‖v‖|) ^ b ≤ Mm * ‖v‖ ^ (-s) := by
        have := r26t8a_p06_slog b hε hv h1
        have e : ‖v‖ ^ (-sp) = ‖v‖ ^ (-s) * ‖v‖ ^ (s - sp) := by
          rw [← Real.rpow_add hv]; congr 1; ring
        calc ‖v‖ ^ (-sp) * (1 + |Real.log ‖v‖|) ^ b
            = ‖v‖ ^ (-s) * (‖v‖ ^ (s - sp) * (1 + |Real.log ‖v‖|) ^ b) := by rw [e]; ring
          _ ≤ ‖v‖ ^ (-s) * Mm := mul_le_mul_of_nonneg_left this hvs.le
          _ = Mm * ‖v‖ ^ (-s) := mul_comm _ _
      have h4 : ‖v‖ ^ (-sigma) * (1 + |Real.log ‖v‖|) ^ b ≤ Mm * ‖v‖ ^ (-s) :=
        (mul_le_mul_of_nonneg_right h2 (by positivity)).trans h3
      nlinarith [hneg, h4, mul_nonneg (by positivity : (0:ℝ) ≤ 2 * 2 ^ s) hvs.le]
    · rw [min_eq_left h1]
      simp only [Nat.cast_zero, add_zero, Real.one_rpow, Real.log_one, abs_zero, add_zero, one_pow, mul_one]
      have h5 : (2 : ℝ) ^ (-s) ≤ ‖v‖ ^ (-s) :=
        Real.rpow_le_rpow_of_nonpos hv hv2 (by linarith)
      have h6 : (2 : ℝ) ^ s * 2 ^ (-s) = 1 := by
        rw [← Real.rpow_add (by norm_num)]; simp
      have h7 : (1 : ℝ) ≤ 2 ^ s * ‖v‖ ^ (-s) := by
        calc (1 : ℝ) = 2 ^ s * 2 ^ (-s) := h6.symm
          _ ≤ 2 ^ s * ‖v‖ ^ (-s) := mul_le_mul_of_nonneg_left h5 (by positivity)
      nlinarith [Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) s]
  have hjX : 0 < jbracket X := s83_jb_pos X
  have hcE : 0 ≤ 1 + Mm + 2 * 2 ^ s := by
    have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) s; linarith
  have hjb : 0 ≤ jbracket X ^ (2 * M) := Real.rpow_nonneg hjX.le _
  refine ⟨A * (3 ^ (2 * M) * jbracket X ^ (2 * M)) * (1 + Mm + 2 * 2 ^ s),
    mul_nonneg (mul_nonneg hA (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hjb)) hcE, ?_⟩
  intro v hv hv2
  have h0 := hF.2 0 0 (by omega) X v (norm_pos_iff.1 hv)
  have hmj : ‖mixedJet 0 0 F X v‖ = |midPair F X v| := by
    simp only [mixedJet, norm_iteratedFDeriv_zero, Real.norm_eq_abs]
  rw [hmj] at h0
  refine h0.trans ?_
  have hpw := r26t8a_p01_weight (d := d) hM (X := X) (z := v) hv2
  have hpw0 : 0 ≤ pairWeight M (X + (1 / 2 : ℝ) • v) (X - (1 / 2 : ℝ) • v) := by
    unfold pairWeight; exact mul_nonneg (Real.rpow_nonneg (s83_jb_pos _).le _) (Real.rpow_nonneg (s83_jb_pos _).le _)
  have hE' := hE v hv hv2
  calc A * pairWeight M (X + (1 / 2 : ℝ) • v) (X - (1 / 2 : ℝ) • v) * (1 + (min 1 ‖v‖) ^ (-(sigma + ((0 : ℕ) : ℝ))) *
        (1 + |Real.log (min 1 ‖v‖)|) ^ b)
      ≤ A * (3 ^ (2 * M) * jbracket X ^ (2 * M)) * ((1 + Mm + 2 * 2 ^ s) * ‖v‖ ^ (-s)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hpw hA) hE'
          (add_nonneg zero_le_one (mul_nonneg (Real.rpow_nonneg (le_min zero_le_one hv.le) _)
            (pow_nonneg (by linarith [abs_nonneg (Real.log (min 1 ‖v‖))]) _)))
          (mul_nonneg hA (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hjb))
    _ = _ := by ring

end HRS.MS.R26T8A
