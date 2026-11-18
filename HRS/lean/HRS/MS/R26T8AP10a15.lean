import HRS.MS.R26T8AP10a14
import HRS.MS.R26T8AP06a4
import HRS.MS.WadAux1

/-!
# S8.2 T8A P10a (part 15): from the conormal envelope to a pole bound
`r26t8a_p10a_env`: `1 + s^(-e0) (1+|log s|)^b ≤ C (1 + r^(-e))` for `s = min 1 r`, `e0 < e`, `0 < e`.
`r26t8a_p10a_Tj_bound`: slice jets of `Q(·,y)` of order `j` are `≤ K A jb(y)^M (1+|u|)^M (1 + |u-y|^(-e))` for `σ + j < e`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_p10a_env (b : ℕ) {e0 e : ℝ} (he0 : e0 < e) (he : 0 < e) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r →
      1 + (min 1 r) ^ (-e0) * (1 + |Real.log (min 1 r)|) ^ b ≤ C * (1 + r ^ (-e)) := by
  refine ⟨1 + r26t8a_p06_M (e - e0) b, by unfold r26t8a_p06_M; positivity, fun r hr => ?_⟩
  have hs : 0 < min 1 r := lt_min one_pos hr
  have hs1 : min 1 r ≤ 1 := min_le_left _ _
  have hM := r26t8a_p06_slog b (sub_pos.2 he0) hs hs1
  have hM0 : 0 ≤ r26t8a_p06_M (e - e0) b := by unfold r26t8a_p06_M; positivity
  have h1 : (min 1 r) ^ (-e0) * (1 + |Real.log (min 1 r)|) ^ b ≤
      r26t8a_p06_M (e - e0) b * (min 1 r) ^ (-e) := by
    have : (min 1 r) ^ (-e0) = (min 1 r) ^ (e - e0) * (min 1 r) ^ (-e) := by
      rw [← Real.rpow_add hs]; congr 1; ring
    rw [this]
    calc (min 1 r) ^ (e - e0) * (min 1 r) ^ (-e) * (1 + |Real.log (min 1 r)|) ^ b
        = ((min 1 r) ^ (e - e0) * (1 + |Real.log (min 1 r)|) ^ b) * (min 1 r) ^ (-e) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hM (Real.rpow_nonneg hs.le _)
  have h2 : (min 1 r) ^ (-e) ≤ 1 + r ^ (-e) := by
    by_cases hr1 : r ≤ 1
    · rw [min_eq_right hr1]; linarith [Real.rpow_nonneg hr.le (-e)]
    · rw [min_eq_left (not_le.1 hr1).le, Real.one_rpow]; linarith [Real.rpow_nonneg hr.le (-e)]
  have h3 : 1 ≤ 1 + r ^ (-e) := by linarith [Real.rpow_nonneg hr.le (-e)]
  nlinarith [mul_le_mul_of_nonneg_left h2 hM0]

theorem r26t8a_p10a_Tj_bound {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {k b : ℕ} {M σ : ℝ} (hM : 0 ≤ M)
    {j : ℕ} (hj : j ≤ k + 2) {e : ℝ} (he : σ + j < e) (he0 : 0 < e) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (A : ℝ), 0 ≤ A → ∀ {Q : Euc d → Euc d → ℝ}, Conormal (k + 2) b M σ A Q →
      ∀ (y u : Euc d), u ≠ y →
        ‖iteratedFDeriv ℝ j (fun v => Q v y) u‖ ≤
          K * A * jbracket y ^ M * (1 + ‖u‖) ^ M * (1 + ‖u - y‖ ^ (-e)) := by
  -- constants for each `q ≤ j`
  have hq : ∀ q ∈ Finset.range (j + 1), ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r →
      1 + (min 1 r) ^ (-(σ + q)) * (1 + |Real.log (min 1 r)|) ^ b ≤ C * (1 + r ^ (-e)) := by
    intro q hq
    have hq' : (q : ℝ) ≤ j := by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hq)
    exact r26t8a_p10a_env b (by linarith) he0
  choose! C hC0 hC using hq
  refine ⟨(∑ q ∈ Finset.range (j + 1), (j.choose q : ℝ) * C q), ?_, ?_⟩
  · exact Finset.sum_nonneg fun q hq => mul_nonneg (Nat.cast_nonneg _) (hC0 q hq)
  intro A hA Q hQ y u hu
  have hs := r26t8a_p10a_slice_jet hchi hA hQ hj hu
  have hpw : pairWeight M u y ≤ jbracket y ^ M * (1 + ‖u‖) ^ M := by
    unfold pairWeight
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (s83_jb_pos u).le (s83_jb_le_one_add u) hM)
      (Real.rpow_nonneg (s83_jb_pos y).le _)
  have hn : 0 < ‖u - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hu)
  refine hs.trans ?_
  have : ∀ q ∈ Finset.range (j + 1), (j.choose q : ℝ) * (A * pairWeight M u y *
      (1 + (min 1 ‖u - y‖) ^ (-(σ + q)) * (1 + |Real.log (min 1 ‖u - y‖)|) ^ b)) ≤
      (j.choose q : ℝ) * C q * A * jbracket y ^ M * (1 + ‖u‖) ^ M * (1 + ‖u - y‖ ^ (-e)) := by
    intro q hq
    have h1 := hC q hq ‖u - y‖ hn
    have hpw0 : 0 ≤ pairWeight M u y := by
      unfold pairWeight
      exact mul_nonneg (Real.rpow_nonneg (s83_jb_pos _).le _) (Real.rpow_nonneg (s83_jb_pos _).le _)
    have hch : (0 : ℝ) ≤ j.choose q := Nat.cast_nonneg _
    have hjy : 0 ≤ jbracket y ^ M := Real.rpow_nonneg (s83_jb_pos y).le _
    have h2 : A * pairWeight M u y ≤ A * (jbracket y ^ M * (1 + ‖u‖) ^ M) :=
      mul_le_mul_of_nonneg_left hpw hA
    have h4 : 0 ≤ 1 + (min 1 ‖u - y‖) ^ (-(σ + q)) * (1 + |Real.log (min 1 ‖u - y‖)|) ^ b := by
      positivity
    have h3 := mul_le_mul h2 h1 h4 (mul_nonneg hA (mul_nonneg hjy (by positivity)))
    calc (j.choose q : ℝ) * (A * pairWeight M u y *
          (1 + (min 1 ‖u - y‖) ^ (-(σ + q)) * (1 + |Real.log (min 1 ‖u - y‖)|) ^ b))
        ≤ (j.choose q : ℝ) * (A * (jbracket y ^ M * (1 + ‖u‖) ^ M) * (C q * (1 + ‖u - y‖ ^ (-e)))) :=
          mul_le_mul_of_nonneg_left h3 hch
      _ = _ := by ring
  refine (Finset.sum_le_sum this).trans (le_of_eq ?_)
  simp only [Finset.sum_mul]

end HRS.MS.R26T8A
