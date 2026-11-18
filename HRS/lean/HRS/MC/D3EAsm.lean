import HRS.MC.FDLE
import HRS.MC.D3EW
import HRS.MC.D3EG

/-!
# Packet D3EAsm: Lemma D.3 on `ℝ^d`, assembled from `FDLE`, `D3EW` and `D3EG`.

The statement is `HRS.fdl_kernel_euclid` with ONE repair, recorded in `docs/ISSUES.md` as
`MC: request FDL-E1`: the third bullet of (i), `w_λ ≤ g + C·1_{s=0}`, carries the extra premise
`s = 0 → ‖z‖ ≤ 1` (for `s = 0` and `‖z‖` large `g(z) = -log‖z‖ → -∞` while `w_λ = 0`).  Once Session A
applies the repair to `HRS/Appendix/FDL.lean`, the tie `example := (@fdl_kernel_euclid_proof : type_of% @HRS.fdl_kernel_euclid)`
below becomes valid.
-/

noncomputable section

open MeasureTheory Filter Topology

namespace HRS.MC.D3EAsm

open HRS

variable {d : ℕ}

theorem fdl_kernel_euclid_proof (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {b : ℝ} (hb : IsFDLConst ψ s b) :
    -- (i)
    (∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam → lam < 1 →
      (∀ z : Euc d, z ≠ 0 → 0 ≤ fdlWE ψ s b lam z) ∧
      (∀ z : Euc d, lam ≤ ‖z‖ →
        fdlWE ψ s b lam z = 0 ∧ fdlTruncE ψ s b lam z = Whole.rieszKernel d s z) ∧
      (∀ z : Euc d, z ≠ 0 → (s = 0 → ‖z‖ ≤ 1) →
        fdlWE ψ s b lam z ≤ Whole.rieszKernel d s z + C * (if s = 0 then 1 else 0)) ∧
      ∫⁻ z : Euc d, ENNReal.ofReal (fdlWE ψ s b lam z) ≤
        ENNReal.ofReal (C * lam ^ ((d : ℝ) - s))) ∧
    -- (ii), `j + s > 0`
    (∀ j : ℕ, 0 < (j : ℝ) + s → ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam → lam < 1 →
      ∀ z : Euc d, z ≠ 0 →
        ‖iteratedFDeriv ℝ j (fdlWE ψ s b lam) z‖ ≤
          (if ‖z‖ ≤ lam then C * ‖z‖ ^ (-s - (j : ℝ)) else 0) ∧
        ‖iteratedFDeriv ℝ j (fdlTruncE ψ s b lam) z‖ ≤ C * (max lam ‖z‖) ^ (-s - (j : ℝ))) ∧
    -- (ii), `s = j = 0`
    (s = 0 → ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam → lam < 1 → ∀ z : Euc d, z ≠ 0 →
      |fdlWE ψ s b lam z| ≤ (if ‖z‖ ≤ lam then C * Real.log (lam / ‖z‖) else 0) ∧
      |fdlTruncE ψ s b lam z| ≤ C * (1 + |Real.log (max lam ‖z‖)|)) ∧
    -- (ii), smoothness and sup bounds ("in particular")
    (∀ lam : ℝ, 0 < lam → lam < 1 →
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fdlTruncE ψ s b lam)) ∧
    (∀ j : ℕ, 0 < (j : ℝ) + s → ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam → lam < 1 → ∀ z : Euc d,
      ‖iteratedFDeriv ℝ j (fdlTruncE ψ s b lam) z‖ ≤ C * lam ^ (-s - (j : ℝ))) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam → lam < 1 →
      |fdlTruncE ψ s b lam 0| ≤
        C * (lam ^ (-s) + (if s = 0 then |Real.log lam| else 0))) ∧
    -- (iv)
    (0 < s → ∃ c : ℝ, 0 < c ∧ ∀ lam : ℝ, 0 < lam → lam < 1 → ∀ z : Euc d, lam ≤ ‖z‖ →
      c * ‖z‖ ^ (-s) ≤ fdlTruncE ψ s b lam z) ∧
    (s = 0 → ∃ c C : ℝ, 0 < c ∧ ∀ lam : ℝ, 0 < lam → lam < 1 → ∀ z : Euc d, lam ≤ ‖z‖ →
      ‖z‖ ≤ 1 / 2 → c * Real.log (1 / ‖z‖) - C ≤ fdlTruncE ψ s b lam z) ∧
    (∀ K : ℝ, fdlK ≤ K → ∃ c : ℝ, 0 < c ∧ ∀ lam : ℝ, 0 < lam → lam < 1 → ∀ z : Euc d, z ≠ 0 →
      ‖z‖ ≤ 2 * lam → c * (if s = 0 then 1 else lam ^ (-s)) ≤ fdlWE ψ s b (K * lam) z) := by
  obtain ⟨hiv1, hiv2, hiv3⟩ := FDLE.fdle_part_iv hd hs0 hsd hψ hb
  refine ⟨FDLE.fdle_part_i hd hs0 hsd hψ hb, ?_, ?_, D3EG.d3eg_smooth hd hs0 hsd hψ hb,
    D3EG.d3eg_sup hd hs0 hsd hψ hb, D3EG.d3eg_zero hd hs0 hsd hψ hb, hiv1, hiv2, hiv3⟩
  · intro j hj
    obtain ⟨C1, hC1, h1⟩ := D3EW.d3ew_deriv hd hs0 hsd hψ hb j hj
    obtain ⟨C2, hC2, h2⟩ := D3EG.d3eg_deriv hd hs0 hsd hψ hb j hj
    refine ⟨max C1 C2, le_max_of_le_left hC1, fun lam hl hl1 z hz => ⟨?_, ?_⟩⟩
    · have := h1 lam hl hl1 z hz
      split_ifs at this ⊢
      · exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
          (Real.rpow_nonneg (norm_nonneg _) _))
      · exact this
    · exact (h2 lam hl hl1 z hz).trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
        (Real.rpow_nonneg (le_trans hl.le (le_max_left _ _)) _))
  · intro hs
    obtain ⟨C1, hC1, h1⟩ := D3EW.d3ew_log hd hs0 hsd hψ hb hs
    obtain ⟨C2, hC2, h2⟩ := D3EG.d3eg_log hd hs0 hsd hψ hb hs
    refine ⟨max C1 C2, le_max_of_le_left hC1, fun lam hl hl1 z hz => ⟨?_, ?_⟩⟩
    · have := h1 lam hl hl1 z hz
      split_ifs at this ⊢ with h
      · refine this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_)
        exact Real.log_nonneg (by rw [le_div_iff₀ (norm_pos_iff.2 hz)]; linarith)
      · exact this
    · exact (h2 lam hl hl1 z hz).trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
        (by positivity))

end HRS.MC.D3EAsm
