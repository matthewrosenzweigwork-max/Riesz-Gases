import HRS.MD.EQLZSgSmooth

/-!
# EQ-LZ packet SG-2: the semigroup law `P_{s+t} = P_s P_t` on smooth data (`eqlz_sg_semigroup`), proof

Route: a classical backward solution `f` on `[0, s+t]` with terminal datum `φ`; `f s = P_t φ` (`d1_P_eq`), and the
restriction of `f` to `[0, s]` is a backward solution with terminal datum `P_t φ` (smooth by `eqlz_sg_smooth`), so
`P_s (P_t φ) = f 0 = P_{s+t} φ` by `d1_P_eq`.
-/

noncomputable section

open MeasureTheory Filter Topology
open HRS

namespace HRS.MD.EQLZSgSemigroup

variable {n : ℕ}

/-- The restriction of a backward solution on `[0, T]` to `[0, s]`, `s ≤ T`, is a backward solution with terminal
datum `f s`. -/
theorem eqlzsg_restrict {κ : ℝ} {b : Torus n → Euc n} {T s : ℝ} (hsT : s ≤ T) {φ : Torus n → ℝ}
    {f : ℝ → Torus n → ℝ} (h : D1BackwardSolution κ b T φ f) :
    D1BackwardSolution κ b s (f s) f where
  c2 r hr := h.c2 r ⟨hr.1, hr.2.trans hsT⟩
  cont_c2 j hj := by
    have h1 := (h.cont_c2 j hj).comp
      ((continuous_inclusion (Set.Icc_subset_Icc_right hsT)).prodMap continuous_id)
    exact h1
  terminal := rfl
  time_deriv x r hr := h.time_deriv x r ⟨hr.1, hr.2.trans_le hsT⟩
  cont_time_deriv := by
    have h1 := h.cont_time_deriv.comp
      ((continuous_inclusion (Set.Icc_subset_Icc_right hsT)).prodMap continuous_id)
    exact h1

/-- `d1_P` at time `0` is the identity. -/
theorem eqlzsg_P_zero (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ} (hU : Torus.IsSmooth U)
    (ψ : Torus n → ℝ) : d1_P hn hκ hU 0 ψ = ψ := by
  funext x
  unfold d1_P
  simp

/-- (SG-2, `eqlz_sg_semigroup`.)  Statement copied verbatim from `HRS.MD.EQLZ.eqlz_sg_semigroup`. -/
theorem eqlz_sg_semigroup_proof (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ} (hU : Torus.IsSmooth U)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) {φ : Torus n → ℝ} (hφ : Torus.IsSmooth φ) :
    d1_P hn hκ hU (s + t) φ = d1_P hn hκ hU s (d1_P hn hκ hU t φ) := by
  rcases hs.eq_or_lt with h0 | hpos
  · subst h0
    rw [eqlzsg_P_zero hn hκ hU, zero_add]
  · have hT : 0 < s + t := by linarith
    obtain ⟨f, hf⟩ := d1_backward_classical hn hκ hU hT hφ
    have hPt : ∀ x, d1_P hn hκ hU t φ x = f s x := by
      intro x
      rw [d1_P_eq hn hκ hU hT hφ hf ⟨ht, by linarith⟩ x]
      congr 1; ring
    have hfs : f s = d1_P hn hκ hU t φ := funext fun x => (hPt x).symm
    have hsm : Torus.IsSmooth (d1_P hn hκ hU t φ) :=
      HRS.MD.EQLZSgSmooth.eqlz_sg_smooth_proof hn hκ hU ht hφ
    have hres : D1BackwardSolution κ (d1_gradDrift U) s (d1_P hn hκ hU t φ) f := by
      rw [← hfs]
      exact eqlzsg_restrict (by linarith) hf
    funext x
    rw [d1_P_eq hn hκ hU hpos hsm hres ⟨hs, le_rfl⟩ x,
      d1_P_eq hn hκ hU hT hφ hf ⟨by linarith, le_rfl⟩ x]
    simp

end HRS.MD.EQLZSgSemigroup

end
