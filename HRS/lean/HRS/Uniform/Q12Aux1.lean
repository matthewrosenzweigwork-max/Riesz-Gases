import Mathlib

/-!
# Q12, part 1: iterated forward differences of a function with bounded derivatives
-/

noncomputable section

open Set Function fwdDiff

namespace HRS.Uniform.Q12

lemma q12_mvt {u u' : ℝ → ℝ} {a b B : ℝ} (hab : a ≤ b) (hc : ContinuousOn u (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt u (u' t) t) (hB : ∀ t ∈ Ioo a b, |u' t| ≤ B) :
    |u b - u a| ≤ B * (b - a) := by
  rcases hab.eq_or_lt with h | h
  · subst h; simp
  · obtain ⟨c, hc1, hc2⟩ := exists_hasDerivAt_eq_slope u u' h hc hd
    have h1 : u b - u a = u' c * (b - a) := by
      rw [hc2]; field_simp [(sub_pos.2 h).ne']
    rw [h1, abs_mul, abs_of_pos (sub_pos.2 h)]
    exact mul_le_mul_of_nonneg_right (hB c hc1) (sub_pos.2 h).le

/-- If `u 0, …, u n` are continuous on `[0, ∞)` with `u m' = u (m+1)` on `(0, ∞)` and
`|u n| ≤ B` on `(0, ∞)`, then the `n`-th forward difference of `u 0` at `0` is at most
`ε ^ n * B` (`n ≥ 1`). -/
lemma q12_fd_bound {ε : ℝ} (hε : 0 < ε) :
    ∀ (L : ℕ) (B : ℝ) (u : ℕ → ℝ → ℝ),
      (∀ m, m < L + 1 → ContinuousOn (u m) (Ici 0)) →
      (∀ m, m < L + 1 → ∀ t, 0 < t → HasDerivAt (u m) (u (m + 1) t) t) →
      (∀ t, 0 < t → |u (L + 1) t| ≤ B) →
      |((fwdDiff ε)^[L + 1] (u 0)) 0| ≤ ε ^ (L + 1) * B := by
  intro L
  induction L with
  | zero =>
    intro B u hc hd hB
    simp only [zero_add, Function.iterate_one, fwdDiff, pow_one]
    have := q12_mvt (u := u 0) (u' := u 1) (a := 0) (b := 0 + ε) (B := B) (by linarith)
      ((hc 0 (by omega)).mono (fun t ht => ht.1))
      (fun t ht => hd 0 (by omega) t ht.1)
      (fun t ht => hB t ht.1)
    simpa [mul_comm] using this
  | succ L ih =>
    intro B u hc hd hB
    set v : ℕ → ℝ → ℝ := fun m t => u m (t + ε) - u m t with hv
    have hshift : ∀ m, m < L + 2 → ∀ t, 0 < t → HasDerivAt (u m) (u (m + 1) t) t := hd
    have h1 : ∀ m, m < L + 1 → ContinuousOn (v m) (Ici 0) := by
      intro m hm
      have hcm := hc m (by omega)
      refine ContinuousOn.sub ?_ hcm
      have : ContinuousOn (fun t => u m (t + ε)) (Ici 0) := by
        refine hcm.comp (continuousOn_id.add continuousOn_const) (fun t ht => ?_)
        have : (0:ℝ) ≤ t := ht
        show (0:ℝ) ≤ t + ε
        linarith
      exact this
    have h2 : ∀ m, m < L + 1 → ∀ t, 0 < t → HasDerivAt (v m) (v (m + 1) t) t := by
      intro m hm t ht
      have a1 := (hd m (by omega) (t + ε) (by linarith)).comp_add_const t ε
      have a2 := hd m (by omega) t ht
      exact a1.sub a2
    have h3 : ∀ t, 0 < t → |v (L + 1) t| ≤ ε * B := by
      intro t ht
      have := q12_mvt (u := u (L + 1)) (u' := u (L + 2)) (a := t) (b := t + ε) (B := B)
        (by linarith)
        (fun s hs => (hd (L + 1) (by omega) s (lt_of_lt_of_le ht hs.1)).continuousAt.continuousWithinAt)
        (fun s hs => hd (L + 1) (by omega) s (lt_trans ht hs.1))
        (fun s hs => hB s (lt_trans ht hs.1))
      simp only [hv]
      calc |u (L + 1) (t + ε) - u (L + 1) t| ≤ B * (t + ε - t) := this
        _ = ε * B := by ring
    have := ih (ε * B) v h1 h2 h3
    rw [Function.iterate_succ_apply]
    have e : fwdDiff ε (u 0) = v 0 := rfl
    rw [e]
    calc _ ≤ ε ^ (L + 1) * (ε * B) := this
      _ = ε ^ (L + 1 + 1) * B := by ring

end HRS.Uniform.Q12
