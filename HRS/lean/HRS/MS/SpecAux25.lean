import Mathlib

/-!
# S8P: a symmetric strongly continuous semigroup is injective (generic, for S8.7)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  `s8p_semigroup_ker_trivial`: if `T(t)` are symmetric, `T(0) = 1`,
`T(s+t) = T(s)T(t)` for `s,t ≥ 0` and `t ↦ T(t)x` is continuous on `[0,∞)`, then `T(1)x = 0 ⇒ x = 0`
(`T(1)x = 0 ⇒ ‖T(1/2)x‖² = ⟨T(1)x,x⟩ = 0 ⇒ … ⇒ T(2^{-n})x = 0 → x`).
`s8p_semigroup_nonneg`: `⟨T(2t)x,x⟩ = ‖T(t)x‖² ≥ 0`.
-/

noncomputable section

open Filter Topology Set
open scoped RealInnerProductSpace

namespace HRS.MS.Spec

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem s8p_semigroup_sq (T : ℝ → H →L[ℝ] H)
    (hsymm : ∀ t, 0 ≤ t → ∀ x y, ⟪T t x, y⟫ = ⟪x, T t y⟫)
    (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → T (s + t) = T s * T t) {t : ℝ} (ht : 0 ≤ t) (x : H) :
    ⟪T (2 * t) x, x⟫ = ‖T t x‖ ^ 2 := by
  rw [two_mul, hadd t t ht ht, ContinuousLinearMap.mul_apply, hsymm t ht, ← real_inner_self_eq_norm_sq]

theorem s8p_semigroup_nonneg (T : ℝ → H →L[ℝ] H)
    (hsymm : ∀ t, 0 ≤ t → ∀ x y, ⟪T t x, y⟫ = ⟪x, T t y⟫)
    (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → T (s + t) = T s * T t) {t : ℝ} (ht : 0 ≤ t) (x : H) :
    0 ≤ ⟪T (2 * t) x, x⟫ := by
  rw [s8p_semigroup_sq T hsymm hadd ht]; positivity

theorem s8p_semigroup_ker_trivial (T : ℝ → H →L[ℝ] H)
    (hsymm : ∀ t, 0 ≤ t → ∀ x y, ⟪T t x, y⟫ = ⟪x, T t y⟫)
    (hzero : T 0 = 1) (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → T (s + t) = T s * T t)
    (hcont : ∀ x, ContinuousOn (fun t => T t x) (Ici 0)) {x : H} (hx : T 1 x = 0) : x = 0 := by
  have hn : ∀ n : ℕ, T ((1 / 2) ^ n) x = 0 := by
    intro n
    induction n with
    | zero => simpa using hx
    | succ n ih =>
      have ht : (0 : ℝ) ≤ (1 / 2) ^ (n + 1) := by positivity
      have h2 := s8p_semigroup_sq T hsymm hadd ht x
      have : 2 * ((1 / 2 : ℝ) ^ (n + 1)) = (1 / 2) ^ n := by rw [pow_succ]; ring
      rw [this, ih, inner_zero_left] at h2
      have : ‖T ((1 / 2) ^ (n + 1)) x‖ ^ 2 = 0 := h2.symm
      exact norm_eq_zero.1 (by simpa using this)
  have hlim : Tendsto (fun n : ℕ => T ((1 / 2 : ℝ) ^ n) x) atTop (𝓝 (T 0 x)) := by
    have hc : ContinuousWithinAt (fun t => T t x) (Ici 0) 0 := (hcont x) 0 (mem_Ici.2 le_rfl)
    have hs : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝[Ici 0] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num),
        Eventually.of_forall fun n => mem_Ici.2 (by positivity)⟩
    exact hc.tendsto.comp hs
  have h0 : (fun n : ℕ => T ((1 / 2 : ℝ) ^ n) x) = fun _ => 0 := funext hn
  rw [h0] at hlim
  have := tendsto_nhds_unique hlim tendsto_const_nhds
  rw [hzero] at this
  simpa using this

end HRS.MS.Spec
