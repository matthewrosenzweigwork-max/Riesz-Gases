import HRS.Sections.QuenchAux28

/-!
# Packet QUENCH (Q27), part 29: parts (iii), (iv) of Proposition 7.13 from the series identity
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

namespace Qch

open HRS.Sec7

variable {d : ℕ} {m T : ℝ} {s β β₀ : ℝ}

variable (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β)

include hd hs0 hsd hβ in
lemma lamStar_le (k : PosHalf d) : lamStar d s β ≤ lamMode d s β k.1 := by
  obtain ⟨k0, hk0⟩ := exists_min_lam hd hs0 hsd hβ
  rw [lamStar_eq hd hs0 hsd hβ k0 hk0]
  exact hk0 k

/-- the tail weights -/
def gk (d : ℕ) (s β β₀ m T a : ℝ) (k : PosHalf d) : ℝ :=
  if lamMode d s β k.1 = lamStar d s β then 0 else
    Real.exp (-2 * (lamMode d s β k.1 - lamStar d s β) * a) * wk d s β β₀ m T k

variable (Δ : ℝ → (PathSpace d m T [×2]→L[ℝ] ℝ) → ℝ)

lemma ser_ck
    (hser : ∀ a : ℝ, 0 ≤ a → ∀ M : PathSpace d m T [×2]→L[ℝ] ℝ, Δ a M =
      ∑' k : PosHalf d, deltaVar d s β β₀ k.1 * Real.exp (-2 * lamMode d s β k.1 * a) *
          (M ![modePath m T (lamMode d s β k.1) (modeFn k.1 true),
               modePath m T (lamMode d s β k.1) (modeFn k.1 true)] +
            M ![modePath m T (lamMode d s β k.1) (modeFn k.1 false),
               modePath m T (lamMode d s β k.1) (modeFn k.1 false)]))
    {a : ℝ} (ha : 0 ≤ a) (M : PathSpace d m T [×2]→L[ℝ] ℝ) :
    Δ a M = ∑' k : PosHalf d, Real.exp (-2 * lamMode d s β k.1 * a) * ckM d s β β₀ m T M k := by
  rw [hser a ha M]
  refine tsum_congr fun k => ?_
  unfold ckM; ring

include hd hs0 hsd hβ in
lemma gk_nonneg (hβ₀ : 0 < β₀) {a : ℝ} (k : PosHalf d) : 0 ≤ gk d s β β₀ m T a k := by
  unfold gk
  split_ifs
  · exact le_rfl
  · unfold wk; positivity

include hd hs0 hsd hβ in
lemma gk_le (hβ₀ : 0 < β₀) {a : ℝ} (ha : 0 ≤ a) (k : PosHalf d) :
    gk d s β β₀ m T a k ≤ wk d s β β₀ m T k := by
  unfold gk
  have hw : 0 ≤ wk d s β β₀ m T k := by unfold wk; positivity
  split_ifs
  · exact hw
  · have := lamStar_le hd hs0 hsd hβ k
    have h : Real.exp (-2 * (lamMode d s β k.1 - lamStar d s β) * a) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith)
    calc _ ≤ 1 * wk d s β β₀ m T k := by gcongr
      _ = _ := one_mul _

include hd hs0 hsd hβ in
theorem tail_bound (hβ₀ : 0 < β₀) (hm : (d : ℝ) / 2 + 1 < m) (hT : 0 < T)
    (hser : ∀ a : ℝ, 0 ≤ a → ∀ M : PathSpace d m T [×2]→L[ℝ] ℝ, Δ a M =
      ∑' k : PosHalf d, deltaVar d s β β₀ k.1 * Real.exp (-2 * lamMode d s β k.1 * a) *
          (M ![modePath m T (lamMode d s β k.1) (modeFn k.1 true),
               modePath m T (lamMode d s β k.1) (modeFn k.1 true)] +
            M ![modePath m T (lamMode d s β k.1) (modeFn k.1 false),
               modePath m T (lamMode d s β k.1) (modeFn k.1 false)]))
    {a : ℝ} (ha : 0 ≤ a) (M : PathSpace d m T [×2]→L[ℝ] ℝ) :
    |Real.exp (2 * lamStar d s β * a) * Δ a M - slowTensor d s β β₀ m T M| ≤
      ‖M‖ * ∑' k, gk d s β β₀ m T a k := by
  have hl : ∀ k : PosHalf d, 0 ≤ lamMode d s β k.1 := fun k => (lamMode_pos' hd hs0 hsd hβ k).le
  have hwsum := summable_wk (β₀ := β₀) (m := m) (T := T) hd hs0 hsd hβ hβ₀ hm hT
  set S : Set (PosHalf d) := {k | lamMode d s β k.1 = lamStar d s β} with hS
  set c := ckM d s β β₀ m T M with hc
  have hcb : ∀ k, ‖c k‖ ≤ ‖M‖ * wk d s β β₀ m T k := fun k => by
    rw [Real.norm_eq_abs]; exact abs_ckM_le M hl k
  have hcsum : Summable c := Summable.of_norm_bounded (hwsum.mul_left ‖M‖) hcb
  have hslow : slowTensor d s β β₀ m T M = ∑' k, S.indicator c k := by
    have := tsum_subtype S c
    rw [← this]
    rfl
  set F : PosHalf d → ℝ := fun k => Real.exp (-2 * (lamMode d s β k.1 - lamStar d s β) * a) * c k with hF
  have hFeq : ∀ k, Real.exp (2 * lamStar d s β * a) * (Real.exp (-2 * lamMode d s β k.1 * a) * c k) = F k := by
    intro k
    simp only [hF]
    rw [← mul_assoc, ← Real.exp_add]
    congr 2; ring
  have hFb : ∀ k, ‖F k‖ ≤ ‖M‖ * wk d s β β₀ m T k := fun k => by
    have := lamStar_le hd hs0 hsd hβ k
    have h : Real.exp (-2 * (lamMode d s β k.1 - lamStar d s β) * a) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith)
    simp only [hF, norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
    calc _ ≤ 1 * ‖c k‖ := by gcongr
      _ = ‖c k‖ := one_mul _
      _ ≤ _ := hcb k
  have hFsum : Summable F := Summable.of_norm_bounded (hwsum.mul_left ‖M‖) hFb
  have hmain : Real.exp (2 * lamStar d s β * a) * Δ a M = ∑' k, F k := by
    rw [ser_ck Δ hser ha M, ← tsum_mul_left]
    exact tsum_congr hFeq
  have hgsum : Summable (gk d s β β₀ m T a) :=
    Summable.of_nonneg_of_le (fun k => gk_nonneg hd hs0 hsd hβ hβ₀ k) (gk_le hd hs0 hsd hβ hβ₀ ha) hwsum
  rw [hmain, hslow, ← Summable.tsum_sub hFsum (hcsum.indicator S)]
  have hbd : ∀ k, ‖F k - S.indicator c k‖ ≤ ‖M‖ * gk d s β β₀ m T a k := by
    intro k
    by_cases hk : k ∈ S
    · have hk' : lamMode d s β k.1 = lamStar d s β := hk
      rw [Set.indicator_of_mem hk]
      simp only [hF, hk', sub_self, mul_zero, Real.exp_zero, zero_mul, one_mul, sub_self, norm_zero]
      unfold gk
      simp [hk']
    · have hk' : ¬ lamMode d s β k.1 = lamStar d s β := hk
      rw [Set.indicator_of_notMem hk, sub_zero]
      unfold gk
      rw [if_neg hk']
      simp only [hF, norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
      calc Real.exp (-2 * (lamMode d s β k.1 - lamStar d s β) * a) * ‖c k‖
          ≤ Real.exp (-2 * (lamMode d s β k.1 - lamStar d s β) * a) * (‖M‖ * wk d s β β₀ m T k) := by
            gcongr; exact hcb k
        _ = _ := by ring
  have := tsum_of_norm_bounded (hgsum.hasSum.mul_left ‖M‖) hbd
  rwa [Real.norm_eq_abs] at this

include hd hs0 hsd hβ in
theorem tendsto_tail (hβ₀ : 0 < β₀) (hm : (d : ℝ) / 2 + 1 < m) (hT : 0 < T) :
    Tendsto (fun a : ℝ => ∑' k, gk d s β β₀ m T a k) atTop (𝓝 0) := by
  have hwsum := summable_wk (β₀ := β₀) (m := m) (T := T) hd hs0 hsd hβ hβ₀ hm hT
  have := tendsto_tsum_of_dominated_convergence (f := fun (a : ℝ) k => gk d s β β₀ m T a k)
    (g := fun _ => (0 : ℝ)) (bound := wk d s β β₀ m T) (𝓕 := atTop) hwsum ?_ ?_
  · simpa using this
  · intro k
    by_cases hk : lamMode d s β k.1 = lamStar d s β
    · simp only [gk, hk, if_true]; exact tendsto_const_nhds
    · have hlt : lamStar d s β < lamMode d s β k.1 := lt_of_le_of_ne (lamStar_le hd hs0 hsd hβ k) (Ne.symm hk)
      simp only [gk, hk, if_false]
      have h1 : Tendsto (fun a : ℝ => (-2 * (lamMode d s β k.1 - lamStar d s β)) * a) atTop atBot :=
        tendsto_id.const_mul_atTop_of_neg (by linarith)
      have h2 := (Real.tendsto_exp_atBot.comp h1).mul_const (wk d s β β₀ m T k)
      simpa using h2
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with a ha k
    rw [Real.norm_of_nonneg (gk_nonneg hd hs0 hsd hβ hβ₀ k)]
    exact gk_le hd hs0 hsd hβ hβ₀ ha k

end Qch

end HRS
