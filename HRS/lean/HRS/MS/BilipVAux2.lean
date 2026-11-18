import HRS.MS.BilipVAux1
import HRS.Whole.Adjoint

/-!
# MS-BILIP-V, part 2: a translation-invariant smooth partition of unity on the lattice `s ℤ^d`

`bv_pou`: for `d s ≤ r` there is one `ρ ∈ C_c^∞` supported in `B(0,r)` with `∑_k ρ(y - s k) = 1` for all `y`
(in the finite form: for every finite set `K` containing the indices `k` with `‖y - s k‖ < r`).
Route: `BilipVPlan.md`.
-/

noncomputable section

open Set
open scoped ContDiff

namespace HRS.MS.BilipV

variable {d : ℕ}

theorem bv_pt_add (s : ℝ) (a b : Fin d → ℤ) : bv_pt s (a + b) = bv_pt s a + bv_pt s b := by
  ext i
  simp [bv_pt_apply, mul_add]

theorem bv_pou {s r : ℝ} (hs : 0 < s) (hr : 0 < r) (hsr : d * s ≤ r) :
    ∃ ρ : HRS.Euc d → ℝ, ContDiff ℝ ∞ ρ ∧ HasCompactSupport ρ ∧ (∀ y, r ≤ ‖y‖ → ρ y = 0) ∧
      (∀ y, 0 ≤ ρ y) ∧
      ∀ (y : HRS.Euc d) (K : Finset (Fin d → ℤ)), (∀ k, ‖y - bv_pt s k‖ < r → k ∈ K) →
        ∑ k ∈ K, ρ (y - bv_pt s k) = 1 := by
  classical
  let f : ContDiffBump (0 : HRS.Euc d) := ⟨r / 2, r, by positivity, by linarith⟩
  have hf0 : ∀ y : HRS.Euc d, r ≤ ‖y‖ → f y = 0 := fun y hy =>
    f.zero_of_le_dist (by show r ≤ dist y 0; rw [dist_zero_right]; exact hy)
  have hfnn : ∀ y, 0 ≤ f y := fun y => f.nonneg
  -- local finiteness
  obtain ⟨N, hN⟩ := bv_net (d := d) hs (r + 1)
  have hloc : ∀ y0 : HRS.Euc d, ∃ K0 : Finset (Fin d → ℤ), ∀ y : HRS.Euc d, ‖y - y0‖ < 1 →
      ∀ k, k ∉ K0 → f (y - bv_pt s k) = 0 := by
    intro y0
    obtain ⟨K0, -, hK0⟩ := hN y0
    refine ⟨K0, fun y hy k hk => ?_⟩
    by_contra h
    have h1 : ‖y - bv_pt s k‖ < r := by
      by_contra h2
      exact h (hf0 _ (not_lt.1 h2))
    apply hk
    refine hK0 k ?_
    calc ‖y0 - bv_pt s k‖ = ‖(y0 - y) + (y - bv_pt s k)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖y0 - y‖ + ‖y - bv_pt s k‖ := norm_add_le _ _
      _ ≤ r + 1 := by rw [norm_sub_rev]; linarith
  choose K0 hK0 using hloc
  set D : HRS.Euc d → ℝ := fun y => ∑' k : Fin d → ℤ, f (y - bv_pt s k) with hD
  have hDeq : ∀ y0 y : HRS.Euc d, ‖y - y0‖ < 1 → D y = ∑ k ∈ K0 y0, f (y - bv_pt s k) :=
    fun y0 y hy => tsum_eq_sum (fun k hk => hK0 y0 y hy k hk)
  have hDsm : ContDiff ℝ ∞ D := by
    refine contDiff_iff_contDiffAt.2 fun y0 => ?_
    have hev : D =ᶠ[nhds y0] fun y => ∑ k ∈ K0 y0, f (y - bv_pt s k) := by
      filter_upwards [Metric.ball_mem_nhds y0 one_pos] with y hy
      exact hDeq y0 y (by simpa [dist_eq_norm] using hy)
    refine ContDiffAt.congr_of_eventuallyEq ?_ hev
    exact (ContDiff.sum fun k _ => f.contDiff.comp (contDiff_id.sub contDiff_const)).contDiffAt
  have hDge : ∀ y, 1 ≤ D y := by
    intro y
    obtain ⟨k1, hk1⟩ := bv_approx hs y
    have h1 : f (y - bv_pt s k1) = 1 := by
      refine f.one_of_mem_closedBall ?_
      rw [mem_closedBall_zero_iff]
      have : (d : ℝ) * s / 2 ≤ r / 2 := by linarith
      exact hk1.trans this
    have hk1m : k1 ∈ K0 y := by
      by_contra h
      have := hK0 y y (by simp) k1 h
      rw [h1] at this
      exact one_ne_zero this
    rw [hDeq y y (by simp)]
    calc (1 : ℝ) = f (y - bv_pt s k1) := h1.symm
      _ ≤ _ := Finset.single_le_sum (f := fun k => f (y - bv_pt s k)) (fun k _ => hfnn _) hk1m
  have hDper : ∀ (y : HRS.Euc d) (a : Fin d → ℤ), D (y - bv_pt s a) = D y := by
    intro y a
    simp only [hD]
    have := (Equiv.addLeft a).tsum_eq (fun k : Fin d → ℤ => f (y - bv_pt s k))
    rw [← this]
    refine tsum_congr fun k => ?_
    simp [bv_pt_add, sub_sub]
  have hDpos : ∀ y, 0 < D y := fun y => lt_of_lt_of_le one_pos (hDge y)
  refine ⟨fun y => f y / D y, f.contDiff.div hDsm (fun y => (hDpos y).ne'), ?_, ?_, ?_, ?_⟩
  · refine HasCompactSupport.intro (isCompact_closedBall (0 : HRS.Euc d) r) (fun y hy => ?_)
    have : r ≤ ‖y‖ := by
      by_contra h
      exact hy (by rw [mem_closedBall_zero_iff]; linarith [not_le.1 h])
    simp [hf0 y this]
  · intro y hy
    simp [hf0 y hy]
  · intro y
    exact div_nonneg (hfnn y) (hDpos y).le
  · intro y K hK
    have hsum : ∑ k ∈ K, f (y - bv_pt s k) = D y := by
      symm
      refine tsum_eq_sum fun k hk => hf0 _ ?_
      by_contra h
      exact hk (hK k (not_le.1 h))
    calc ∑ k ∈ K, f (y - bv_pt s k) / D (y - bv_pt s k)
        = ∑ k ∈ K, f (y - bv_pt s k) / D y := Finset.sum_congr rfl fun k _ => by rw [hDper]
      _ = (∑ k ∈ K, f (y - bv_pt s k)) / D y := by rw [Finset.sum_div]
      _ = 1 := by rw [hsum]; exact div_self (hDpos y).ne'

end HRS.MS.BilipV
