import HRS.MS.SA12X2R36O

/-!
# S.A.12 R36 (SA12X2), part P: the density approximation theorem

For `a ∈ C^(m+1)_c` with `tsupport a ⊆ B̄(0,R)` and bounded jets `‖∂^j a‖ ≤ B` (`j ≤ m+1`), the mollified
functions `b_n(x) = ∫ φ_n(x-y) a(y) dy` are smooth, supported in `B̄(0,R+1)`, have tuple partials bounded by `B`
(orders `≤ m+1`), and their tuple partials converge pointwise to those of `a`.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12

open HRS HRS.Whole

variable {d : ℕ}

theorem sa12x2_approx (m : ℕ) (B R : ℝ) (a : Euc d → ℝ) (ha : ContDiff ℝ (m + 1) a)
    (hac : HasCompactSupport a) (hR : tsupport a ⊆ closedBall (0 : Euc d) R)
    (hB : ∀ j ≤ m + 1, ∀ x, ‖iteratedFDeriv ℝ j a x‖ ≤ B) :
    ∃ b : ℕ → Euc d → ℝ, (∀ n, ContDiff ℝ ∞ (b n)) ∧
      (∀ n, tsupport (b n) ⊆ closedBall (0 : Euc d) (R + 1)) ∧
      (∀ n, ∀ j ≤ m + 1, ∀ idx : Fin j → Fin d, ∀ x, |partialDeriv idx (b n) x| ≤ B) ∧
      (∀ j ≤ m + 1, ∀ idx : Fin j → Fin d, ∀ x,
        Tendsto (fun n => partialDeriv idx (b n) x) atTop (𝓝 (partialDeriv idx a x))) := by
  have hpd : ∀ n : ℕ, ∀ j ≤ m + 1, ∀ idx : Fin j → Fin d, ∀ x,
      partialDeriv idx (fun x => ∫ y, sa12x2_mol (d := d) n (x - y) * a y) x =
        ∫ y, sa12x2_mol (d := d) n (x - y) * partialDeriv idx a y := by
    intro n j hj idx x
    exact sa12x2_pd_mol (d := d) (φ := sa12x2_mol (d := d) n)
      (sa12x2_mol_contDiff (d := d) n).continuous.locallyIntegrable j a
      (ha.of_le (by exact_mod_cast hj)) hac idx x
  refine ⟨fun n x => ∫ y, sa12x2_mol (d := d) n (x - y) * a y,
    fun n => sa12x2_mol_contDiff_conv ha.continuous n, ?_, ?_, ?_⟩
  · intro n
    apply closure_minimal _ isClosed_closedBall
    intro x hx
    obtain ⟨y, hy⟩ : ∃ y, sa12x2_mol (d := d) n (x - y) * a y ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hx (by simp only [hcon, integral_zero])
    have h1 : sa12x2_mol (d := d) n (x - y) ≠ 0 := left_ne_zero_of_mul hy
    have h2 : a y ≠ 0 := right_ne_zero_of_mul hy
    have hy1 : y ∈ closedBall (0 : Euc d) R := hR (subset_tsupport _ h2)
    have hxy : x - y ∈ ball (0 : Euc d) (1 / ((n : ℝ) + 1)) := by
      have hmem : x - y ∈ Function.support (sa12x2_mol (d := d) n) := h1
      unfold sa12x2_mol at hmem
      rw [(sa12x2_bump (d := d) n).support_normed_eq (μ := (volume : Measure (Euc d)))] at hmem
      exact hmem
    have hn1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    rw [mem_closedBall_zero_iff] at hy1 ⊢
    rw [mem_ball_zero_iff] at hxy
    have := norm_le_norm_add_norm_sub' x y
    linarith
  · intro n j hj idx x
    rw [hpd n j hj idx x]
    have hg : Continuous (fun y => partialDeriv idx a y) :=
      sa12x2_pd_cont (m := m) ha hj idx
    refine sa12x2_mol_bound (φ := sa12x2_mol (d := d) n) (sa12x2_mol_nonneg (d := d) n)
      (sa12x2_mol_integral (d := d) n) ?_ (sa12x2_mol_hasCompactSupport (d := d) n) hg B ?_ x
    · exact (sa12x2_mol_contDiff (d := d) n).continuous.integrable_of_hasCompactSupport
        (sa12x2_mol_hasCompactSupport (d := d) n)
    · intro y
      exact (sa12x2_pd_le_norm a idx y).trans (hB j hj y)
  · intro j hj idx x
    have hfun : (fun n : ℕ => partialDeriv idx (fun x => ∫ y, sa12x2_mol (d := d) n (x - y) * a y) x) =
        fun n : ℕ => ∫ y, sa12x2_mol (d := d) n (x - y) * partialDeriv idx a y :=
      funext fun n => hpd n j hj idx x
    show Tendsto (fun n : ℕ => partialDeriv idx (fun x => ∫ y, sa12x2_mol (d := d) n (x - y) * a y) x)
      atTop (𝓝 (partialDeriv idx a x))
    rw [hfun]
    exact sa12x2_mol_tendsto (sa12x2_pd_cont (m := m) ha hj idx) x

end HRS.MH.AdjointRd.Phase2SA12
