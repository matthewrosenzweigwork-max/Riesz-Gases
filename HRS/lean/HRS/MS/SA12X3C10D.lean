import HRS.MS.SA12X3C10C

/-!
# S.A.12 C10 (SA12X3), part D: weighted `Y` integral versus the cell energy; fine-lattice cover of a real ball
-/

set_option autoImplicit false
set_option maxHeartbeats 12800000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12 HRS.MH.AdjointRd.Phase2SA12Construction

variable {d : ℕ}

theorem sa12x3_wY_le_jetSq (m : ℕ) {w u : Euc d → ℝ} (hw : Continuous w) (hwc : HasCompactSupport w)
    (hu : ContDiff ℝ ∞ u) :
    Integrable (fun x => w x ^ 2 * sa12z3_Y m u x) ∧
      ∫ x, w x ^ 2 * sa12z3_Y m u x ≤ HRS.MH.AdjointRd.jetSq m w u := by
  have hi : ∀ {r : ℕ} (γ : Fin r → Fin d), Integrable (fun x => (w x * partialDeriv γ u x) ^ 2) := by
    intro r γ
    have hcont : Continuous (fun x => (w x * partialDeriv γ u x) ^ 2) :=
      (hw.mul (sa12z3_pd_contDiff_inf hu γ).continuous).pow 2
    have hcs : HasCompactSupport (fun x => (w x * partialDeriv γ u x) ^ 2) :=
      (hwc.mul_right (f' := partialDeriv γ u)).comp_left (g := fun t : ℝ => t ^ 2) (by simp)
    exact hcont.integrable_of_hasCompactSupport (μ := (volume : Measure (Euc d))) hcs
  have hpt : ∀ x, w x ^ 2 * sa12z3_Y m u x =
      ∑ r ∈ Finset.range (m + 1), ∑ γ : Fin r → Fin d, (w x * partialDeriv γ u x) ^ 2 := by
    intro x
    unfold sa12z3_Y
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun γ _ => ?_
    ring
  have hint : Integrable (fun x => w x ^ 2 * sa12z3_Y m u x) := by
    simp_rw [hpt]
    exact integrable_finset_sum _ fun r _ => integrable_finset_sum _ fun γ _ => hi γ
  refine ⟨hint, ?_⟩
  simp_rw [hpt]
  rw [integral_finset_sum _ fun r _ => integrable_finset_sum _ fun γ _ => hi γ]
  unfold HRS.MH.AdjointRd.jetSq
  refine Finset.sum_le_sum fun r hr => ?_
  rw [integral_finset_sum _ fun γ _ => hi γ]
  have h0 : 0 ≤ ∑ γ : Fin r → Fin d, ∫ x, (w x * partialDeriv γ u x) ^ 2 :=
    Finset.sum_nonneg fun γ _ => integral_nonneg fun x => sq_nonneg _
  have hc1 : (1 : ℝ) ≤ (Nat.choose m r : ℝ) := by
    have : 1 ≤ Nat.choose m r := Nat.choose_pos (Nat.lt_succ_iff.1 (Finset.mem_range.1 hr))
    exact_mod_cast this
  nlinarith

theorem sa12x3_cover_pt (hd : 1 ≤ d) {χ : Euc d → ℝ} (hχ : IsUlocCutoff χ) {Ψ : ℝ → Euc d → Euc d} {τ L : ℝ}
    (hL0 : 0 ≤ L) (hL : ∀ x y, ‖Function.invFun (Ψ τ) x - Function.invFun (Ψ τ) y‖ ≤ L * ‖x - y‖)
    (K0 : Finset (Fin d → ℤ)) (hK0 : ∀ k : Fin d → ℤ, ‖cellPt d k‖ ≤ 2 * L + 1 → k ∈ K0) (c : Euc d) :
    ∃ z0 : Fin d → ℤ, ∀ x ∈ closedBall c 2, ∃ k ∈ K0, advCutoff χ Ψ τ (cellPt d (z0 + k)) x = 1 := by
  obtain ⟨z0, hz0⟩ := HRS.MS.UniqC3.exists_cellPt_near hd (Function.invFun (Ψ τ) c)
  refine ⟨z0, fun x hx => ?_⟩
  obtain ⟨z1, hz1⟩ := HRS.MS.UniqC3.exists_cellPt_near hd (Function.invFun (Ψ τ) x)
  refine ⟨z1 - z0, hK0 _ ?_, ?_⟩
  · have hadd : cellPt d z1 = cellPt d z0 + cellPt d (z1 - z0) := by
      rw [← sa12z3_cellPt_add]; simp
    have hxc : ‖x - c‖ ≤ 2 := by rw [mem_closedBall, dist_eq_norm] at hx; exact hx
    have h1 := hL x c
    have h2 : L * ‖x - c‖ ≤ L * 2 := mul_le_mul_of_nonneg_left hxc hL0
    have e : cellPt d (z1 - z0) = (cellPt d z1 - Function.invFun (Ψ τ) x) +
        (Function.invFun (Ψ τ) x - Function.invFun (Ψ τ) c) + (Function.invFun (Ψ τ) c - cellPt d z0) := by
      rw [eq_sub_of_add_eq' hadd.symm]; abel
    rw [e]
    have n1 : ‖cellPt d z1 - Function.invFun (Ψ τ) x‖ ≤ 1 / 2 := by rw [norm_sub_rev]; exact hz1
    have n3 : ‖Function.invFun (Ψ τ) c - cellPt d z0‖ ≤ 1 / 2 := hz0
    calc _ ≤ ‖cellPt d z1 - Function.invFun (Ψ τ) x‖ + ‖Function.invFun (Ψ τ) x - Function.invFun (Ψ τ) c‖ +
          ‖Function.invFun (Ψ τ) c - cellPt d z0‖ := (norm_add₃_le)
      _ ≤ 2 * L + 1 := by linarith
  · rw [add_sub_cancel]
    unfold advCutoff
    apply hχ.2.2.2.2
    rw [mem_closedBall, dist_zero_right]
    have : ‖Function.invFun (Ψ τ) x - cellPt d z1‖ ≤ 1 / 2 := hz1
    linarith

end HRS.MH.AdjointRd.Phase2SA12Near
