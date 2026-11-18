import HRS.MS.SA16Y10Bd2
import HRS.MS.SA16Y4Ap2

/-!
# S.A.16 (SA16Y10) Bd3: `sa16y10_bcInt_diff` (stability G3(b), sub regime)

`‖B_{bcInt b₁ σ} - B_{bcInt b₂ σ}‖_{W^{m+2}→W^{m+1}} ≤ K δ` where `δ` bounds the `C^{m+1}` size of the coordinates of
`b₁ r - b₂ r` (`r ∈ [0,t]`), uniformly in the mollification index `N`.
-/

set_option autoImplicit false

noncomputable section
open scoped ContDiff
open Filter MeasureTheory

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

variable {d : ℕ}

set_option maxHeartbeats 6400000 in
theorem sa16y10_bcInt_diff (d m : ℕ) (p : ℝ) [Fact (2 ≤ p)] :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (t : ℝ), 0 < t → ∀ (N : ℕ), 1 ≤ N →
      ∀ b₁ b₂ : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d), ∀ δ : ℝ, 0 ≤ δ →
      (∀ r ∈ Set.Icc (0 : ℝ) t, ∀ j : Fin d, Continuous (fun y => b₁ r y j) ∧ Continuous (fun y => b₂ r y j)) →
      (∀ r ∈ Set.Icc (0 : ℝ) t, ∀ j : Fin d,
        ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (fun y => b₁ r y j - b₂ r y j)) →
      (∀ r ∈ Set.Icc (0 : ℝ) t, ∀ j y, |b₁ r y j - b₂ r y j| ≤ δ) →
      (∀ r ∈ Set.Icc (0 : ℝ) t, ∀ j i, 1 ≤ i → i ≤ m + 1 → ∀ x,
        ‖iteratedFDeriv ℝ i (fun y => b₁ r y j - b₂ r y j) x‖ ≤ δ) →
      ∀ {B₁ B₂ : ℝ}, (∀ σ ∈ Set.Icc (0 : ℝ) t, SA16BddCoef (m + 1) B₁ (sa16y4_bcInt d N t b₁ σ)) →
        (∀ σ ∈ Set.Icc (0 : ℝ) t, SA16BddCoef (m + 1) B₂ (sa16y4_bcInt d N t b₂ σ)) →
      ∀ σ ∈ Set.Icc (0 : ℝ) t,
        ‖sa16so_B d (m + 1) p (sa16y4_bcInt d N t b₁ σ) - sa16so_B d (m + 1) p (sa16y4_bcInt d N t b₂ σ)‖ ≤ K * δ := by
  obtain ⟨Cb, hCb0, hCb⟩ := sa16y10_tm_bdd d m
  refine ⟨sa16so_cB d (m + 1) Cb, sa16so_cB_nonneg d (m + 1) hCb0, fun t ht N hN b₁ b₂ δ hδ hcont hsm hb0 hbj B₁ B₂ hB1 hB2 σ hσ => ?_⟩
  have hnode : ∀ i ∈ Finset.range (N + 1), SA16BddCoef (m + 1) (Cb * δ)
      (fun j => sa16y4_tm d N (fun y => b₁ (t - (i : ℝ) * t / N) y j - b₂ (t - (i : ℝ) * t / N) y j)) := fun i hi => by
    have hmem := sa16y4_node_mem hN ht hi
    exact hCb N (fun j y => b₁ (t - (i : ℝ) * t / N) y j - b₂ (t - (i : ℝ) * t / N) y j) δ hδ
      (fun j => hsm _ hmem j) (fun j y => hb0 _ hmem j y) (fun j k hk1 hk2 x => hbj _ hmem j k hk1 hk2 x)
  have hconv := sa16y4_bddCoef_convex (Finset.range (N + 1)) (fun i => sa16y4_hat N t i σ)
    (fun i _ => sa16y4_hat_nonneg N t i σ) (sa16y4_hat_sum hN ht hσ)
    (c := fun i j => sa16y4_tm d N (fun y => b₁ (t - (i : ℝ) * t / N) y j - b₂ (t - (i : ℝ) * t / N) y j)) hnode
  have hD : (fun i x => sa16y4_bcInt d N t b₁ σ i x - sa16y4_bcInt d N t b₂ σ i x) =
      fun j x => ∑ i ∈ Finset.range (N + 1), sa16y4_hat N t i σ *
        sa16y4_tm d N (fun y => b₁ (t - (i : ℝ) * t / N) y j - b₂ (t - (i : ℝ) * t / N) y j) x := by
    funext j x
    unfold sa16y4_bcInt
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hmem := sa16y4_node_mem hN ht hi
    rw [sa16y10_tm_sub N (hcont _ hmem j).1 (hcont _ hmem j).2, ← mul_sub]
  rw [← sa16so_B_sub (hB1 σ hσ) (hB2 σ hσ)]
  refine (sa16so_B_norm (hD ▸ hconv)).trans (le_of_eq ?_)
  unfold sa16so_cB
  ring

end HRS.Whole.AppendixA.Phase2SA16R

end
