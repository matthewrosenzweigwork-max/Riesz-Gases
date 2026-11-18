import HRS.MS.SA16Y11Dr2
import HRS.MS.SA16Y4Ap2
import HRS.MS.SA16Y4Ip1

/-!
# S.A.16 (SA16Y11) Dr3: the interpolated truncated mollified drift difference is a bounded coefficient with bound linear in the difference

`sa16y11_bcInt_diff`: if `b1 r - b2 r` has all components with `‖D^k‖ ≤ δ` (`k ≤ m+1`) on the nodes, then for every `σ ∈ [0,t]`, `N`,
`(j,x) ↦ bcInt b1 σ j x - bcInt b2 σ j x` is `SA16BddCoef (m+1) (C δ)` (`C` from `sa16y11_tm_bdd`, independent of `N`, `t`, `σ`).
Uses `tm` linear, the hat weights convex (`sa16y4_bddCoef_convex`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16Q

section Dr3
variable {d : ℕ}

lemma sa16y11_tm_sub (n : ℕ) {f g : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Continuous f) (hg : Continuous g)
    (x : EuclideanSpace ℝ (Fin d)) :
    sa16y4_tm d n (fun y => f y - g y) x = sa16y4_tm d n f x - sa16y4_tm d n g x := by
  unfold sa16y4_tm
  have hρ : Continuous (fun y => sa16y_rho d n (x - y)) :=
    (sa16y_rho_smooth n).continuous.comp (continuous_const.sub continuous_id)
  have hint : ∀ u : EuclideanSpace ℝ (Fin d) → ℝ, Continuous u →
      Integrable (fun y => u y * sa16y_rho d n (x - y)) := fun u hu =>
    (hu.mul hρ).integrable_of_hasCompactSupport ((sa16y4_cc_shift (sa16y4_rho_cc n) x).mul_left)
  rw [← mul_sub, ← integral_sub (hint f hf) (hint g hg)]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [sub_mul]

theorem sa16y11_bcInt_diff (d m : ℕ) (hd : 1 ≤ d) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ δ : ℝ, 0 ≤ δ → ∀ t : ℝ, 0 < t →
      ∀ b1 b2 : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d), ∀ N : ℕ, 1 ≤ N →
      (∀ r ∈ Icc (0 : ℝ) t, ∀ j : Fin d, ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (fun y => b1 r y j) ∧
        ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (fun y => b2 r y j)) →
      (∀ r ∈ Icc (0 : ℝ) t, ∀ j : Fin d, ∀ k ≤ m + 1, ∀ x,
        ‖iteratedFDeriv ℝ k (fun y => b1 r y j - b2 r y j) x‖ ≤ δ) →
      ∀ σ ∈ Icc (0 : ℝ) t, SA16BddCoef (m + 1) (C * δ)
        (fun j x => sa16y4_bcInt d N t b1 σ j x - sa16y4_bcInt d N t b2 σ j x) := by
  obtain ⟨C, hC1, hC⟩ := sa16y11_tm_bdd d m hd
  refine ⟨C, hC1, fun δ hδ t ht b1 b2 N hN hsm hder σ hσ => ?_⟩
  have hc : ∀ i ∈ Finset.range (N + 1), SA16BddCoef (m + 1) (C * δ)
      (fun j => sa16y4_tm d N (fun y => b1 (t - (i : ℝ) * t / N) y j - b2 (t - (i : ℝ) * t / N) y j)) := by
    intro i hi
    have hr := sa16y4_node_mem hN ht hi
    exact hC δ hδ N _ (fun j => ((hsm _ hr j).1).sub (hsm _ hr j).2) (fun j k hk x => hder _ hr j k hk x)
  have hw0 : ∀ i ∈ Finset.range (N + 1), 0 ≤ sa16y4_hat N t i σ := fun i _ => sa16y4_hat_nonneg N t i σ
  have h := sa16y4_bddCoef_convex (Finset.range (N + 1)) (fun i => sa16y4_hat N t i σ) hw0
    (sa16y4_hat_sum hN ht hσ)
    (c := fun i j => sa16y4_tm d N (fun y => b1 (t - (i : ℝ) * t / N) y j - b2 (t - (i : ℝ) * t / N) y j)) hc
  have e : (fun j x => sa16y4_bcInt d N t b1 σ j x - sa16y4_bcInt d N t b2 σ j x) = fun j x =>
      ∑ i ∈ Finset.range (N + 1), sa16y4_hat N t i σ *
        sa16y4_tm d N (fun y => b1 (t - (i : ℝ) * t / N) y j - b2 (t - (i : ℝ) * t / N) y j) x := by
    funext j x
    unfold sa16y4_bcInt
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hr := sa16y4_node_mem hN ht hi
    rw [sa16y11_tm_sub N (hsm _ hr j).1.continuous (hsm _ hr j).2.continuous x, mul_sub]
  rw [e]; exact h

end Dr3

end HRS.Whole.AppendixA.Phase2SA16R

end
