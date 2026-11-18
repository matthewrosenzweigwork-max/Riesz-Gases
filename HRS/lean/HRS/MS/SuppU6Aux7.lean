import HRS.MS.SuppU6Aux6

/-!
# U6 aux 7: uniform derivative bounds of `χ_j ∘ F_j`
-/

noncomputable section

open scoped RealInnerProductSpace ContDiff
open MeasureTheory Metric Filter Topology Finset

namespace HRS.U6

variable {d : ℕ}

lemma norm_u6B_A_le {k j : EuclideanSpace ℝ (Fin d)} (h : ‖k - j‖ ≤ 1 / 2)
    (v : EuclideanSpace ℝ (Fin d)) : ‖u6B k (u6A j v)‖ ≤ 2 * ‖v‖ := by
  have h1 := norm_u6B_sq k (u6A j v)
  have h2 : ⟪k, u6A j v⟫ = ⟪u6A j k, v⟫ := inner_u6A j k v
  have h3 : ‖u6A j k‖ ≤ 3 / 2 := by
    have : u6A j k = u6A j j + u6A j (k - j) := by rw [← map_add]; congr 1; abel
    rw [this]
    calc _ ≤ ‖u6A j j‖ + ‖u6A j (k - j)‖ := norm_add_le _ _
      _ ≤ 1 + 1 / 2 := add_le_add (norm_u6A_self_le j) ((norm_u6A_le j _).trans h)
      _ = 3 / 2 := by norm_num
  have h4 : |⟪u6A j k, v⟫| ≤ 3 / 2 * ‖v‖ :=
    (abs_real_inner_le_norm _ _).trans (by gcongr)
  have h5 : ⟪u6A j k, v⟫ ^ 2 ≤ (3 / 2 * ‖v‖) ^ 2 := by
    rw [← sq_abs]; gcongr
  have h6 := norm_u6A_le j v
  have h7 : ‖u6A j v‖ ^ 2 ≤ ‖v‖ ^ 2 := by gcongr
  have : ‖u6B k (u6A j v)‖ ^ 2 ≤ (2 * ‖v‖) ^ 2 := by
    rw [h1, h2]; nlinarith [sq_nonneg ‖v‖]
  exact le_of_sq_le_sq this (by positivity)

lemma u6Fi_F_lin (k j : EuclideanSpace ℝ (Fin d)) (u : EuclideanSpace ℝ (Fin d)) :
    u6Fi k (u6F j u) = ((u6B k).comp (u6A j)) u + u6B k (j - k) := by
  unfold u6Fi u6F
  show u6B k (j + u6A j u - k) = u6B k (u6A j u) + u6B k (j - k)
  rw [← map_add]
  congr 1
  abel

section Net

variable {S : Set (EuclideanSpace ℝ (Fin d))}

lemma u6_chi_chart_eq (j : S) (N : Finset S)
    (hN : ∀ k : S, k ∈ N ↔ ∃ u v : EuclideanSpace ℝ (Fin d), ‖u‖ ≤ 1 / 4 ∧ ‖v‖ ≤ 1 / 4 ∧
      u6F k.1 u = u6F j.1 v) :
    (fun u => u6chi S j (j.1 + u6A j.1 u)) = fun u => u6psi d u *
      u6G (∑ k ∈ N, u6psi d (((u6B k.1).comp (u6A j.1)) u + u6B k.1 (j.1 - k.1)) ^ 2) := by
  funext u
  have e1 : u6psik S j (j.1 + u6A j.1 u) = u6psi d u := by
    unfold u6psik
    exact congrArg (u6psi d) (u6Fi_F j.1 u)
  unfold u6chi
  rw [e1]
  by_cases h0 : u6psi d u = 0
  · rw [h0, zero_mul, zero_mul]
  · congr 2
    have hu : ‖u‖ < 1 / 4 := by
      by_contra hcon
      push Not at hcon
      exact h0 (u6psi_eq_zero hcon)
    unfold u6Psi
    rw [tsum_eq_sum (s := N)]
    · refine Finset.sum_congr rfl (fun k _ => ?_)
      unfold u6psik
      rw [show j.1 + u6A j.1 u = u6F j.1 u from rfl, u6Fi_F_lin]
    · intro k hk
      have : u6psik S k (j.1 + u6A j.1 u) = 0 := by
        by_contra hne
        apply hk
        rw [hN]
        refine ⟨u6Fi k.1 (u6F j.1 u), u, ?_, hu.le, u6F_Fi _ _⟩
        by_contra hcon
        push Not at hcon
        exact hne (u6psi_eq_zero hcon.le)
      rw [this]; ring

lemma u6_chart_deriv_bound (hS : S.Pairwise (u6Sep (1 / 16 : ℝ))) (n : ℕ) :
    ∃ C : ℝ, ∀ (j : S) (u : EuclideanSpace ℝ (Fin d)),
      ‖iteratedFDeriv ℝ n (fun u' => u6chi S j (j.1 + u6A j.1 u')) u‖ ≤ C := by
  obtain ⟨M, hM⟩ := u6psi_bound d
  obtain ⟨K, hK⟩ := u6_count_sub (d := d) (by norm_num : (0 : ℝ) < 1 / 16) (by norm_num)
    hS (1 / 4) (1 / 4) (by norm_num) (by norm_num)
  obtain ⟨C, hC⟩ := u6_chi_bound (u6psi_contDiff d) M hM u6G_contDiff K 2 (by norm_num) n
  refine ⟨C, fun j u => ?_⟩
  have hfin := (hK j.1 {k : S | ∃ u v : EuclideanSpace ℝ (Fin d), ‖u‖ ≤ 1 / 4 ∧ ‖v‖ ≤ 1 / 4 ∧
      u6F k.1 u = u6F j.1 v} (fun k hk => hk))
  set N := hfin.1.toFinset with hNdef
  have hN : ∀ k : S, k ∈ N ↔ ∃ u v : EuclideanSpace ℝ (Fin d), ‖u‖ ≤ 1 / 4 ∧ ‖v‖ ≤ 1 / 4 ∧
      u6F k.1 u = u6F j.1 v := fun k => by simp [hNdef]
  have hcard : N.card ≤ K := by
    have := hfin.2
    rw [hfin.1.encard_eq_coe_toFinset_card] at this
    exact_mod_cast this
  rw [u6_chi_chart_eq j N hN]
  refine hC N (fun k => (u6B k.1).comp (u6A j.1)) (fun k => u6B k.1 (j.1 - k.1)) hcard ?_ u
  intro k hk
  obtain ⟨u1, v1, hu1, hv1, h⟩ := (hN k).mp hk
  have := (u6_pair_bounds h).1
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (fun v => ?_)
  exact norm_u6B_A_le (by linarith) v

end Net

end HRS.U6
