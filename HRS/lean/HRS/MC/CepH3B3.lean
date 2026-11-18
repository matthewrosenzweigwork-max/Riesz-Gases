import HRS.MC.CepH3B2

/-!
# Packet CEPH3, part B3: the alcove is open; local uniform convergence `G n → ∇Φ` on compacta of the alcove
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

noncomputable section

namespace HRS.MC.CepH3

open HRS HRS.MC.Cepa

variable {N : ℕ} {J : ℝ → Ch N → Ch N}

lemma h3b_alcove_isOpen : IsOpen (cep_Alcove N) := by
  have h1 : IsOpen {z : Ch N | ∀ k l : Fin N, k < l → z k < z l} := by
    have : {z : Ch N | ∀ k l : Fin N, k < l → z k < z l} =
        ⋂ k : Fin N, ⋂ l : Fin N, {z : Ch N | k < l → z k < z l} := by
      ext z; simp
    rw [this]
    refine isOpen_iInter_of_finite fun k => isOpen_iInter_of_finite fun l => ?_
    by_cases hkl : k < l
    · simp only [hkl, true_implies]
      exact isOpen_lt (by fun_prop) (by fun_prop)
    · simp only [hkl, false_implies, setOf_true]; exact isOpen_univ
  have h2 : IsOpen {z : Ch N | ∀ k l : Fin N, z l < z k + 1} := by
    have : {z : Ch N | ∀ k l : Fin N, z l < z k + 1} =
        ⋂ k : Fin N, ⋂ l : Fin N, {z : Ch N | z l < z k + 1} := by
      ext z; simp
    rw [this]
    exact isOpen_iInter_of_finite fun k => isOpen_iInter_of_finite fun l =>
      isOpen_lt (by fun_prop) (by fun_prop)
  exact h1.inter h2

/-- Local uniform convergence of the Yosida approximations of `∇Φ` on compact subsets of the alcove. -/
lemma h3b_G_unif (hJ : cep_Yosida 1 N J) {K : Set (Ch N)} (hK : IsCompact K) (hKA : K ⊆ cep_Alcove N)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ z ∈ K,
      ‖(n : ℝ) • (z - J n z) - h3a_gam z‖ ≤ ε := by
  obtain ⟨δ, hδ, hthick⟩ := hK.exists_cthickening_subset_open h3b_alcove_isOpen hKA
  have hcomp : IsCompact (Metric.cthickening δ K) := hK.cthickening
  have hunif := hcomp.uniformContinuousOn_of_continuous (h3a_gam_continuousOn.mono hthick)
  obtain ⟨η, hη, hηprop⟩ := Metric.uniformContinuousOn_iff.mp hunif ε hε
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (h3a_gam_continuousOn.mono hKA)
  have hB0 : 0 ≤ B ∨ K = ∅ := by
    rcases K.eq_empty_or_nonempty with h | ⟨x, hx⟩
    · exact Or.inr h
    · exact Or.inl ((norm_nonneg _).trans (hB x hx))
  set m := min δ η with hm
  have hmpos : 0 < m := lt_min hδ hη
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (|B| / m)
  refine ⟨n₀, fun n hn z hz => ?_⟩
  have hnpos : (0 : ℝ) < n := by
    have : (0:ℝ) < n₀ := lt_of_le_of_lt (by positivity) hn₀
    exact lt_of_lt_of_le this (by exact_mod_cast hn)
  have hnge : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
  have hG := h3b_G_le hJ hnpos (hKA hz)
  have hforce := h3b_force hJ hnpos z
  have hdist : ‖J n z - z‖ < m := by
    have e : J n z - z = -(((n : ℝ))⁻¹ • ((n : ℝ) • (z - J n z))) := by
      rw [smul_smul, inv_mul_cancel₀ hnpos.ne', one_smul]; abel
    rw [e, norm_neg, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hnpos]
    have h1 : ‖(n : ℝ) • (z - J n z)‖ ≤ |B| := hG.trans ((hB z hz).trans (le_abs_self B))
    have h2 : |B| / m < n := lt_of_lt_of_le hn₀ hnge
    rw [div_lt_iff₀ hmpos] at h2
    calc (n : ℝ)⁻¹ * ‖(n : ℝ) • (z - J n z)‖ ≤ (n : ℝ)⁻¹ * |B| :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ < m := by rw [inv_mul_lt_iff₀ hnpos]; linarith
  have hmem : J n z ∈ Metric.cthickening δ K :=
    Metric.mem_cthickening_of_dist_le (J n z) z δ K hz (by
      rw [dist_eq_norm]; exact (hdist.trans_le (min_le_left _ _)).le)
  have := hηprop (J n z) hmem z (Metric.self_subset_cthickening _ hz) (by
    rw [dist_eq_norm]; exact hdist.trans_le (min_le_right _ _))
  rw [dist_eq_norm] at this
  rw [← hforce]
  exact this.le

end HRS.MC.CepH3
