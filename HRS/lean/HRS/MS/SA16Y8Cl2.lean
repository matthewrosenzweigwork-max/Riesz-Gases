import HRS.MS.SA16Y8Cl1

/-!
# S.A.16 (SA16Y8) Cl2: the regularity hypotheses of `classical_of_regular_representative` for the family (classical clause, K4, part 5)

From the uniform bounds, the uniform Hölder modulus of `D²u` and the continuity of `τ ↦ u τ x`, `∇u τ x v`, `D²u τ x v w` we derive the
bound `hb` on `iteratedFDeriv ℝ j (u τ)`, `j ≤ 2`, and its joint continuity `hcont` on `[0,t] × ℝ^d`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16Q
open HRS HRS.Whole HRS.Whole.AppendixA

section Cl2
variable {d : ℕ}

/-- a uniform Lipschitz bound gives equicontinuity -/
lemma sa16y8_equi_lip {E : Type*} [NormedAddCommGroup E] (S : Set ℝ) (g : ℝ → Euc d → E) (K : ℝ) (hK : 0 ≤ K)
    (hL : ∀ τ ∈ S, ∀ x y : Euc d, ‖g τ y - g τ x‖ ≤ K * ‖y - x‖) :
    ∀ (x₀ : Euc d) (ε : ℝ), 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ τ ∈ S, ∀ x : Euc d, dist x x₀ < δ →
      dist (g τ x) (g τ x₀) < ε := by
  intro x₀ ε hε
  refine ⟨ε / (K + 1), by positivity, fun τ hτ x hx => ?_⟩
  rw [dist_eq_norm] at hx ⊢
  have h1 := hL τ hτ x₀ x
  have h2 : ‖x - x₀‖ * (K + 1) < ε := (lt_div_iff₀ (by positivity)).1 hx
  nlinarith [norm_nonneg (x - x₀)]

/-- a uniform Hölder bound gives equicontinuity -/
lemma sa16y8_equi_hol {E : Type*} [NormedAddCommGroup E] (S : Set ℝ) (g : ℝ → Euc d → E) (K α : ℝ) (hK : 0 ≤ K)
    (hα : 0 < α)
    (hH : ∀ τ ∈ S, ∀ x h : Euc d, ‖h‖ ≤ 1 → ‖g τ (x + h) - g τ x‖ ≤ K * ‖h‖ ^ α) :
    ∀ (x₀ : Euc d) (ε : ℝ), 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ τ ∈ S, ∀ x : Euc d, dist x x₀ < δ →
      dist (g τ x) (g τ x₀) < ε := by
  intro x₀ ε hε
  set a : ℝ := ε / (2 * (K + 1)) with ha
  have ha0 : 0 < a := by positivity
  have hδ0 : 0 < a ^ α⁻¹ := Real.rpow_pos_of_pos ha0 _
  refine ⟨min 1 (a ^ α⁻¹), lt_min one_pos hδ0, fun τ hτ x hx => ?_⟩
  rw [dist_eq_norm] at hx ⊢
  have hle1 : ‖x - x₀‖ ≤ 1 := (hx.trans_le (min_le_left _ _)).le
  have hle2 : ‖x - x₀‖ ≤ a ^ α⁻¹ := (hx.trans_le (min_le_right _ _)).le
  have e : x₀ + (x - x₀) = x := by abel
  have h1 := hH τ hτ x₀ (x - x₀) hle1
  rw [e] at h1
  have h3 : ‖x - x₀‖ ^ α ≤ a := by
    calc ‖x - x₀‖ ^ α ≤ (a ^ α⁻¹) ^ α := Real.rpow_le_rpow (norm_nonneg _) hle2 hα.le
      _ = a := Real.rpow_inv_rpow ha0.le hα.ne'
  have h4 : K * ‖x - x₀‖ ^ α ≤ K * a := mul_le_mul_of_nonneg_left h3 hK
  have h5 : K * a < ε := by
    rw [ha, ← mul_div_assoc, div_lt_iff₀ (by positivity)]
    nlinarith
  exact lt_of_le_of_lt (h1.trans h4) h5

/-- joint continuity of `L ∘ g` from the two hypotheses on `g` -/
lemma sa16y8_cont_via {G E : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup E]
    [NormedSpace ℝ E] (L : G →L[ℝ] E) (S : Set ℝ) (g : ℝ → Euc d → G) (H : ℝ → Euc d → E)
    (hτ : ∀ x₀, ContinuousOn (fun τ => g τ x₀) S)
    (hx : ∀ (x₀ : Euc d) (ε : ℝ), 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ τ ∈ S, ∀ x : Euc d, dist x x₀ < δ →
      dist (g τ x) (g τ x₀) < ε)
    (hH : ∀ τ ∈ S, ∀ x, H τ x = L (g τ x)) :
    ContinuousOn (fun q : ℝ × Euc d => H q.1 q.2) (S ×ˢ univ) := by
  obtain ⟨h1, h2⟩ := sa16y8_transport L S g hτ hx
  have := sa16y8_jc S (fun τ x => L (g τ x)) h1 h2
  exact this.congr (fun q hq => hH q.1 hq.1 q.2)

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 3200000 in
theorem sa16y8_cont_assembly (t : ℝ) (u : ℝ → Euc d → ℝ) (K α : ℝ) (hK : 0 < K) (hα : 0 < α)
    (hc2 : ∀ τ ∈ Icc (0 : ℝ) t, ContDiff ℝ 2 (u τ))
    (hbd : ∀ τ ∈ Icc (0 : ℝ) t, ∀ x, ‖u τ x‖ ≤ K ∧ ‖fderiv ℝ (u τ) x‖ ≤ K ∧ ‖sa16y8_D2 (u τ) x‖ ≤ K)
    (hhol : ∀ τ ∈ Icc (0 : ℝ) t, ∀ x h : Euc d, ‖h‖ ≤ 1 →
      ‖sa16y8_D2 (u τ) (x + h) - sa16y8_D2 (u τ) x‖ ≤ K * ‖h‖ ^ α)
    (h0 : ∀ x₀, ContinuousOn (fun τ => u τ x₀) (Icc (0 : ℝ) t))
    (h1 : ∀ x₀ v, ContinuousOn (fun τ => fderiv ℝ (u τ) x₀ v) (Icc (0 : ℝ) t))
    (h2 : ∀ x₀ v w, ContinuousOn (fun τ => sa16y8_D2 (u τ) x₀ v w) (Icc (0 : ℝ) t)) :
    (∃ B : ℝ, ∀ j ≤ 2, ∀ τ ∈ Icc (0 : ℝ) t, ∀ x, ‖iteratedFDeriv ℝ j (u τ) x‖ ≤ B) ∧
    ∀ j ≤ 2, ContinuousOn (fun q : ℝ × Euc d => iteratedFDeriv ℝ j (u q.1) q.2)
      (Icc (0 : ℝ) t ×ˢ univ) := by
  have hdiff : ∀ τ ∈ Icc (0 : ℝ) t, Differentiable ℝ (u τ) := fun τ hτ =>
    (hc2 τ hτ).differentiable (by norm_num)
  have hdiff1 : ∀ τ ∈ Icc (0 : ℝ) t, Differentiable ℝ (fderiv ℝ (u τ)) := fun τ hτ =>
    ((hc2 τ hτ).fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  refine ⟨⟨K + K + K, ?_⟩, ?_⟩
  · intro j hj τ hτ x
    have hn := hbd τ hτ x
    interval_cases j
    · rw [norm_iteratedFDeriv_zero]; linarith [hn.1]
    · rw [sa16y8_iter1_eq, LinearIsometryEquiv.norm_map]; linarith [hn.2.1]
    · have e : ‖iteratedFDeriv ℝ 2 (u τ) x‖ = ‖sa16y8_D2 (u τ) x‖ := by
        have := sa16y8_norm_D2_iter (u := u τ) 0 x
        rw [norm_iteratedFDeriv_zero, zero_add] at this
        exact this.symm
      rw [e]; linarith [hn.2.2]
  · intro j hj
    interval_cases j
    · refine sa16y8_cont_via (continuousMultilinearCurryFin0 ℝ (Euc d) ℝ).symm.toContinuousLinearEquiv.toContinuousLinearMap
        (Icc (0 : ℝ) t) u (fun τ x => iteratedFDeriv ℝ 0 (u τ) x) h0 (sa16y8_equi_lip _ u K hK.le ?_) ?_
      · intro τ hτ x y
        exact (Convex.norm_image_sub_le_of_norm_fderiv_le (fun z _ => (hdiff τ hτ) z)
          (fun z _ => (hbd τ hτ z).2.1) convex_univ (mem_univ x) (mem_univ y))
      · intro τ _ x
        rw [iteratedFDeriv_zero_eq_comp]
        rfl
    · refine sa16y8_cont_via
        (continuousMultilinearCurryFin1 ℝ (Euc d) ℝ).symm.toContinuousLinearEquiv.toContinuousLinearMap
        (Icc (0 : ℝ) t) (fun τ x => fderiv ℝ (u τ) x) (fun τ x => iteratedFDeriv ℝ 1 (u τ) x) ?_ (sa16y8_equi_lip _ _ K hK.le ?_) ?_
      · intro x₀
        exact continuousOn_clm_apply.2 (h1 x₀)
      · intro τ hτ x y
        exact (Convex.norm_image_sub_le_of_norm_fderiv_le (f := fderiv ℝ (u τ)) (fun z _ => (hdiff1 τ hτ) z)
          (fun z _ => (hbd τ hτ z).2.2) convex_univ (mem_univ x) (mem_univ y))
      · intro τ _ x
        rw [sa16y8_iter1_eq]
        rfl
    · refine sa16y8_cont_via (sa16y8_Psi d) (Icc (0 : ℝ) t) (fun τ x => sa16y8_D2 (u τ) x) (fun τ x => iteratedFDeriv ℝ 2 (u τ) x) ?_
        (sa16y8_equi_hol _ _ K α hK.le hα (fun τ hτ x h hh => hhol τ hτ x h hh)) ?_
      · intro x₀
        refine continuousOn_clm_apply.2 (fun v => ?_)
        exact continuousOn_clm_apply.2 (h2 x₀ v)
      · intro τ hτ x
        exact sa16y8_iter2_eq (hc2 τ hτ) x

end Cl2

end HRS.Whole.AppendixA.Phase2SA16Q
