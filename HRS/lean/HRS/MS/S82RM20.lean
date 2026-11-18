import HRS.MS.S82RM19

/-!
# S8.2 R02 (S82R), M20: telescoping over changed coordinates
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Function
open scoped ENNReal BigOperators

namespace HRS.MS.S82R
open HRS.External

variable {E : Type*} [MeasurableSpace E]

lemma s82r_config_chain {μ : Measure E} [IsProbabilityMeasure μ] (V : WeakPotential μ) {ψ0 : E → ℝ}
    {M M₁ : ℝ} (hψ : IsField μ ψ0 M M₁) {n : ℕ} {lam : ℝ} (hlam : 0 ≤ lam) {P : ℝ}
    (hP : lam * n * V.γ ≤ P) (i : Fin n) (x y : Fin n → E) (s : Finset (Fin n))
    (hs : s ⊆ Finset.univ.erase i) (z : E) :
    |s82r_nd μ (s82r_PhiC V ψ0 lam i x) z - s82r_nd μ (s82r_PhiC V ψ0 lam i (s82r_hyb x y s)) z| ≤
      ∑ ℓ ∈ s, (open Classical in if x ℓ = y ℓ then 0 else
        (Real.exp (M + (M₁ + P)) * s82r_d V lam z (x ℓ) + Real.exp (M + (M₁ + P)) ^ 2 * (lam * V.γ)) +
        (Real.exp (M + (M₁ + P)) * s82r_d V lam z (y ℓ) + Real.exp (M + (M₁ + P)) ^ 2 * (lam * V.γ))) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have : s82r_hyb x y ∅ = x := by funext ℓ; simp [s82r_hyb]
      rw [this]; simp
  | insert j s hj ih =>
      have hs' : s ⊆ Finset.univ.erase i := (Finset.subset_insert _ _).trans hs
      have hjmem : j ∈ Finset.univ.erase i := hs (Finset.mem_insert_self _ _)
      rw [Finset.sum_insert hj]
      have h1 := ih hs'
      set c1 := s82r_hyb x y s with hc1
      have hc2 : s82r_hyb x y (insert j s) = update c1 j (y j) := s82r_hyb_update x y s j hj
      have hc1j : c1 j = x j := s82r_hyb_eq x y s j hj
      refine (abs_sub_le _ (s82r_nd μ (s82r_PhiC V ψ0 lam i c1) z) _).trans ?_
      have h2 : |s82r_nd μ (s82r_PhiC V ψ0 lam i c1) z -
          s82r_nd μ (s82r_PhiC V ψ0 lam i (s82r_hyb x y (insert j s))) z| ≤
          (if x j = y j then 0 else
          (Real.exp (M + (M₁ + P)) * s82r_d V lam z (x j) + Real.exp (M + (M₁ + P)) ^ 2 * (lam * V.γ)) +
          (Real.exp (M + (M₁ + P)) * s82r_d V lam z (y j) + Real.exp (M + (M₁ + P)) ^ 2 * (lam * V.γ))) := by
        by_cases hxy : x j = y j
        · have : s82r_hyb x y (insert j s) = c1 := by
            rw [hc2]; funext ℓ
            by_cases h : ℓ = j
            · subst h; simp [hc1j, hxy]
            · simp [Function.update_of_ne h]
          rw [this]; simp [hxy]
        · rw [if_neg hxy]
          set Ψ : E → ℝ := fun z => ψ0 z - lam * ∑ l ∈ (Finset.univ.erase i).erase j, V.q z (c1 l) with hΨ
          have hΦ1 : s82r_PhiC V ψ0 lam i c1 = fun z => Ψ z - lam * V.q z (x j) := by
            rw [s82r_PhiC_split V ψ0 lam i j hjmem c1, hc1j]
          have hΦ2 : s82r_PhiC V ψ0 lam i (s82r_hyb x y (insert j s)) =
              fun z => Ψ z - lam * V.q z (y j) := by
            rw [s82r_PhiC_split V ψ0 lam i j hjmem, hc2]
            funext w
            simp only [hΨ, Function.update_self]
            congr 3
            refine Finset.sum_congr rfl fun l hl => ?_
            rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]
          obtain ⟨b1, b2, b3, b4⟩ := s82r_phiC_budget V hψ hlam hP i c1
          obtain ⟨b1', b2', b3', b4'⟩ := s82r_phiC_budget V hψ hlam hP i (s82r_hyb x y (insert j s))
          rw [hΦ1] at b3 b4
          rw [hΦ2] at b3' b4'
          have hq : ∀ w : E, Measurable (fun z => V.q z w) := fun w =>
            V.measurable_q.comp (measurable_id.prodMk measurable_const)
          have hΨm : Measurable Ψ := hψ.measurable.sub
            ((Finset.measurable_sum _ fun l _ => hq (c1 l)).const_mul lam)
          have hΨM : ∀ z, Ψ z ≤ M := fun z => by
            have := mul_nonneg hlam (Finset.sum_nonneg fun l (_ : l ∈ (Finset.univ.erase i).erase j) =>
              V.q_nonneg z (c1 l))
            have := hψ.le z
            simp only [hΨ]; linarith
          have key := s82r_oc_coord V hΨm hΨM hlam (x j) (y j) b3 b3' b4 b4' z
          have eK : Real.exp ((M₁ + P) + M) = Real.exp (M + (M₁ + P)) := by rw [add_comm]
          have eK2 : Real.exp (M + 2 * (M₁ + P) + M) = Real.exp (M + (M₁ + P)) ^ 2 := by
            rw [sq, ← Real.exp_add]; ring_nf
          rw [eK, eK2] at key
          rw [hΦ1, hΦ2]
          refine key.trans (le_of_eq ?_)
          ring
      linarith [h1, h2]

end HRS.MS.S82R

end
