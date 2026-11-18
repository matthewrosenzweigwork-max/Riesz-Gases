import HRS.MS.S82RM13

/-!
# S8.2 R02 (S82R), M14: the dual comparison theorem
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Function
open scoped ENNReal BigOperators Classical

namespace HRS.MS.S82R
open HRS.External

variable {E : Type*} [MeasurableSpace E] {n : ℕ}

theorem s82r_dual_bound [NeZero n] {μ : Measure E} [IsProbabilityMeasure μ] {S S' : Spec E n}
    {κ κ' : Fin n → (Fin n → E) → E → ℝ} {Γ : E → E → ℝ} {b : E → ℝ}
    (hS : s82r_Dens μ S κ) (hS' : s82r_Dens μ S' κ') (hH : s82r_Hyp μ Γ b κ κ')
    (hsym : ∀ z u, Γ z u = Γ u z) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : ∀ u, ∫ z, Γ z u ∂μ ≤ θ)
    (hθ1 : ((n : ℝ) - 1) * θ < 1) {ρ : E → ℝ} (hρ : Measurable ρ) (hρ0 : ∀ z, 0 ≤ ρ z)
    (hρi : Integrable ρ μ)
    (hsup : ∀ᵐ z ∂μ, (1 - 1 / (n : ℝ)) * ρ z + (((n : ℝ) - 1) / n) * s82r_Gam μ Γ ρ z ≤
      ρ z - (1 / (n : ℝ)) * b z)
    (i0 : Fin n) {A : Set E} (hA : MeasurableSet A) :
    ∫ x, A.indicator (fun _ => (1 : ℝ)) (x i0) ∂S.P -
        ∫ x, A.indicator (fun _ => (1 : ℝ)) (x i0) ∂S'.P ≤ ∫ z in A, ρ z ∂μ := by
  obtain ⟨G0, hG0⟩ := hH.Γb
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  set f : (Fin n → E) → ℝ := fun x => A.indicator (fun _ => (1 : ℝ)) (x i0) with hf
  have hfm : Measurable f := (measurable_const.indicator hA).comp (measurable_pi_apply i0)
  have hfb : ∀ x, |f x| ≤ 1 := by
    intro x; simp only [hf]; by_cases hx : x i0 ∈ A <;> simp [Set.indicator, hx]
  have hW0 := s82r_W0_ok i0 hA
  have hwok := fun J => s82r_wseq_ok hH.Γm hH.Γ0 hθ hG0 hW0 J
  -- initial Lipschitz bound
  have hFF0 : ∀ x y, f x - f y ≤ s82r_cost (s82r_W0 i0 A) x y := by
    intro x y
    have hnn : ∀ ℓ ∈ Finset.univ, 0 ≤ (if x ℓ = y ℓ then (0 : ℝ) else
        s82r_W0 i0 A ℓ (x ℓ) + s82r_W0 i0 A ℓ (y ℓ)) := fun ℓ _ => by
      split_ifs
      · exact le_rfl
      · exact add_nonneg (hW0.nonneg ℓ _) (hW0.nonneg ℓ _)
    have := Finset.single_le_sum hnn (Finset.mem_univ i0)
    refine le_trans ?_ this
    by_cases h : x i0 = y i0
    · simp only [hf, h]; simp
    · simp only [hf, h, if_false, s82r_W0, if_true]
      by_cases hx : x i0 ∈ A <;> by_cases hy : y i0 ∈ A <;> simp [Set.indicator, hx, hy]
  -- transfer along the iteration
  have Cl : ∀ J : ℕ, ∀ x y, (S.scan^[J] f) x - (S'.scan^[J] f) y ≤
      s82r_cost (s82r_wseq μ Γ n (s82r_W0 i0 A) J) x y +
        ∑ m ∈ Finset.range J, (1 / (n : ℝ)) * ∑ i, ∫ z, s82r_wseq μ Γ n (s82r_W0 i0 A) m i z * b z ∂μ := by
    intro J
    induction J with
    | zero => intro x y; simpa [s82r_wseq_zero] using hFF0 x y
    | succ J ih =>
        intro x y
        obtain ⟨h1, h2, -⟩ := s82r_iter_scan S hfm hfb J
        obtain ⟨h1', h2', -⟩ := s82r_iter_scan S' hfm hfb J
        have step := s82r_scan_step hS hS' hH (hwok J) h1 h1' h2 h2' ih x y
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', s82r_wseq_succ,
          Finset.sum_range_succ]
        linarith
  -- supersolution pairing
  have Pq : ∀ J : ℕ, ∑ m ∈ Finset.range J, (1 / (n : ℝ)) *
      ∑ i, ∫ z, s82r_wseq μ Γ n (s82r_W0 i0 A) m i z * b z ∂μ +
      ∑ i, ∫ z, s82r_wseq μ Γ n (s82r_W0 i0 A) J i z * ρ z ∂μ ≤
      ∑ i, ∫ z, s82r_W0 i0 A i z * ρ z ∂μ := by
    intro J
    obtain ⟨Bb, hBb⟩ := hH.bb
    induction J with
    | zero => simp [s82r_wseq_zero]
    | succ J ih =>
        have step := s82r_super_step hH.Γm hH.Γ0 hG0 hsym hH.bm hH.b0 hBb (hwok J) hρ hρ0 hρi hsup
        rw [Finset.sum_range_succ, s82r_wseq_succ]
        linarith
  have hPnn : ∀ J : ℕ, 0 ≤ ∑ i, ∫ z, s82r_wseq μ Γ n (s82r_W0 i0 A) J i z * ρ z ∂μ := fun J =>
    Finset.sum_nonneg fun i _ => integral_nonneg fun z => mul_nonneg ((hwok J).nonneg i z) (hρ0 z)
  have hP0 : ∑ i, ∫ z, s82r_W0 i0 A i z * ρ z ∂μ = ∫ z in A, ρ z ∂μ := by
    rw [Finset.sum_eq_single i0]
    · simp only [s82r_W0, if_true]
      rw [← integral_indicator hA]
      refine integral_congr_ae (ae_of_all _ fun z => ?_)
      by_cases hz : z ∈ A <;> simp [Set.indicator, hz]
    · intro i _ hi
      simp [s82r_W0, hi]
    · intro h; exact absurd (Finset.mem_univ i0) h
  have hk : ∀ J : ℕ, ∑ m ∈ Finset.range J, (1 / (n : ℝ)) *
      ∑ i, ∫ z, s82r_wseq μ Γ n (s82r_W0 i0 A) m i z * b z ∂μ ≤ ∫ z in A, ρ z ∂μ := by
    intro J
    have := Pq J
    have := hPnn J
    linarith
  -- decay
  set r : ℝ := 1 - 1 / (n : ℝ) + (((n : ℝ) - 1) / n) * θ with hr
  have hr0 : 0 ≤ r := by
    have : 0 ≤ 1 - 1 / (n : ℝ) := by rw [sub_nonneg, div_le_one (by linarith)]; exact hn1
    have h3 : 0 ≤ ((n : ℝ) - 1) / n * θ := mul_nonneg (div_nonneg (by linarith) (by linarith)) hθ0
    rw [hr]; linarith
  have hr1 : r < 1 := by
    rw [hr]
    have hn0 : (0 : ℝ) < n := by linarith
    have : ((n : ℝ) - 1) / n * θ < 1 / n := by
      rw [div_mul_eq_mul_div, div_lt_div_iff_of_pos_right hn0]; exact hθ1
    linarith
  set B0 : Fin n → ℝ := fun ℓ => if ℓ = i0 then 1 else 0 with hB0
  have hB00 : ∀ ℓ, 0 ≤ B0 ℓ := fun ℓ => by simp only [hB0]; split_ifs <;> norm_num
  have hB0le : ∀ ℓ z, s82r_W0 i0 A ℓ z ≤ B0 ℓ := fun ℓ z => by
    simp only [hB0, s82r_W0]
    split_ifs
    · by_cases hz : z ∈ A <;> simp [Set.indicator, hz]
    · exact le_rfl
  have hB0sum : ∑ ℓ, B0 ℓ = 1 := by simp [hB0]
  have hdec : ∀ J : ℕ, ∃ B' : Fin n → ℝ, (∀ ℓ, 0 ≤ B' ℓ) ∧
      (∀ ℓ z, s82r_wseq μ Γ n (s82r_W0 i0 A) J ℓ z ≤ B' ℓ) ∧ ∑ ℓ, B' ℓ ≤ r ^ J := by
    intro J
    obtain ⟨B', h0, h1, h2⟩ := s82r_wseq_decay hH.Γm hH.Γ0 hθ0 hθ hG0 hW0 hB00 hB0le J
    exact ⟨B', h0, h1, by rw [hB0sum, mul_one] at h2; exact h2⟩
  -- final estimate for every J
  have hmain : ∀ J : ℕ, ∫ x, f x ∂S.P - ∫ x, f x ∂S'.P ≤ 2 * r ^ J + ∫ z in A, ρ z ∂μ := by
    intro J
    obtain ⟨B', hB'0, hB', hBs⟩ := hdec J
    obtain ⟨h1, h2, h3⟩ := s82r_iter_scan S hfm hfb J
    obtain ⟨h1', h2', h3'⟩ := s82r_iter_scan S' hfm hfb J
    have hcost : ∀ x y, s82r_cost (s82r_wseq μ Γ n (s82r_W0 i0 A) J) x y ≤ 2 * r ^ J := by
      intro x y
      have : s82r_cost (s82r_wseq μ Γ n (s82r_W0 i0 A) J) x y ≤ ∑ ℓ, (B' ℓ + B' ℓ) := by
        unfold s82r_cost
        refine Finset.sum_le_sum fun ℓ _ => ?_
        split_ifs
        · exact add_nonneg (hB'0 ℓ) (hB'0 ℓ)
        · exact add_le_add (hB' ℓ _) (hB' ℓ _)
      refine this.trans ?_
      have e : ∑ ℓ, (B' ℓ + B' ℓ) = 2 * ∑ ℓ, B' ℓ := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun ℓ _ => by ring
      rw [e]; linarith
    set c : ℝ := 2 * r ^ J + ∫ z in A, ρ z ∂μ with hc
    have hxy : ∀ x y, (S.scan^[J] f) x - (S'.scan^[J] f) y ≤ c := fun x y =>
      (Cl J x y).trans (add_le_add (hcost x y) (hk J))
    have hint : ∀ g : (Fin n → E) → ℝ, Measurable g → (∀ x, |g x| ≤ 1) → ∀ P : Measure (Fin n → E),
        IsProbabilityMeasure P → Integrable g P := fun g hg hb P _ =>
      Integrable.of_bound hg.aestronglyMeasurable 1 (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs]; exact hb x)
    have hiS := hint _ h1 h2 S.P inferInstance
    have hiS' := hint _ h1' h2' S'.P inferInstance
    rw [← h3, ← h3']
    have hy : ∀ y, ∫ x, (S.scan^[J] f) x ∂S.P - (S'.scan^[J] f) y ≤ c := by
      intro y
      have : ∫ x, (S.scan^[J] f) x ∂S.P ≤ ∫ x, (c + (S'.scan^[J] f) y) ∂S.P :=
        integral_mono hiS (integrable_const _) fun x => by linarith [hxy x y]
      simp at this
      linarith
    have : ∫ x, (S.scan^[J] f) x ∂S.P - ∫ y, (S'.scan^[J] f) y ∂S'.P =
        ∫ y, (∫ x, (S.scan^[J] f) x ∂S.P - (S'.scan^[J] f) y) ∂S'.P := by
      rw [integral_sub (integrable_const _) hiS']; simp
    rw [this]
    calc ∫ y, (∫ x, (S.scan^[J] f) x ∂S.P - (S'.scan^[J] f) y) ∂S'.P ≤ ∫ y, c ∂S'.P :=
          integral_mono ((integrable_const _).sub hiS') (integrable_const _) hy
      _ = c := by simp
  -- let J → ∞
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have ht : Tendsto (fun J : ℕ => 2 * r ^ J) atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_mul 2
  obtain ⟨J, hJ⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  have := hmain J
  linarith

end HRS.MS.S82R

end
