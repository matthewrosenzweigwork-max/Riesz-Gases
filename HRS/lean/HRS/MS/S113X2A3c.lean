import HRS.MS.S113X2A3b

/-!
# S11.3 X2 part A3c: the exhaustion domains and the removal of the localization (`L¹` convergence of the ratios)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S113X2

open HRS HRS.Whole

variable {d N : ℕ}

theorem s113a_domain_isOpen (d N k : ℕ) : IsOpen (s113a_domain d N k) := by
  unfold s113a_domain
  have h1 : IsOpen {x : EucConfig d N | ∀ i j, i ≠ j → 1 / ((k : ℝ) + 1) < ‖x i - x j‖} := by
    have : {x : EucConfig d N | ∀ i j, i ≠ j → 1 / ((k : ℝ) + 1) < ‖x i - x j‖} =
        ⋂ i : Fin N, ⋂ j : Fin N, ⋂ (_ : i ≠ j), {x : EucConfig d N | 1 / ((k : ℝ) + 1) < ‖x i - x j‖} := by
      ext x; simp
    rw [this]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => isOpen_iInter_of_finite fun _ =>
      isOpen_lt continuous_const (((continuous_apply i).sub (continuous_apply j)).norm)
  have h2 : IsOpen {x : EucConfig d N | ∀ i, ‖x i‖ < (k : ℝ) + 1} := by
    have : {x : EucConfig d N | ∀ i, ‖x i‖ < (k : ℝ) + 1} = ⋂ i : Fin N, {x : EucConfig d N | ‖x i‖ < (k : ℝ) + 1} := by
      ext x; simp
    rw [this]
    exact isOpen_iInter_of_finite fun i => isOpen_lt ((continuous_apply i).norm) continuous_const
  exact h1.inter h2

theorem s113a_domain_mono (d N : ℕ) : Monotone (s113a_domain d N) := by
  intro a b hab x hx
  refine ⟨fun i j hij => lt_of_le_of_lt ?_ (hx.1 i j hij), fun i => lt_of_lt_of_le (hx.2 i) ?_⟩
  · exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hab 1)
  · have : (a : ℝ) ≤ b := by exact_mod_cast hab
    linarith

theorem s113a_domain_subset_free (d N k : ℕ) : s113a_domain d N k ⊆ (eucCollisionSet d N)ᶜ := by
  rintro x hx ⟨i, j, hij, h⟩
  have := hx.1 i j hij
  rw [h, sub_self, norm_zero] at this
  have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
  linarith

theorem s113a_domain_iUnion (d N : ℕ) : (⋃ k, s113a_domain d N k) = (eucCollisionSet d N)ᶜ := by
  refine Set.Subset.antisymm (Set.iUnion_subset fun k => s113a_domain_subset_free d N k) fun x hx => ?_
  have hsep : ∀ i j, i ≠ j → 0 < ‖x i - x j‖ := fun i j hij =>
    norm_pos_iff.2 (sub_ne_zero.2 fun h => hx ⟨i, j, hij, h⟩)
  -- a common lower bound for the separations, and an upper bound for the norms
  obtain ⟨δ, hδ0, hδ⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ i j, i ≠ j → δ < ‖x i - x j‖ := by
    classical
    by_cases hN : (Finset.univ.offDiag : Finset (Fin N × Fin N)).Nonempty
    · obtain ⟨p, hp, hmin⟩ := Finset.exists_min_image Finset.univ.offDiag (fun p => ‖x p.1 - x p.2‖) hN
      have hp' : p.1 ≠ p.2 := (Finset.mem_offDiag.1 hp).2.2
      refine ⟨‖x p.1 - x p.2‖ / 2, by have := hsep _ _ hp'; positivity, fun i j hij => ?_⟩
      have := hmin (i, j) (Finset.mem_offDiag.2 ⟨Finset.mem_univ _, Finset.mem_univ _, hij⟩)
      have := hsep _ _ hp'
      linarith
    · refine ⟨1, one_pos, fun i j hij => ?_⟩
      exact absurd ⟨(i, j), Finset.mem_offDiag.2 ⟨Finset.mem_univ _, Finset.mem_univ _, hij⟩⟩ hN
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ i, ‖x i‖ < R := by
    refine ⟨(∑ i, ‖x i‖) + 1, fun i => ?_⟩
    have := Finset.single_le_sum (f := fun i => ‖x i‖) (fun j _ => norm_nonneg (x j)) (Finset.mem_univ i)
    linarith
  obtain ⟨k1, hk1⟩ := exists_nat_gt (1 / δ)
  obtain ⟨k2, hk2⟩ := exists_nat_gt R
  refine Set.mem_iUnion.2 ⟨max k1 k2, fun i j hij => ?_, fun i => ?_⟩
  · calc 1 / (((max k1 k2 : ℕ) : ℝ) + 1) ≤ δ := by
          rw [div_le_iff₀ (by positivity)]
          have h1 : 1 / δ < ((max k1 k2 : ℕ) : ℝ) + 1 := by
            have : (k1 : ℝ) ≤ ((max k1 k2 : ℕ) : ℝ) := by exact_mod_cast le_max_left _ _
            linarith
          rw [div_lt_iff₀ hδ0] at h1
          nlinarith
      _ < ‖x i - x j‖ := hδ i j hij
  · have : (k2 : ℝ) ≤ ((max k1 k2 : ℕ) : ℝ) := by exact_mod_cast le_max_right _ _
    linarith [hR i]

/-- The closed, bounded, separated configurations containing `s113a_domain d N k`. -/
theorem s113a_domain_closure_subset (d N k : ℕ) : closure (s113a_domain d N k) ⊆
    {x : EucConfig d N | (∀ i j, i ≠ j → 1 / ((k : ℝ) + 1) ≤ ‖x i - x j‖) ∧ ∀ i, ‖x i‖ ≤ (k : ℝ) + 1} := by
  have hA : IsClosed {x : EucConfig d N | ∀ i j, i ≠ j → 1 / ((k : ℝ) + 1) ≤ ‖x i - x j‖} := by
    have : {x : EucConfig d N | ∀ i j, i ≠ j → 1 / ((k : ℝ) + 1) ≤ ‖x i - x j‖} =
        ⋂ i : Fin N, ⋂ j : Fin N, ⋂ (_ : i ≠ j), {x : EucConfig d N | 1 / ((k : ℝ) + 1) ≤ ‖x i - x j‖} := by
      ext x; simp
    rw [this]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_le continuous_const (((continuous_apply i).sub (continuous_apply j)).norm)
  have hB : IsClosed {x : EucConfig d N | ∀ i, ‖x i‖ ≤ (k : ℝ) + 1} := by
    have : {x : EucConfig d N | ∀ i, ‖x i‖ ≤ (k : ℝ) + 1} =
        ⋂ i : Fin N, {x : EucConfig d N | ‖x i‖ ≤ (k : ℝ) + 1} := by
      ext x; simp
    rw [this]
    exact isClosed_iInter fun i => isClosed_le ((continuous_apply i).norm) continuous_const
  have hcl : IsClosed {x : EucConfig d N | (∀ i j, i ≠ j → 1 / ((k : ℝ) + 1) ≤ ‖x i - x j‖) ∧
      ∀ i, ‖x i‖ ≤ (k : ℝ) + 1} := hA.inter hB
  refine closure_minimal (fun x hx => ⟨fun i j hij => (hx.1 i j hij).le, fun i => (hx.2 i).le⟩) hcl

theorem s113a_domain_closure_compact (d N k : ℕ) : IsCompact (closure (s113a_domain d N k)) := by
  refine Metric.isCompact_of_isClosed_isBounded isClosed_closure ?_
  refine (Metric.isBounded_closedBall (x := (0 : EucConfig d N)) (r := (k : ℝ) + 1)).subset ?_
  intro x hx
  have := (s113a_domain_closure_subset d N k hx).2
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by positivity)]
  exact this

theorem s113a_domain_closure_subset_free (d N k : ℕ) : closure (s113a_domain d N k) ⊆ (eucCollisionSet d N)ᶜ := by
  intro x hx ⟨i, j, hij, h⟩
  have := (s113a_domain_closure_subset d N k hx).1 i j hij
  rw [h, sub_self, norm_zero] at this
  have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
  linarith

end HRS.MS.S113X2

end
