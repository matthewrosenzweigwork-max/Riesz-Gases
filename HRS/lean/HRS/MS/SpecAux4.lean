import Mathlib

/-!
# S8P: monotone enumeration by `ℕ` of a countable infinite type with finite sublevel sets

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  `s8p_enum_monotone`: `f : ι → ℝ` with `{i | f i ≤ c}` finite for every `c`
(`ι` countable and infinite) gives `σ : ℕ ≃ ι` with `f ∘ σ` monotone.  Used to turn the Hilbert basis of eigenvectors of
`SpecAux3` (eigenvalues `1/lam i`) into the sequence `(e_ℓ, ω_ℓ)` of S8.7.
-/

noncomputable section

open Filter

namespace HRS.MS.Spec

theorem s8p_enum_monotone {ι : Type*} [Countable ι] [Infinite ι] (f : ι → ℝ)
    (hf : ∀ c : ℝ, {i | f i ≤ c}.Finite) : ∃ σ : ℕ ≃ ι, Monotone (f ∘ σ) := by
  classical
  obtain ⟨enc, henc⟩ : ∃ enc : ι → ℕ, Function.Injective enc := Countable.exists_injective_nat ι
  let lt : ι → ι → Prop := fun i j => f i < f j ∨ (f i = f j ∧ enc i < enc j)
  have lt_trans : ∀ {i j k}, lt i j → lt j k → lt i k := by
    intro i j k hij hjk
    rcases hij with h1 | ⟨h1, h2⟩ <;> rcases hjk with h3 | ⟨h3, h4⟩
    · exact Or.inl (h1.trans h3)
    · exact Or.inl (h3 ▸ h1)
    · exact Or.inl (h1 ▸ h3)
    · exact Or.inr ⟨h1.trans h3, h2.trans h4⟩
  have lt_irrefl : ∀ i, ¬ lt i i := by
    intro i h; rcases h with h | ⟨-, h⟩ <;> exact lt_irrefl _ h
  have lt_total : ∀ i j, i ≠ j → lt i j ∨ lt j i := by
    intro i j hij
    rcases lt_trichotomy (f i) (f j) with h | h | h
    · exact Or.inl (Or.inl h)
    · rcases lt_trichotomy (enc i) (enc j) with h' | h' | h'
      · exact Or.inl (Or.inr ⟨h, h'⟩)
      · exact absurd (henc h') hij
      · exact Or.inr (Or.inr ⟨h.symm, h'⟩)
    · exact Or.inr (Or.inl h)
  have hP : ∀ i, {j | lt j i}.Finite := fun i =>
    (hf (f i)).subset fun j hj => by
      rcases hj with h | ⟨h, -⟩
      · exact h.le
      · exact h.le
  let r : ι → ℕ := fun i => (hP i).toFinset.card
  have r_lt : ∀ {i j}, lt i j → r i < r j := by
    intro i j hij
    refine Finset.card_lt_card (Finset.ssubset_iff_of_subset ?_ |>.2 ⟨i, ?_, ?_⟩)
    · intro k hk
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hk ⊢
      exact lt_trans hk hij
    · simpa using hij
    · simpa using lt_irrefl i
  have r_inj : Function.Injective r := by
    intro i j h
    by_contra hij
    rcases lt_total i j hij with h1 | h1
    · exact (r_lt h1).ne h
    · exact (r_lt h1).ne h.symm
  have r_le : ∀ {i j}, r i ≤ r j → f i ≤ f j := by
    intro i j h
    by_contra hlt
    push Not at hlt
    have : lt j i := Or.inl hlt
    exact absurd (r_lt this) (not_lt.2 h)
  have down : ∀ i, ∀ m < r i, ∃ j, r j = m := by
    intro i m hm
    have hsub : (hP i).toFinset.image r ⊆ Finset.range (r i) := by
      intro n hn
      simp only [Finset.mem_image, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hn
      obtain ⟨j, hj, rfl⟩ := hn
      exact Finset.mem_range.2 (r_lt hj)
    have hcard : (Finset.range (r i)).card ≤ ((hP i).toFinset.image r).card := by
      rw [Finset.card_image_of_injective _ r_inj, Finset.card_range]
    have heq := Finset.eq_of_subset_of_card_le hsub hcard
    have : m ∈ (hP i).toFinset.image r := by rw [heq]; exact Finset.mem_range.2 hm
    obtain ⟨j, -, hj⟩ := Finset.mem_image.1 this
    exact ⟨j, hj⟩
  have r_surj : Function.Surjective r := by
    intro n
    have hinfr : (Set.range r).Infinite := Set.infinite_range_of_injective r_inj
    obtain ⟨_, ⟨i, rfl⟩, hi⟩ := hinfr.exists_gt n
    exact down i n hi
  let σ : ℕ ≃ ι := (Equiv.ofBijective r ⟨r_inj, r_surj⟩).symm
  have h1 : ∀ m, r (σ m) = m := fun m => (Equiv.ofBijective r ⟨r_inj, r_surj⟩).apply_symm_apply m
  refine ⟨σ, fun m n hmn => r_le ?_⟩
  rw [h1, h1]; exact hmn

end HRS.MS.Spec
