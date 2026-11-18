import HRS.MC.CepH5C1

/-!
# Packet C: `h5Comp_iUnion` (continuation of `CepH5C1.lean`)
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepH5Pf

open HRS

section Components

variable {N : ℕ} [NeZero N]

/-- Every point of the circle has a representative in any window `[c, c+1)`. -/
lemma h5c_exists_rep (a : UnitAddCircle) (c : ℝ) : ∃ v ∈ Set.Ico c (c + 1), (v : UnitAddCircle) = a := by
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective a
  refine ⟨toIcoMod one_pos c t, by simpa using toIcoMod_mem_Ico one_pos c t, ?_⟩
  have h := self_sub_toIcoMod one_pos c t
  have h2 : ((t - toIcoMod one_pos c t : ℝ) : UnitAddCircle) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]; exact ⟨toIcoDiv one_pos c t, by simpa using h.symm⟩
  rw [AddCircle.coe_sub, sub_eq_zero] at h2
  exact h2.symm

lemma h5c_subset (σ : Equiv.Perm (Fin N)) : h5Comp σ ⊆ (collisionSet 1 N)ᶜ := by
  rintro x ⟨y, rfl, hy⟩ ⟨i, j, hij, hEq⟩
  obtain ⟨n, hn⟩ := h5c_mk_eq (x := y i) (y := y j) hEq
  obtain ⟨k, rfl⟩ := σ.surjective i
  obtain ⟨k', rfl⟩ := σ.surjective j
  have h1 := hy.2 k k'
  have h2 := hy.2 k' k
  have h3 : (n : ℝ) < 1 := by linarith
  have h4 : (-1 : ℝ) < n := by linarith
  have h3' : n < 1 := by exact_mod_cast h3
  have h4' : -1 < n := by exact_mod_cast h4
  have : n = 0 := by omega
  subst this
  have hh : y (σ k) 0 = y (σ k') 0 := by simpa [sub_eq_zero] using hn
  exact hij (h5c_lift_inj hy hh)

lemma h5c_supset (x : Config 1 N) (hx : x ∉ collisionSet 1 N) : ∃ σ : h5Idx N, x ∈ h5Comp σ.1 := by
  have hinj : ∀ i j, x i 0 = x j 0 → i = j := by
    intro i j h
    by_contra hne
    refine hx ⟨i, j, hne, ?_⟩
    funext l
    have : l = 0 := Subsingleton.elim _ _
    subst this; exact h
  obtain ⟨c, hc⟩ := QuotientAddGroup.mk_surjective (x 0 0)
  have hex : ∀ i, ∃ v ∈ Set.Ico c (c + 1), (v : UnitAddCircle) = x i 0 := fun i => h5c_exists_rep _ c
  choose v hvmem hvcoe using hex
  have hv0 : v 0 = c := by
    have hc' : c ∈ Set.Ico c (c + 1) := ⟨le_rfl, by linarith⟩
    exact (AddCircle.coe_eq_coe_iff_of_mem_Ico (hvmem 0) hc').1 (by rw [hvcoe 0]; exact hc.symm)
  have hvinj : Function.Injective v := by
    intro i j h
    exact hinj i j (by rw [← hvcoe i, ← hvcoe j, h])
  set τ : Equiv.Perm (Fin N) := Tuple.sort v with hτ
  have hmono : Monotone (v ∘ τ) := Tuple.monotone_sort v
  have hτ0 : τ 0 = 0 := by
    have h1 : v (τ 0) ≤ v 0 := by
      have := hmono (Fin.zero_le (τ.symm 0))
      simpa using this
    have h2 : c ≤ v (τ 0) := (hvmem _).1
    exact hvinj (le_antisymm h1 (by rw [hv0]; exact h2))
  refine ⟨⟨τ, hτ0⟩, fun i => (WithLp.toLp 2 fun _ => v i : Euc 1), ?_, ?_, ?_⟩
  · funext i l
    have : l = 0 := Subsingleton.elim _ _
    subst this
    exact hvcoe i
  · intro k k' hkk'
    show v (τ k) < v (τ k')
    exact lt_of_le_of_ne (hmono hkk'.le) (fun h => (ne_of_lt hkk') (τ.injective (hvinj h)))
  · intro k k'
    show v (τ k') < v (τ k) + 1
    have := (hvmem (τ k')).2
    have := (hvmem (τ k)).1
    linarith

theorem h5Comp_iUnion_proof : (⋃ σ : h5Idx N, h5Comp σ.1) = (collisionSet 1 N)ᶜ := by
  ext x
  simp only [mem_iUnion]
  constructor
  · rintro ⟨σ, hσ⟩; exact h5c_subset σ.1 hσ
  · intro hx; exact h5c_supset x hx

end Components

end HRS.MC.CepH5Pf
