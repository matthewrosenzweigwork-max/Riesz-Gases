import HRS.MS.SA16PRiesz6

/-!
# SA16P, part 7: weak closedness of closed subspaces; weak convergence in a closed subspace

Generic facts about a real normed space `E` and a closed subspace `X`, used with `E = L^p(μ;ℝ^ι)` and
`X = WmpSpace d m p`:

* `sa16p_weak_mem`: a weak limit (in `E`) of elements of a closed subspace `X` lies in `X`.
* `sa16p_weak_restrict`: if `u_n ∈ X` converge weakly in `E` to `u₀ ∈ X`, they converge weakly in `X`, i.e. against
  every `ℓ ∈ StrongDual ℝ X` (Hahn-Banach extension).
-/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set Function
open scoped ENNReal NNReal

namespace HRS.Whole.AppendixA.Phase2SA16P

section Weak
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma sa16p_weak_mem (X : Submodule ℝ E) (hX : IsClosed (X : Set E)) {u : ℕ → E} {u₀ : E}
    (hu : ∀ n, u n ∈ X)
    (hw : ∀ ℓ : StrongDual ℝ E, Tendsto (fun n => ℓ (u n)) atTop (𝓝 (ℓ u₀))) : u₀ ∈ X := by
  by_contra hnot
  obtain ⟨f, c, hf1, hf2⟩ := geometric_hahn_banach_closed_point (X.convex) hX hnot
  have h0 : ∀ a ∈ X, f a = 0 := by
    intro a ha
    by_contra hne
    have hc : 0 < c := by
      have := hf1 0 X.zero_mem
      simpa using this
    -- scale `a` so that `f (t a) ≥ c`
    obtain ⟨t, ht⟩ : ∃ t : ℝ, c < t * f a := by
      by_cases hpos : 0 < f a
      · exact ⟨(c + 1) / f a, by rw [div_mul_cancel₀ _ hpos.ne']; linarith⟩
      · have hneg : f a < 0 := lt_of_le_of_ne (not_lt.1 hpos) hne
        exact ⟨(c + 1) / f a, by rw [div_mul_cancel₀ _ hneg.ne]; linarith⟩
    have := hf1 (t • a) (X.smul_mem t ha)
    rw [map_smul, smul_eq_mul] at this
    linarith
  have hlim : Tendsto (fun n => f (u n)) atTop (𝓝 (f u₀)) := hw f
  have : ∀ n, f (u n) = 0 := fun n => h0 _ (hu n)
  simp only [this] at hlim
  have hf0 : f u₀ = 0 := tendsto_nhds_unique tendsto_const_nhds hlim |>.symm
  have hc : 0 < c := by
    have := hf1 0 X.zero_mem
    simpa using this
  linarith

lemma sa16p_weak_restrict (X : Submodule ℝ E) {u : ℕ → E} {u₀ : E} (hu : ∀ n, u n ∈ X)
    (hu₀ : u₀ ∈ X)
    (hw : ∀ ℓ : StrongDual ℝ E, Tendsto (fun n => ℓ (u n)) atTop (𝓝 (ℓ u₀)))
    (ℓ : StrongDual ℝ X) :
    Tendsto (fun n => ℓ ⟨u n, hu n⟩) atTop (𝓝 (ℓ ⟨u₀, hu₀⟩)) := by
  obtain ⟨g, hg, -⟩ := exists_extension_norm_eq X ℓ
  have := hw g
  have e1 : ∀ n, ℓ ⟨u n, hu n⟩ = g (u n) := fun n => (hg ⟨u n, hu n⟩).symm
  have e2 : ℓ ⟨u₀, hu₀⟩ = g u₀ := (hg ⟨u₀, hu₀⟩).symm
  simp only [e1, e2]
  exact this

end Weak

end HRS.Whole.AppendixA.Phase2SA16P
