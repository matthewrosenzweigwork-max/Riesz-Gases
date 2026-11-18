import HRS.MC.CepH5L2a
import HRS.MC.CepH5C3
import HRS.Stochastic.SelectedFlow

/-!
# Packet C, L2 (`h5_class_constancy`), part b: the almost sure statement
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepH5Pf

open HRS

section Flow

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {N : ℕ} [NeZero N]

/-- A weakly cyclically ordered lift of a collision-free configuration is strictly ordered. -/
lemma h5c_weak_to_strict {π : Equiv.Perm (Fin N)} {Z : Fin N → Euc 1} (hZ : CyclicallyOrdered π Z)
    (hx : (fun i => Torus.mk (Z i)) ∉ collisionSet 1 N) : cep_StrictlyOrdered π Z := by
  obtain ⟨h1, h2⟩ := hZ 0
  have hcoll : ∀ i j, i ≠ j → ∀ n : ℤ, Z i 0 - Z j 0 = n → False := by
    intro i j hij n hn
    refine hx ⟨i, j, hij, ?_⟩
    funext l
    have : l = 0 := Subsingleton.elim _ _
    subst this
    exact h5c_coe_of_int hn
  refine ⟨fun k k' hkk' => ?_, fun k k' => ?_⟩
  · refine lt_of_le_of_ne (h1 k k' hkk'.le) fun h => ?_
    exact hcoll (π k) (π k') (fun h' => (ne_of_lt hkk') (π.injective h')) 0 (by simp [h])
  · refine lt_of_le_of_ne (h2 k k') fun h => ?_
    by_cases hk : π k' = π k
    · rw [hk] at h; linarith
    · exact hcoll (π k') (π k) hk 1 (by simp [h])

theorem h5_class_constancy_proof {D : DynData 1} {T : ℝ} {X₀ : Ω → Config 1 N}
    {W : ℝ≥0 → Ω → (Fin N → Euc 1)} {X : ℝ≥0 → Ω → Config 1 N}
    (hX : IsCepaLepingleFlow P D T X₀ W X) :
    ∀ᵐ ω ∂P, ∀ σ : h5Idx N, X₀ ω ∈ h5Comp σ.1 → ∀ t : ℝ≥0, (t : ℝ) ≤ T →
      X t ω ∉ collisionSet 1 N → X t ω ∈ h5Comp σ.1 := by
  obtain ⟨π, _, hπ⟩ := hX.ordered
  filter_upwards [hπ, hX.toContact.init] with ω hω hinit
  obtain ⟨Y, hXY, _, hYo⟩ := hω
  intro σ h0 t ht hcol
  have hT : (0 : ℝ) ≤ T := le_trans (NNReal.coe_nonneg t) ht
  have hT0 : ((0 : ℝ≥0) : ℝ) ≤ T := by simpa using hT
  have hx0 : X₀ ω = fun i => Torus.mk (Y 0 i) := by rw [← hinit]; exact hXY 0 hT0
  have hc0 : (fun i => Torus.mk (Y 0 i)) ∉ collisionSet 1 N := by
    rw [← hx0]; exact h5c_subset σ.1 h0
  have hZ0 := h5c_weak_to_strict (hYo 0 hT0) hc0
  have hZt := h5c_weak_to_strict (hYo t ht) (by rw [← hXY t ht]; exact hcol)
  obtain ⟨y, hy, hyo⟩ := h0
  obtain ⟨y', h1, h2⟩ := h5c_core σ.2 hyo hZ0 hZt (hy.trans hx0)
  rw [hXY t ht]
  exact ⟨y', h1, h2⟩

end Flow

end HRS.MC.CepH5Pf
