import HRS.MS.S82P2Grad3

/-!
# S8.2 (S82T): a.e. non-collision under the physical canonical law, and transfer of pair statistics
`canonicalP <= C0 * unpinnedReference` and the reference law has a.s. no collisions (`s82p2_noncollision`), so a pair
sum with an off-diagonal kernel identity `F = F'` (for `x != y`) is a.e. equal under `canonicalP`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82T
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82P2

/-- Almost surely under `canonicalP` all particles are at distinct points. -/
theorem s82t_ae_noncollision {d : ℕ} (hd : 2 ≤ d) {a beta C0 : ℝ} {rho : Euc d → ℝ} {q : Euc d → ℝ}
    {h : ℕ → Euc d → ℝ} [IsProbabilityMeasure (HRS.Whole.withDensityReal rho)]
    (hW : WeakReferenceSetup d a beta rho q h C0) {N : ℕ} (hN : 2 ≤ N) :
    ∀ᵐ X ∂canonicalP d N a beta, ∀ i j : Fin N, i ≠ j → X i ≠ X j := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  have hm : 1 ≤ m := by omega
  have hdom := hW.domination (m + 1) hN
  have hac : canonicalP d (m + 1) a beta ≪ unpinnedReference q h
      (HRS.Whole.withDensityReal rho) beta (m + 1) :=
    Measure.absolutelyContinuous_of_le_smul hdom
  have hall : ∀ i : Fin (m + 1), ∀ᵐ X ∂unpinnedReference q h (HRS.Whole.withDensityReal rho) beta (m + 1),
      ∀ j : Fin (m + 1), i ≠ j → X i ≠ X j := by
    intro i
    have h0 := s82p2_noncollision hd hW hm i
    rw [ae_iff]
    have : {X : EucConfig d (m + 1) | ¬∀ j : Fin (m + 1), i ≠ j → X i ≠ X j} ⊆
        {X | ∃ j, j ≠ i ∧ X j = X i} := by
      intro X hX
      simp only [Set.mem_setOf_eq, not_forall, not_not] at hX
      obtain ⟨j, hij, hXe⟩ := hX
      exact ⟨j, hij.symm, hXe.symm⟩
    exact measure_mono_null this h0
  have hall' := ae_all_iff.2 hall
  exact hac.ae_le (by filter_upwards [hall'] with X hX i j hij using hX i j hij)

lemma s82t_pairSum_congr {d N : ℕ} {F F' : Euc d → Euc d → ℝ} {X : EucConfig d N}
    (hX : ∀ i j : Fin N, i ≠ j → X i ≠ X j) (hF : ∀ x y, x ≠ y → F x y = F' x y) :
    Phase2S82.pairSum F X = Phase2S82.pairSum F' X := by
  unfold Phase2S82.pairSum
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
  exact hF _ _ (hX i j (Finset.ne_of_mem_erase hj).symm)

end HRS.MS.S82T
