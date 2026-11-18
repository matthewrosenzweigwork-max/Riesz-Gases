import HRS.Whole.AppendixA
import HRS.MS.SA16PRiesz7

/-!
# SA16P, part 8: weak compactness and weak continuity in the closed jet space `WmpSpace d m p`

`q = p/(p-1)`.  `D` is any dense subset of `L^q(ℝ^d)` (in applications the Schwartz functions, dense by Mathlib).
The `i`-th component pairing is `sa16p_pair p i G ψ = ∫ G_i ψ`.

* `sa16p_wmp_weak`: `G_n, G₀ ∈ WmpSpace` bounded by `B` whose component pairings against `D` converge converge weakly in
  `WmpSpace`: `ℓ G_n → ℓ G₀` for EVERY `ℓ ∈ StrongDual ℝ (WmpSpace d m p)` (the quantifier of `IsWmpWeaklyContinuous`).
* `sa16p_wmp_limit`: a bounded sequence in `WmpSpace` whose component pairings against `D` converge has a weak limit
  `G₀ ∈ WmpSpace` with `‖G₀‖ ≤ card * B`, to which it converges weakly (against every `ℓ ∈ StrongDual`).
-/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set Function
open scoped ENNReal NNReal

namespace HRS.Whole.AppendixA.Phase2SA16P
open HRS HRS.Whole HRS.Whole.AppendixA

section Wmp
variable {d m : ℕ} {p : ℝ} [Fact (2 ≤ p)]

lemma sa16p_one_lt : 1 < p := by
  have : (2 : ℝ) ≤ p := Fact.out
  linarith

lemma sa16p_wmp_closed :
    IsClosed ((WmpSpace d m p : Submodule ℝ (WLp d m p)) : Set (WLp d m p)) := by
  unfold WmpSpace
  exact Submodule.isClosed_topologicalClosure _

instance sa16p_fact_conj : Fact (1 ≤ ENNReal.ofReal (Real.conjExponent p)) :=
  ⟨by
    have h := (Real.HolderConjugate.conjExponent (sa16p_one_lt (p := p))).symm.lt
    simpa using ENNReal.ofReal_le_ofReal h.le⟩

/-- **Weak convergence in `WmpSpace` from pairings against a dense class.** -/
theorem sa16p_wmp_weak
    (D : Set (Lp ℝ (ENNReal.ofReal (Real.conjExponent p)) (volume : Measure (Euc d))))
    (hD : Dense D) {B : ℝ} (G : ℕ → WmpSpace d m p) (G₀ : WmpSpace d m p)
    (hG : ∀ n, ‖G n‖ ≤ B) (hG₀ : ‖G₀‖ ≤ B)
    (hconv : ∀ i : WIndex d m, ∀ ψ ∈ D, Tendsto
      (fun n => sa16p_pair p i ((G n : WmpSpace d m p) : WLp d m p) ψ) atTop
      (𝓝 (sa16p_pair p i ((G₀ : WmpSpace d m p) : WLp d m p) ψ)))
    (ℓ : StrongDual ℝ (WmpSpace d m p)) :
    Tendsto (fun n => ℓ (G n)) atTop (𝓝 (ℓ G₀)) := by
  classical
  have hpq := Real.HolderConjugate.conjExponent (sa16p_one_lt (p := p))
  have hamb : ∀ ℓ' : StrongDual ℝ (WLp d m p),
      Tendsto (fun n => ℓ' ((G n : WmpSpace d m p) : WLp d m p)) atTop
        (𝓝 (ℓ' ((G₀ : WmpSpace d m p) : WLp d m p))) := fun ℓ' =>
    sa16p_weak_of_pairings hpq D hD (B := B) (fun n => ((G n : WmpSpace d m p) : WLp d m p))
      ((G₀ : WmpSpace d m p) : WLp d m p) hG hG₀ hconv ℓ'
  exact sa16p_weak_restrict (WmpSpace d m p) (fun n => (G n).2) G₀.2 hamb ℓ

/-- **Weak limit in `WmpSpace`.** -/
theorem sa16p_wmp_limit
    (D : Set (Lp ℝ (ENNReal.ofReal (Real.conjExponent p)) (volume : Measure (Euc d))))
    (hD : Dense D) {B : ℝ} (G : ℕ → WmpSpace d m p) (hG : ∀ n, ‖G n‖ ≤ B)
    (hconv : ∀ i : WIndex d m, ∀ ψ ∈ D, ∃ c, Tendsto
      (fun n => sa16p_pair p i ((G n : WmpSpace d m p) : WLp d m p) ψ) atTop (𝓝 c)) :
    ∃ G₀ : WmpSpace d m p, ‖G₀‖ ≤ (Fintype.card (WIndex d m) : ℝ) * B ∧
      (∀ i : WIndex d m, ∀ ψ : Lp ℝ (ENNReal.ofReal (Real.conjExponent p)) (volume : Measure (Euc d)),
        Tendsto (fun n => sa16p_pair p i ((G n : WmpSpace d m p) : WLp d m p) ψ) atTop
          (𝓝 (sa16p_pair p i ((G₀ : WmpSpace d m p) : WLp d m p) ψ))) ∧
      ∀ ℓ : StrongDual ℝ (WmpSpace d m p), Tendsto (fun n => ℓ (G n)) atTop (𝓝 (ℓ G₀)) := by
  classical
  have hpq := Real.HolderConjugate.conjExponent (sa16p_one_lt (p := p))
  obtain ⟨u₀, hu₀, hpair⟩ := sa16p_exists_weak_limit hpq D hD (B := B)
    (fun n => ((G n : WmpSpace d m p) : WLp d m p)) hG hconv
  set B' : ℝ := max B ((Fintype.card (WIndex d m) : ℝ) * B) with hB'
  have hamb : ∀ ℓ' : StrongDual ℝ (WLp d m p),
      Tendsto (fun n => ℓ' ((G n : WmpSpace d m p) : WLp d m p)) atTop (𝓝 (ℓ' u₀)) := fun ℓ' =>
    sa16p_weak_of_pairings hpq (Set.univ) dense_univ (B := B') (fun n => ((G n : WmpSpace d m p) : WLp d m p))
      u₀ (fun n => (hG n).trans (le_max_left _ _)) (hu₀.trans (le_max_right _ _))
      (fun i ψ _ => hpair i ψ) ℓ'
  have hmem : u₀ ∈ WmpSpace d m p :=
    sa16p_weak_mem (WmpSpace d m p) sa16p_wmp_closed (fun n => (G n).2) hamb
  refine ⟨⟨u₀, hmem⟩, hu₀, hpair, fun ℓ => ?_⟩
  exact sa16p_weak_restrict (WmpSpace d m p) (fun n => (G n).2) hmem hamb ℓ

end Wmp

end HRS.Whole.AppendixA.Phase2SA16P
