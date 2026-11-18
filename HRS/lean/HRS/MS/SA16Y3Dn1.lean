import Mathlib

/-!
# S.A.16 (SA16Y3) Dn1: a countable dense family of `C_c^∞` test classes in `L^q(ℝ^d)` (packet P8, iso case, step b3)

`sa16y3_dense_cc`: for `q` with `1 ≤ q < ∞` there is a sequence `Ψ : ℕ → L^q` whose range is dense and each `Ψ k` has a
representative `g` that is smooth with compact support. Used as the family `Ψ_k` of `sa16p_wmp_compact`
(which needs `Dense (Set.range Ψ)` in `L^{p'}`). Built from Mathlib's `MeasureTheory.Lp.dense_hasCompactSupport_contDiff`
and the separability of `L^q` (`Lp.SecondCountableTopology`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R

variable {d : ℕ}

lemma sa16y3_dense_cc (q : ℝ) [hq : Fact (1 ≤ ENNReal.ofReal q)] (hfin : ENNReal.ofReal q ≠ ⊤) :
    ∃ Ψ : ℕ → Lp ℝ (ENNReal.ofReal q) (volume : Measure (EuclideanSpace ℝ (Fin d))),
      Dense (Set.range Ψ) ∧
        ∀ k, ∃ g : EuclideanSpace ℝ (Fin d) → ℝ, Ψ k =ᵐ[volume] g ∧ HasCompactSupport g ∧ ContDiff ℝ ∞ g := by
  set D : Set (Lp ℝ (ENNReal.ofReal q) (volume : Measure (EuclideanSpace ℝ (Fin d)))) :=
    {f | ∃ g : EuclideanSpace ℝ (Fin d) → ℝ, f =ᵐ[volume] g ∧ HasCompactSupport g ∧ ContDiff ℝ ∞ g} with hD
  have hDdense : Dense D := MeasureTheory.Lp.dense_hasCompactSupport_contDiff (μ := (volume : Measure (EuclideanSpace ℝ (Fin d)))) hfin
  haveI : Fact (ENNReal.ofReal q ≠ ⊤) := ⟨hfin⟩
  haveI : SecondCountableTopology (Lp ℝ (ENNReal.ofReal q) (volume : Measure (EuclideanSpace ℝ (Fin d)))) := inferInstance
  haveI : TopologicalSpace.SeparableSpace (Lp ℝ (ENNReal.ofReal q) (volume : Measure (EuclideanSpace ℝ (Fin d)))) := inferInstance
  have hsep : TopologicalSpace.IsSeparable D :=
    TopologicalSpace.IsSeparable.mono (TopologicalSpace.isSeparable_univ_iff.2 inferInstance) (subset_univ _)
  obtain ⟨t, htD, htc, hDt⟩ := hsep.exists_countable_dense_subset
  have hD0 : (0 : Lp ℝ (ENNReal.ofReal q) (volume : Measure (EuclideanSpace ℝ (Fin d)))) ∈ D :=
    ⟨0, Lp.coeFn_zero _ _ _, HasCompactSupport.zero, contDiff_const⟩
  have hne : t.Nonempty := by
    rcases t.eq_empty_or_nonempty with h | h
    · exfalso
      have h2 := hDt hD0
      rw [h, closure_empty] at h2
      exact h2
    · exact h
  obtain ⟨Ψ, hΨ⟩ := htc.exists_eq_range hne
  have hdt : Dense t := fun f => closure_minimal hDt isClosed_closure (hDdense f)
  refine ⟨Ψ, hΨ ▸ hdt, fun k => ?_⟩
  have hmem : Ψ k ∈ t := by rw [hΨ]; exact mem_range_self k
  exact htD hmem

end HRS.Whole.AppendixA.Phase2SA16R
