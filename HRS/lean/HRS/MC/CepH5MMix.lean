import HRS.Stochastic.SelectedFlow

/-!
# Packet M (CEPH5 measure lemmas): the mixture formula for a finite measurable partition

`h5M_mixture_general`: if `C : ι → Set (Config 1 N)` is a finite family of measurable, pairwise disjoint sets
covering the collision-free configurations, then the selected law is the mixture of the conditional selected laws.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepH5Pf

open HRS

section Mix

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}

theorem h5M_mixture_general {ι : Type*} [Fintype ι] [IsProbabilityMeasure P] {X₀ : Ω → Config 1 N}
    (hX₀ : Measurable X₀) (hdist : ∀ᵐ ω ∂P, X₀ ω ∉ collisionSet 1 N)
    {X : ℝ≥0 → Ω → Config 1 N} (t : ℝ) (hXt : Measurable (X (Real.toNNReal t)))
    (C : ι → Set (Config 1 N)) (hCm : ∀ i, MeasurableSet (C i))
    (hCd : Pairwise fun i j => Disjoint (C i) (C j)) (hCu : (⋃ i, C i) = (collisionSet 1 N)ᶜ) :
    selectedLaw P X t = ∑ i : ι, ENNReal.ofReal ((P (X₀ ⁻¹' C i)).toReal) •
      selectedLaw (ProbabilityTheory.cond P (X₀ ⁻¹' C i)) X t := by
  classical
  ext S hS
  have hY : MeasurableSet (X (Real.toNNReal t) ⁻¹' S) := hXt hS
  have hA : ∀ i, MeasurableSet (X₀ ⁻¹' C i) := fun i => hX₀ (hCm i)
  simp only [selectedLaw, law, Measure.coe_finset_sum, Measure.smul_apply, Finset.sum_apply,
    smul_eq_mul]
  rw [Measure.map_apply hXt hS]
  have hterm : ∀ i, ENNReal.ofReal ((P (X₀ ⁻¹' C i)).toReal) *
      (ProbabilityTheory.cond P (X₀ ⁻¹' C i)).map (X (Real.toNNReal t)) S
      = P (X₀ ⁻¹' C i ∩ X (Real.toNNReal t) ⁻¹' S) := by
    intro i
    rw [Measure.map_apply hXt hS, ENNReal.ofReal_toReal (measure_ne_top P _),
      ProbabilityTheory.cond_apply (hA i) P]
    by_cases h0 : P (X₀ ⁻¹' C i) = 0
    · rw [h0, zero_mul]
      exact (measure_mono_null Set.inter_subset_left h0).symm
    · rw [← mul_assoc, ENNReal.mul_inv_cancel h0 (measure_ne_top P _), one_mul]
  simp only [hterm]
  have hdisj : Pairwise (Function.onFun Disjoint fun i => X₀ ⁻¹' C i ∩ X (Real.toNNReal t) ⁻¹' S) := by
    intro i j hij
    exact ((hCd hij).preimage X₀).mono Set.inter_subset_left Set.inter_subset_left
  have hsum := measure_iUnion (μ := P) hdisj (fun i => (hA i).inter hY)
  rw [tsum_fintype] at hsum
  rw [← hsum]
  have hcov : (⋃ i, X₀ ⁻¹' C i ∩ X (Real.toNNReal t) ⁻¹' S)
      = X₀ ⁻¹' (collisionSet 1 N)ᶜ ∩ X (Real.toNNReal t) ⁻¹' S := by
    rw [← hCu, Set.preimage_iUnion, Set.iUnion_inter]
  rw [hcov]
  rw [Set.inter_comm]
  refine (measure_inter_conull ?_).symm
  rw [Set.preimage_compl, compl_compl]
  exact measure_eq_zero_iff_ae_notMem.mpr hdist
end Mix

end HRS.MC.CepH5Pf
