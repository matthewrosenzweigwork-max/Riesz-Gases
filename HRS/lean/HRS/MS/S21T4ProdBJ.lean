import HRS.MS.S21T4ProdBI

/-!
# R26-T3.S13: finite sums preserve convergence in L²

The finite-sum lemma is formulated on one probability space, so it can be
applied to simultaneous Gaussian quadratic-chaos coordinates.
-/

set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R26T3
open HRS

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem s21t4_tendstoL2_finset_sum {ι : Type*}
    (s : Finset ι) {Fn : ι → ℕ → Ω → ℝ}
    {F : ι → Ω → ℝ}
    (hm : ∀ i ∈ s, ∀ n, AEStronglyMeasurable (Fn i n) P)
    (h : ∀ i ∈ s, TendstoL2 P (Fn i) (F i)) :
    TendstoL2 P (fun n ω => ∑ i ∈ s, Fn i n ω)
      (fun ω => ∑ i ∈ s, F i ω) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      unfold TendstoL2
      constructor
      · exact aestronglyMeasurable_const
      · simp
  | @insert a s ha ih =>
      have haM : ∀ n, AEStronglyMeasurable (Fn a n) P :=
        fun n => hm a (Finset.mem_insert_self a s) n
      have hrestM : ∀ n, AEStronglyMeasurable
          (fun ω : Ω => ∑ i ∈ s, Fn i n ω) P := by
        intro n
        exact Finset.aestronglyMeasurable_fun_sum s (fun i hi =>
          hm i (Finset.mem_insert_of_mem hi) n)
      have hrest : TendstoL2 P
          (fun n ω => ∑ i ∈ s, Fn i n ω)
          (fun ω => ∑ i ∈ s, F i ω) :=
        ih (fun i hi => hm i (Finset.mem_insert_of_mem hi))
          (fun i hi => h i (Finset.mem_insert_of_mem hi))
      have hs := s21t4_tendstoL2_add haM hrestM
        (h a (Finset.mem_insert_self a s)) hrest
      simpa only [Finset.sum_insert ha] using hs

end HRS.MS.R26T3
