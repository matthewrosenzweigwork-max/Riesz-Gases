import HRS.MS.R2SeAux19

/-!
# S9.9 `r2_static_edgeworth`, packet 20: the pair energy of a finite-rank kernel

Worker S99, namespace `S99`.  `s99_pe_finrank`: for `h_n = ∑_{a,b} c_{ab} u_a ⊗ u_b` (`c` symmetric, `u_a ∈ C_c^∞`) and a probability
measure `μ`,
`N · pairEnergy h_n X μ = ½ ∑_{a,b} c_{ab} Z_a Z_b - ½ μ_N(∑ c_{ab} u_a u_b)`, `Z_a = √N(μ_N(u_a) - μ(u_a))`.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

noncomputable section

namespace S99

open S45
open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d N : ℕ}

theorem s99_sum4 {ι κ α β : Type*} [Fintype ι] [Fintype κ] [Fintype α] [Fintype β]
    (f : ι → κ → α → β → ℝ) :
    ∑ i, ∑ j, ∑ a, ∑ b, f i j a b = ∑ a, ∑ b, ∑ i, ∑ j, f i j a b := by
  calc ∑ i, ∑ j, ∑ a, ∑ b, f i j a b = ∑ i, ∑ a, ∑ j, ∑ b, f i j a b :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ a, ∑ i, ∑ j, ∑ b, f i j a b := Finset.sum_comm
    _ = ∑ a, ∑ i, ∑ b, ∑ j, f i j a b :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ i, ∑ j, f i j a b := Finset.sum_congr rfl fun a _ => Finset.sum_comm

theorem s99_pe_finrank {m : ℕ} {c : Fin m → Fin m → ℝ} {u : Fin m → Euc d → ℝ}
    (hu : IsR2FiniteRankData c u) (μ : Measure (Euc d)) [IsProbabilityMeasure μ] (hN : 1 ≤ N)
    (X : EucConfig d N) :
    (N : ℝ) * pairEnergy (r2FiniteRankKernel c u) X μ =
      (1 / 2) * ∑ a, ∑ b, c a b * ((Real.sqrt N * (pair (empirical X) (u a) - pair μ (u a))) *
          (Real.sqrt N * (pair (empirical X) (u b) - pair μ (u b)))) -
        (1 / 2) * pair (empirical X) (fun x => ∑ a, ∑ b, c a b * (u a x * u b x)) := by
  have hN' : 0 < N := hN
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  have hsq : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt (by positivity)
  have hint : ∀ a, Integrable (u a) μ := fun a =>
    (hu.smooth a).continuous.integrable_of_hasCompactSupport (hu.compactSupport a)
  set mm : Fin m → ℝ := fun a => pair μ (u a) with hmm
  set S : Fin m → ℝ := fun a => ∑ i, u a (X i) with hSdef
  have hAe : ∀ a, pair (empirical X) (u a) = (N : ℝ)⁻¹ * S a := fun a => pair_empirical hN' X (u a)
  -- the row integral
  have hrow : ∀ x : Euc d, ∫ y, r2FiniteRankKernel c u x y ∂μ = ∑ a, ∑ b, c a b * u a x * mm b := by
    intro x
    unfold r2FiniteRankKernel
    rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => (hint b).const_mul _]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_finsetSum _ fun b _ => (hint b).const_mul _]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [integral_const_mul]
    simp only [hmm, pair]
  -- the double integral
  have hdbl : ∫ x, ∫ y, r2FiniteRankKernel c u x y ∂μ ∂μ = ∑ a, ∑ b, c a b * (mm a * mm b) := by
    simp_rw [hrow]
    rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => ((hint a).const_mul (c a b)).mul_const (mm b)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_finsetSum _ fun b _ => ((hint a).const_mul (c a b)).mul_const (mm b)]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [integral_mul_const, integral_const_mul]
    simp only [hmm, pair]
    ring
  -- the pair sum
  have hpair : ∑ i, ∑ j ∈ Finset.univ.erase i, r2FiniteRankKernel c u (X i) (X j) =
      (∑ a, ∑ b, c a b * (S a * S b)) -
        ∑ i, ∑ a, ∑ b, c a b * (u a (X i) * u b (X i)) := by
    have e1 : ∀ i, ∑ j ∈ Finset.univ.erase i, r2FiniteRankKernel c u (X i) (X j) =
        (∑ j, r2FiniteRankKernel c u (X i) (X j)) - r2FiniteRankKernel c u (X i) (X i) := fun i => by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]; ring
    simp_rw [e1]
    rw [Finset.sum_sub_distrib]
    congr 1
    · unfold r2FiniteRankKernel
      rw [s99_sum4 (fun i j a b => c a b * u a (X i) * u b (X j))]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      simp only [hSdef]
      rw [Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    · refine Finset.sum_congr rfl fun i _ => ?_
      unfold r2FiniteRankKernel
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      ring
  have hrowsum : ∑ i, ∫ y, r2FiniteRankKernel c u (X i) y ∂μ = ∑ a, ∑ b, c a b * S a * mm b := by
    simp_rw [hrow]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [hSdef]
    rw [Finset.mul_sum, Finset.sum_mul]
  -- the right-hand side
  set T1 : ℝ := ∑ a, ∑ b, c a b * (S a * S b) with hT1
  set T2 : ℝ := ∑ a, ∑ b, c a b * S a * mm b with hT2
  set T4 : ℝ := ∑ a, ∑ b, c a b * (mm a * mm b) with hT4
  set Ud : ℝ := ∑ i, ∑ a, ∑ b, c a b * (u a (X i) * u b (X i)) with hUd
  have hT3 : ∑ a, ∑ b, c a b * (mm a * S b) = T2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hu.symm b a]; ring
  have hZ : ∑ a, ∑ b, c a b * ((Real.sqrt N * (pair (empirical X) (u a) - pair μ (u a))) *
      (Real.sqrt N * (pair (empirical X) (u b) - pair μ (u b)))) =
      (N : ℝ)⁻¹ * T1 - T2 - ∑ a, ∑ b, c a b * (mm a * S b) + N * T4 := by
    have hpt : ∀ a b : Fin m, c a b * ((Real.sqrt N * (pair (empirical X) (u a) - pair μ (u a))) *
        (Real.sqrt N * (pair (empirical X) (u b) - pair μ (u b)))) =
        (N : ℝ)⁻¹ * (c a b * (S a * S b)) - c a b * S a * mm b - c a b * (mm a * S b) +
          N * (c a b * (mm a * mm b)) := by
      intro a b
      have e : (Real.sqrt N * (pair (empirical X) (u a) - pair μ (u a))) *
          (Real.sqrt N * (pair (empirical X) (u b) - pair μ (u b))) =
          (Real.sqrt N * Real.sqrt N) * ((pair (empirical X) (u a) - pair μ (u a)) *
          (pair (empirical X) (u b) - pair μ (u b))) := by ring
      rw [e, hsq, hAe a, hAe b]
      simp only [hmm]
      field_simp
      ring
    simp_rw [hpt]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rfl
  unfold pairEnergy
  rw [hpair, hrowsum, hdbl, hZ, hT3, pair_empirical hN']
  have hUd2 : (∑ i, ∑ a, ∑ b, c a b * (u a (X i) * u b (X i))) = Ud := rfl
  rw [hUd2]
  field_simp
  ring

end S99

end
