import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# S21H2, packet R26-T3.S14a (part B): Hilbert-Schmidt operators are compact (generic)

`s21h2_compact_of_hs`: if `b` is a Hilbert basis of `E` and `∑ ‖T b_i‖² < ∞`, then `T` is compact.  Proof: the finite-rank operators
`T_s = ∑_{i∈s} ⟪b_i, ·⟫ T b_i` converge to `T` in operator norm (tail estimate by Cauchy-Schwarz and Bessel), and compact operators are closed.
-/

noncomputable section

open Filter Topology
open scoped RealInnerProductSpace

namespace HRS.MS.R26T3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] {ι : Type*}

theorem s21h2_tail_bound (b : HilbertBasis ι ℝ E) (T : E →L[ℝ] E) (s : Finset ι) {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ t : Finset ι, Disjoint t s → ∑ i ∈ t, ‖T (b i)‖ ^ 2 ≤ δ ^ 2) (x : E) :
    ‖T x - ∑ i ∈ s, ⟪b i, x⟫ • T (b i)‖ ≤ δ * ‖x‖ := by
  classical
  have hsum : HasSum (fun i => ⟪b i, x⟫ • T (b i)) (T x) := by
    have := T.hasSum (b.hasSum_repr x)
    simpa [map_smul, HilbertBasis.repr_apply_apply] using this
  have hlim : Tendsto (fun u : Finset ι => ‖∑ i ∈ u, ⟪b i, x⟫ • T (b i) - ∑ i ∈ s, ⟪b i, x⟫ • T (b i)‖)
      atTop (𝓝 ‖T x - ∑ i ∈ s, ⟪b i, x⟫ • T (b i)‖) :=
    ((hsum : Tendsto (fun u : Finset ι => ∑ i ∈ u, ⟪b i, x⟫ • T (b i)) atTop (𝓝 (T x))).sub_const _).norm
  refine le_of_tendsto hlim ?_
  filter_upwards [eventually_ge_atTop s] with u hu
  have e1 : ∑ i ∈ u, ⟪b i, x⟫ • T (b i) - ∑ i ∈ s, ⟪b i, x⟫ • T (b i) =
      ∑ i ∈ u \ s, ⟪b i, x⟫ • T (b i) := by
    rw [← Finset.sum_sdiff hu]; abel
  rw [e1]
  refine (norm_sum_le _ _).trans ?_
  have e2 : ∀ i, ‖⟪b i, x⟫ • T (b i)‖ = |⟪b i, x⟫| * ‖T (b i)‖ := fun i => by
    rw [norm_smul, Real.norm_eq_abs]
  simp_rw [e2]
  refine (Real.sum_mul_le_sqrt_mul_sqrt _ _ _).trans ?_
  have hB : ∑ i ∈ u \ s, |⟪b i, x⟫| ^ 2 ≤ ‖x‖ ^ 2 := by
    have := b.orthonormal.sum_inner_products_le (𝕜 := ℝ) x (s := u \ s)
    simpa [Real.norm_eq_abs] using this
  have hT := h (u \ s) Finset.sdiff_disjoint
  calc √(∑ i ∈ u \ s, |⟪b i, x⟫| ^ 2) * √(∑ i ∈ u \ s, ‖T (b i)‖ ^ 2) ≤ √(‖x‖ ^ 2) * √(δ ^ 2) :=
        mul_le_mul (Real.sqrt_le_sqrt hB) (Real.sqrt_le_sqrt hT) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = δ * ‖x‖ := by rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hδ]; ring

theorem s21h2_compact_of_hs (b : HilbertBasis ι ℝ E) (T : E →L[ℝ] E)
    (hs : Summable fun i => ‖T (b i)‖ ^ 2) : IsCompactOperator T := by
  classical
  let Ts : Finset ι → E →L[ℝ] E := fun s => ∑ i ∈ s, (innerSL ℝ (b i)).smulRight (T (b i))
  have hTs : ∀ s, IsCompactOperator (Ts s) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa [Ts] using isCompactOperator_zero
    | insert a s ha ih =>
      have h1 : IsCompactOperator ((innerSL ℝ (b a)).smulRight (T (b a))) := by
        have hc : IsCompactOperator (ContinuousLinearMap.toSpanSingleton ℝ (T (b a))) :=
          isCompactOperator_of_locallyCompactSpace_rng _
        exact hc.comp_clm (innerSL ℝ (b a))
      have := h1.add ih
      simpa [Ts, Finset.sum_insert ha] using this
  refine isCompactOperator_of_tendsto (l := atTop) (F := Ts) ?_ (Eventually.of_forall hTs)
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hvan := cauchySeq_finset_iff_sum_vanishing.1 hs.hasSum.cauchySeq
  obtain ⟨s0, hs0⟩ := hvan (Set.Iio ((ε / 2) ^ 2)) (Iio_mem_nhds (by positivity))
  refine ⟨s0, fun s hs' => ?_⟩
  rw [dist_eq_norm]
  have hb : ∀ x, ‖(Ts s - T) x‖ ≤ (ε / 2) * ‖x‖ := by
    intro x
    have := s21h2_tail_bound b T s (δ := ε / 2) (by positivity) (fun t ht => ?_) x
    · have e : (Ts s - T) x = -(T x - ∑ i ∈ s, ⟪b i, x⟫ • T (b i)) := by
        simp [Ts]
      rw [e, norm_neg]; exact this
    · exact (hs0 t (Finset.disjoint_of_subset_right hs' ht)).le
  calc ‖Ts s - T‖ ≤ ε / 2 := ContinuousLinearMap.opNorm_le_bound _ (by positivity) hb
    _ < ε := by linarith

end HRS.MS.R26T3
