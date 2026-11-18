import HRS.MC.QRPWickAux1

/-!
# QRPWick, auxiliary file 2: the finite-dimensional matrix inequality behind the Wick variance bound
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.QRSpec.Wick

section Alg

variable {ι : Type} [Fintype ι]

lemma qrpw_alg_T1 (Sg A : ι → ι → ℝ) (hs : ∀ i j, Sg i j = Sg j i) :
    ∑ i, ∑ j, ∑ k, ∑ l, A i j * A k l * (Sg i k * Sg j l) =
      ∑ k, ∑ j, (∑ i, Sg k i * A i j) * (∑ l, A k l * Sg l j) := by
  have h1 : ∀ k j, (∑ i, Sg k i * A i j) * (∑ l, A k l * Sg l j) =
      ∑ i, ∑ l, A i j * A k l * (Sg i k * Sg j l) := by
    intro k j
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
    rw [hs k i, hs l j]; ring
  simp_rw [h1]
  -- reorder ∑ k ∑ j ∑ i ∑ l into ∑ i ∑ j ∑ k ∑ l
  calc ∑ i, ∑ j, ∑ k, ∑ l, A i j * A k l * (Sg i k * Sg j l)
      = ∑ i, ∑ k, ∑ j, ∑ l, A i j * A k l * (Sg i k * Sg j l) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ j, ∑ l, A i j * A k l * (Sg i k * Sg j l) := Finset.sum_comm
    _ = ∑ k, ∑ j, ∑ i, ∑ l, A i j * A k l * (Sg i k * Sg j l) :=
        Finset.sum_congr rfl fun k _ => Finset.sum_comm

lemma qrpw_alg_T2 (Sg A : ι → ι → ℝ) (hs : ∀ i j, Sg i j = Sg j i) :
    ∑ i, ∑ j, ∑ k, ∑ l, A i j * A k l * (Sg i l * Sg j k) =
      ∑ j, ∑ l, (∑ i, Sg l i * A i j) * (∑ k, Sg j k * A k l) := by
  have h1 : ∀ j l, (∑ i, Sg l i * A i j) * (∑ k, Sg j k * A k l) =
      ∑ i, ∑ k, A i j * A k l * (Sg i l * Sg j k) := by
    intro j l
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    rw [hs l i]; ring
  simp_rw [h1]
  calc ∑ i, ∑ j, ∑ k, ∑ l, A i j * A k l * (Sg i l * Sg j k)
      = ∑ i, ∑ j, ∑ l, ∑ k, A i j * A k l * (Sg i l * Sg j k) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ j, ∑ i, ∑ l, ∑ k, A i j * A k l * (Sg i l * Sg j k) := Finset.sum_comm
    _ = ∑ j, ∑ l, ∑ i, ∑ k, A i j * A k l * (Sg i l * Sg j k) :=
        Finset.sum_congr rfl fun j _ => Finset.sum_comm

lemma qrpw_alg_bound (Sg A : ι → ι → ℝ) (hs : ∀ i j, Sg i j = Sg j i) (K : ℝ)
    (hop : ∀ a : ι → ℝ, ∑ k, (∑ i, Sg k i * a i) ^ 2 ≤ K ^ 2 * ∑ i, a i ^ 2) :
    ∑ i, ∑ j, ∑ k, ∑ l, A i j * A k l * (Sg i k * Sg j l + Sg i l * Sg j k) ≤
      2 * K ^ 2 * ∑ i, ∑ j, A i j ^ 2 := by
  set N : ℝ := ∑ i, ∑ j, A i j ^ 2 with hN
  set C : ι → ι → ℝ := fun k j => ∑ i, Sg k i * A i j with hCdef
  set D : ι → ι → ℝ := fun k j => ∑ l, A k l * Sg l j with hDdef
  have hC : ∑ j, ∑ k, C k j ^ 2 ≤ K ^ 2 * N := by
    have : ∀ j, ∑ k, C k j ^ 2 ≤ K ^ 2 * ∑ i, A i j ^ 2 := fun j => hop (fun i => A i j)
    calc ∑ j, ∑ k, C k j ^ 2 ≤ ∑ j, K ^ 2 * ∑ i, A i j ^ 2 := Finset.sum_le_sum fun j _ => this j
      _ = K ^ 2 * N := by rw [← Finset.mul_sum, hN, Finset.sum_comm]
  have hD : ∑ k, ∑ j, D k j ^ 2 ≤ K ^ 2 * N := by
    have : ∀ k, ∑ j, D k j ^ 2 ≤ K ^ 2 * ∑ l, A k l ^ 2 := by
      intro k
      have := hop (fun l => A k l)
      calc ∑ j, D k j ^ 2 = ∑ j, (∑ l, Sg j l * A k l) ^ 2 := by
            refine Finset.sum_congr rfl fun j _ => ?_
            simp only [hDdef]
            congr 1
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [hs l j]; ring
        _ ≤ _ := this
    calc ∑ k, ∑ j, D k j ^ 2 ≤ ∑ k, K ^ 2 * ∑ l, A k l ^ 2 := Finset.sum_le_sum fun k _ => this k
      _ = K ^ 2 * N := by rw [← Finset.mul_sum]
  have e : ∀ i j k l : ι, A i j * A k l * (Sg i k * Sg j l + Sg i l * Sg j k) =
      A i j * A k l * (Sg i k * Sg j l) + A i j * A k l * (Sg i l * Sg j k) := fun _ _ _ _ => by ring
  simp_rw [e, Finset.sum_add_distrib]
  rw [qrpw_alg_T1 Sg A hs, qrpw_alg_T2 Sg A hs]
  have t1 : ∑ k, ∑ j, (∑ i, Sg k i * A i j) * (∑ l, A k l * Sg l j) ≤
      (∑ k, ∑ j, C k j ^ 2 + ∑ k, ∑ j, D k j ^ 2) / 2 := by
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_le_sum fun j _ => ?_
    have := sq_nonneg (C k j - D k j)
    show C k j * D k j ≤ _
    nlinarith
  have t2 : ∑ j, ∑ l, (∑ i, Sg l i * A i j) * (∑ k, Sg j k * A k l) ≤
      (∑ j, ∑ l, C l j ^ 2 + ∑ j, ∑ l, C j l ^ 2) / 2 := by
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_le_sum fun l _ => ?_
    have := sq_nonneg (C l j - C j l)
    show C l j * C j l ≤ _
    nlinarith
  have c1 : ∑ k, ∑ j, C k j ^ 2 = ∑ j, ∑ k, C k j ^ 2 := Finset.sum_comm
  have c2 : ∑ j, ∑ l, C j l ^ 2 = ∑ j, ∑ k, C k j ^ 2 := Finset.sum_comm
  have c3 : ∑ j, ∑ l, C l j ^ 2 = ∑ j, ∑ k, C k j ^ 2 := rfl
  rw [c2, c3] at t2
  rw [c1] at t1
  nlinarith

end Alg

end HRS.MC.QRSpec.Wick

end
