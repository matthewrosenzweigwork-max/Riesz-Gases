import HRS.MS.S82VG1

/-!
# S8.2 A02 (S82V), part 3: the algebraic identity behind the lifted generator
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace HRS.MS.S82V

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The finite algebra: triple sum, repeated indices, and the `F_mu / N` term. -/
theorem s82v_final_alg0 {N : ℕ} (x : Fin N → E) (G fm : E → E) (hG : ∀ z, G (-z) = -G z)
    (g : Fin N → Fin N → E) (J : Fin N → Fin N → ℝ) :
    let cf : Fin N → Fin N → E := fun i k => G (x i - x k) - fm (x i)
    let T3 : Fin N → Fin N → Fin N → ℝ := fun i j k =>
      -inner ℝ (cf i k) (g i j) - inner ℝ (cf j k) (g j i)
    let Bf : Fin N → Fin N → ℝ := fun i j =>
      inner ℝ (G (x i - x j)) (g i j - g j i) -
        2 * (inner ℝ (fm (x i)) (g i j) + inner ℝ (fm (x j)) (g j i))
    let Gt : Fin N → Fin N → Fin N → ℝ := (fun i j k =>
      (T3 i j k + T3 i k j + T3 j k i - J i j - J i k - J j k) / 3);
    -(N : ℝ) * (∑ i, ∑ j ∈ Finset.univ.erase i, J i j) +
      2 * ((∑ i, ∑ j ∈ Finset.univ.erase i, inner ℝ (fm (x i)) (g i j)) -
        ∑ i, ∑ j ∈ Finset.univ.erase i, ∑ k ∈ Finset.univ.erase i, inner ℝ (cf i k) (g i j)) +
      2 * (∑ i, ∑ j ∈ Finset.univ.erase i, J i j) - s82v_sum3 Gt +
      ∑ i, ∑ j ∈ Finset.univ.erase i, Bf i j = 0 := by
  intro cf T3 Bf Gt
  set J2 : ℝ := ∑ i, ∑ j ∈ Finset.univ.erase i, J i j with hJ2
  set SfM : ℝ := ∑ i, ∑ j ∈ Finset.univ.erase i, inner ℝ (fm (x i)) (g i j) with hSfM
  set SGg : ℝ := ∑ i, ∑ j ∈ Finset.univ.erase i, inner ℝ (G (x i - x j)) (g i j) with hSGg
  set t : Fin N → Fin N → Fin N → ℝ := fun i j k => inner ℝ (cf i k) (g i j) with ht
  set S3 : ℝ := s82v_sum3 t with hS3
  -- the triple sum of T3
  have hT3 : s82v_sum3 T3 = -2 * S3 := by
    have e : T3 = fun i j k => -t i j k - t j i k := rfl
    have e1 : s82v_sum3 (fun i j k => -t i j k - t j i k) =
        -s82v_sum3 t - s82v_sum3 (fun i j k => t j i k) := by
      rw [← s82v_sum3_neg, ← s82v_sum3_sub]
    rw [e, e1, s82v_sum3_swap12 t]; ring
  have hGt : s82v_sum3 Gt = -2 * S3 - ((N : ℝ) - 2) * J2 := by
    have e : Gt = fun i j k => (T3 i j k + T3 i k j + T3 j k i - J i j - J i k - J j k) / 3 :=
      rfl
    rw [e, s82v_sum3_div]
    have h1 : s82v_sum3 (fun i j k => T3 i j k + T3 i k j + T3 j k i - J i j - J i k - J j k) =
        s82v_sum3 T3 + s82v_sum3 (fun i j k => T3 i k j) + s82v_sum3 (fun i j k => T3 j k i) -
          s82v_sum3 (fun i j _ => J i j) - s82v_sum3 (fun i _ k => J i k) -
          s82v_sum3 (fun _ j k => J j k) := by
      rw [s82v_sum3_sub, s82v_sum3_sub, s82v_sum3_sub, s82v_sum3_add, s82v_sum3_add]
    have h2 : s82v_sum3 (fun i _ k => J i k) = s82v_sum3 (fun i j _ => J i j) := by
      have := s82v_sum3_swap23 (fun i j _ => J i j)
      exact this
    have h3 : s82v_sum3 (fun _ j k => J j k) = s82v_sum3 (fun i j _ => J i j) := by
      have := s82v_sum3_cyc (fun i j _ => J i j)
      exact this
    have h4 := s82v_sum3_pair J
    rw [h1, h2, h3, s82v_sum3_swap23 T3, s82v_sum3_cyc T3, hT3, h4]
    ring
  -- the repeated-index split
  have hScf : ∑ i, ∑ j ∈ Finset.univ.erase i, ∑ k ∈ Finset.univ.erase i, inner ℝ (cf i k) (g i j) =
      S3 + ∑ i, ∑ j ∈ Finset.univ.erase i, inner ℝ (cf i j) (g i j) := by
    rw [hS3, s82v_sum3, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [add_comm]
    exact (Finset.add_sum_erase (Finset.univ.erase i) (fun k => inner ℝ (cf i k) (g i j)) hj).symm
  have hRt : ∑ i, ∑ j ∈ Finset.univ.erase i, inner ℝ (cf i j) (g i j) = SGg - SfM := by
    rw [hSGg, hSfM, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [cf, inner_sub_left]
  -- the B-sum
  have hB : ∑ i, ∑ j ∈ Finset.univ.erase i, Bf i j = 2 * SGg - 4 * SfM := by
    have hB1 : ∑ i, ∑ j ∈ Finset.univ.erase i, inner ℝ (G (x i - x j)) (g j i) = -SGg := by
      rw [s82v_pairsum_swap (fun i j => inner ℝ (G (x i - x j)) (g j i)), hSGg, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      have : x j - x i = -(x i - x j) := by abel
      rw [this, hG, inner_neg_left]
    have hB2 : ∑ i, ∑ j ∈ Finset.univ.erase i, inner ℝ (fm (x j)) (g j i) = SfM := by
      rw [s82v_pairsum_swap (fun i j => inner ℝ (fm (x j)) (g j i))]
    have e : ∀ i j, Bf i j = inner ℝ (G (x i - x j)) (g i j) - inner ℝ (G (x i - x j)) (g j i) -
        2 * inner ℝ (fm (x i)) (g i j) - 2 * inner ℝ (fm (x j)) (g j i) := by
      intro i j
      simp only [Bf, inner_sub_right]; ring
    simp_rw [e, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hB1, hB2, ← hSGg, ← hSfM]
    ring
  rw [hGt, hScf, hRt, hB]
  ring

/-- The finite algebra, with the triple and repeated terms given as hypotheses. -/
theorem s82v_final_alg {N : ℕ} (x : Fin N → E) (G fm : E → E) (hG : ∀ z, G (-z) = -G z)
    (g : Fin N → Fin N → E) (J : Fin N → Fin N → ℝ)
    (Gt : Fin N → Fin N → Fin N → ℝ) (Bf : Fin N → Fin N → ℝ)
    (hGt : ∀ i j k, Gt i j k =
      ((-inner ℝ (G (x i - x k) - fm (x i)) (g i j) - inner ℝ (G (x j - x k) - fm (x j)) (g j i)) +
        (-inner ℝ (G (x i - x j) - fm (x i)) (g i k) - inner ℝ (G (x k - x j) - fm (x k)) (g k i)) +
        (-inner ℝ (G (x j - x i) - fm (x j)) (g j k) - inner ℝ (G (x k - x i) - fm (x k)) (g k j)) -
        J i j - J i k - J j k) / 3)
    (hBf : ∀ i j, Bf i j = inner ℝ (G (x i - x j)) (g i j - g j i) -
        2 * (inner ℝ (fm (x i)) (g i j) + inner ℝ (fm (x j)) (g j i))) :
    -(N : ℝ) * (∑ i, ∑ j ∈ Finset.univ.erase i, J i j) +
      2 * ((∑ i, ∑ j ∈ Finset.univ.erase i, inner ℝ (fm (x i)) (g i j)) -
        ∑ i, ∑ j ∈ Finset.univ.erase i, ∑ k ∈ Finset.univ.erase i,
          inner ℝ (G (x i - x k) - fm (x i)) (g i j)) +
      2 * (∑ i, ∑ j ∈ Finset.univ.erase i, J i j) - s82v_sum3 Gt +
      ∑ i, ∑ j ∈ Finset.univ.erase i, Bf i j = 0 := by
  have e1 : Gt = fun i j k =>
      ((-inner ℝ (G (x i - x k) - fm (x i)) (g i j) - inner ℝ (G (x j - x k) - fm (x j)) (g j i)) +
        (-inner ℝ (G (x i - x j) - fm (x i)) (g i k) - inner ℝ (G (x k - x j) - fm (x k)) (g k i)) +
        (-inner ℝ (G (x j - x i) - fm (x j)) (g j k) - inner ℝ (G (x k - x i) - fm (x k)) (g k j)) -
        J i j - J i k - J j k) / 3 := funext fun i => funext fun j => funext fun k => hGt i j k
  have e2 : Bf = fun i j => inner ℝ (G (x i - x j)) (g i j - g j i) -
        2 * (inner ℝ (fm (x i)) (g i j) + inner ℝ (fm (x j)) (g j i)) :=
    funext fun i => funext fun j => hBf i j
  subst e1 e2
  exact s82v_final_alg0 x G fm hG g J

end HRS.MS.S82V

end
