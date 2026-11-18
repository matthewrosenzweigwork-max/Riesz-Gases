import HRS.MC.S7E0b

/-!
# Packets `s7_E3a/b`, file 5: the finite-dimensional lower bound

For a symmetric `H` and `C = 1 - B` with `B >= 0`, `C >= 0`, if `x.x - x.C.x <= eta x.x` on vectors supported
in `[N, L)` and the rows of `H` have squared norm `<= S^2`, then
`sum H_ij H_kl C_ik C_jl >= (1 - 4 eta) sum H_ij^2 - 4 N S^2`.
-/

open scoped BigOperators Matrix Kronecker

noncomputable section

namespace HRS.MC.Sec7.E3Aux5

variable {L : ℕ}

theorem e3_kron_quad2 (M N : Matrix (Fin L) (Fin L) ℝ) (a : Fin L → Fin L → ℝ) :
    star (fun p : Fin L × Fin L => a p.1 p.2) ⬝ᵥ (M ⊗ₖ N) *ᵥ (fun p : Fin L × Fin L => a p.1 p.2) =
      ∑ i, ∑ j, ∑ k, ∑ l, a i j * a k l * (M i k * N j l) := by
  simp only [dotProduct, Matrix.mulVec, Matrix.kroneckerMap_apply, star_trivial, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

/-- the quadratic form of `B` on a sum of two vectors -/
theorem e3_qf_split {B : Matrix (Fin L) (Fin L) ℝ} (hB : B.PosSemidef) (y1 y2 : Fin L → ℝ) :
    (y1 + y2) ⬝ᵥ (B *ᵥ (y1 + y2)) ≤ 2 * (y1 ⬝ᵥ (B *ᵥ y1)) + 2 * (y2 ⬝ᵥ (B *ᵥ y2)) := by
  have h := hB.dotProduct_mulVec_nonneg (y1 - y2)
  simp only [star_trivial] at h
  simp only [Matrix.mulVec_add, Matrix.mulVec_sub, dotProduct_add, dotProduct_sub, add_dotProduct,
    sub_dotProduct] at h ⊢
  linarith


theorem e3_qf_bound {C : Matrix (Fin L) (Fin L) ℝ} {N : ℕ} {η : ℝ} (hη : 0 ≤ η)
    (hB : ((1 : Matrix (Fin L) (Fin L) ℝ) - C).PosSemidef) (hC : C.PosSemidef)
    (htail : ∀ y : Fin L → ℝ, (∀ i : Fin L, (i : ℕ) < N → y i = 0) →
      y ⬝ᵥ y - y ⬝ᵥ (C *ᵥ y) ≤ η * (y ⬝ᵥ y)) (y : Fin L → ℝ) :
    y ⬝ᵥ (((1 : Matrix (Fin L) (Fin L) ℝ) - C) *ᵥ y) ≤
      2 * ∑ i ∈ Finset.univ.filter (fun i : Fin L => (i : ℕ) < N), y i ^ 2 + 2 * η * (y ⬝ᵥ y) := by
  set B : Matrix (Fin L) (Fin L) ℝ := 1 - C with hBdef
  have hQ : ∀ v : Fin L → ℝ, v ⬝ᵥ (B *ᵥ v) = v ⬝ᵥ v - v ⬝ᵥ (C *ᵥ v) := by
    intro v
    rw [hBdef, Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub]
  set y1 : Fin L → ℝ := fun i => if (i : ℕ) < N then y i else 0 with hy1
  set y2 : Fin L → ℝ := fun i => if (i : ℕ) < N then 0 else y i with hy2
  have hsum : y1 + y2 = y := by
    funext i; simp only [hy1, hy2, Pi.add_apply]; split_ifs <;> simp
  have h1 := e3_qf_split hB y1 y2
  rw [hsum] at h1
  have hq1 : y1 ⬝ᵥ (B *ᵥ y1) ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin L => (i : ℕ) < N), y i ^ 2 := by
    rw [hQ]
    have := hC.dotProduct_mulVec_nonneg y1
    simp only [star_trivial] at this
    have e1 : y1 ⬝ᵥ y1 = ∑ i ∈ Finset.univ.filter (fun i : Fin L => (i : ℕ) < N), y i ^ 2 := by
      simp only [dotProduct, hy1, Finset.sum_filter]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> simp [sq]
    linarith
  have hq2 : y2 ⬝ᵥ (B *ᵥ y2) ≤ η * (y ⬝ᵥ y) := by
    have := htail y2 (fun i hi => by simp [hy2, hi])
    rw [hQ]
    refine this.trans (mul_le_mul_of_nonneg_left ?_ hη)
    simp only [dotProduct, hy2]
    refine Finset.sum_le_sum fun i _ => ?_
    split_ifs
    · simp [mul_self_nonneg]
    · exact le_refl _
  linarith


theorem e3_theta_bound {C : Matrix (Fin L) (Fin L) ℝ} {N : ℕ} {η S : ℝ} (hη : 0 ≤ η)
    (hB : ((1 : Matrix (Fin L) (Fin L) ℝ) - C).PosSemidef) (hC : C.PosSemidef)
    (htail : ∀ y : Fin L → ℝ, (∀ i : Fin L, (i : ℕ) < N → y i = 0) →
      y ⬝ᵥ y - y ⬝ᵥ (C *ᵥ y) ≤ η * (y ⬝ᵥ y))
    (H : Fin L → Fin L → ℝ) (hH : ∀ i j, H i j = H j i) (hrow : ∀ i, ∑ k, H i k ^ 2 ≤ S ^ 2) :
    ∑ i, (fun l => H i l) ⬝ᵥ (((1 : Matrix (Fin L) (Fin L) ℝ) - C) *ᵥ (fun l => H i l)) ≤
      2 * N * S ^ 2 + 2 * η * ∑ i, ∑ j, H i j ^ 2 := by
  have h1 : ∀ i, (fun l => H i l) ⬝ᵥ (((1 : Matrix (Fin L) (Fin L) ℝ) - C) *ᵥ (fun l => H i l)) ≤
      2 * ∑ l ∈ Finset.univ.filter (fun l : Fin L => (l : ℕ) < N), H i l ^ 2 +
        2 * η * ∑ l, H i l ^ 2 := by
    intro i
    have := e3_qf_bound hη hB hC htail (fun l => H i l)
    simpa [dotProduct, sq] using this
  refine (Finset.sum_le_sum fun i _ => h1 i).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have h2 : ∑ i, ∑ l ∈ Finset.univ.filter (fun l : Fin L => (l : ℕ) < N), H i l ^ 2 ≤ N * S ^ 2 := by
    rw [Finset.sum_comm]
    calc ∑ l ∈ Finset.univ.filter (fun l : Fin L => (l : ℕ) < N), ∑ i, H i l ^ 2
        ≤ ∑ l ∈ Finset.univ.filter (fun l : Fin L => (l : ℕ) < N), S ^ 2 := by
          refine Finset.sum_le_sum fun l _ => ?_
          calc ∑ i, H i l ^ 2 = ∑ i, H l i ^ 2 := by simp only [hH]
            _ ≤ S ^ 2 := hrow l
      _ = (Finset.univ.filter (fun l : Fin L => (l : ℕ) < N)).card * S ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ N * S ^ 2 := by
          refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
          have : (Finset.univ.filter (fun l : Fin L => (l : ℕ) < N)).card ≤ N := by
            calc _ = ((Finset.univ.filter (fun l : Fin L => (l : ℕ) < N)).image
                  (fun l : Fin L => (l : ℕ))).card :=
                  (Finset.card_image_of_injective _ Fin.val_injective).symm
              _ ≤ (Finset.range N).card := by
                  refine Finset.card_le_card fun m hm => ?_
                  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hm
                  obtain ⟨l, hl, rfl⟩ := hm
                  simpa using hl
              _ = N := Finset.card_range N
          exact_mod_cast this
  have h3 : ∑ i, ∑ l, H i l ^ 2 = ∑ i, ∑ j, H i j ^ 2 := rfl
  nlinarith [h2]


theorem e3_matrix_lower {C : Matrix (Fin L) (Fin L) ℝ} {N : ℕ} {η S : ℝ} (hη : 0 ≤ η)
    (hB : ((1 : Matrix (Fin L) (Fin L) ℝ) - C).PosSemidef) (hC : C.PosSemidef)
    (htail : ∀ y : Fin L → ℝ, (∀ i : Fin L, (i : ℕ) < N → y i = 0) →
      y ⬝ᵥ y - y ⬝ᵥ (C *ᵥ y) ≤ η * (y ⬝ᵥ y))
    (H : Fin L → Fin L → ℝ) (hH : ∀ i j, H i j = H j i) (hrow : ∀ i, ∑ k, H i k ^ 2 ≤ S ^ 2) :
    (1 - 4 * η) * ∑ i, ∑ j, H i j ^ 2 - 4 * N * S ^ 2 ≤
      ∑ i, ∑ j, ∑ k, ∑ l, H i j * H k l * (C i k * C j l) := by
  set B : Matrix (Fin L) (Fin L) ℝ := 1 - C with hBdef
  have hCB : ∀ i k, C i k = (1 : Matrix (Fin L) (Fin L) ℝ) i k - B i k := by
    intro i k; simp [hBdef]
  have hBs : ∀ i k, B i k = B k i := fun i k => by
    have := hB.isHermitian.apply i k
    simpa using this.symm
  have hZ := HRS.MC.Sec7.E0b.e0b_kron_nonneg hB H
  have hpt : ∀ i j k l, H i j * H k l * (C i k * C j l) =
      H i j * H k l * ((1 : Matrix (Fin L) (Fin L) ℝ) i k * (1 : Matrix (Fin L) (Fin L) ℝ) j l) -
      H i j * H k l * ((1 : Matrix (Fin L) (Fin L) ℝ) i k * B j l) -
      H i j * H k l * (B i k * (1 : Matrix (Fin L) (Fin L) ℝ) j l) +
      H i j * H k l * (B i k * B j l) := by
    intro i j k l
    rw [hCB i k, hCB j l]; ring
  simp only [hpt, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hS1 : ∑ i, ∑ j, ∑ k, ∑ l, H i j * H k l *
      ((1 : Matrix (Fin L) (Fin L) ℝ) i k * (1 : Matrix (Fin L) (Fin L) ℝ) j l) =
      ∑ i, ∑ j, H i j ^ 2 := by
    simp [Matrix.one_apply, sq]
  have hS2 : ∑ i, ∑ j, ∑ k, ∑ l, H i j * H k l *
      ((1 : Matrix (Fin L) (Fin L) ℝ) i k * B j l) =
      ∑ i, (fun l => H i l) ⬝ᵥ (B *ᵥ (fun l => H i l)) := by
    simp [Matrix.one_apply, dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  have hS3 : ∑ i, ∑ j, ∑ k, ∑ l, H i j * H k l *
      (B i k * (1 : Matrix (Fin L) (Fin L) ℝ) j l) =
      ∑ i, (fun l => H i l) ⬝ᵥ (B *ᵥ (fun l => H i l)) := by
    simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
      if_true]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
    rw [hH i j, hH k j, hBs i k]; ring
  rw [hS1, hS2, hS3]
  have hT := e3_theta_bound hη hB hC htail H hH hrow
  nlinarith [hT, hZ]

end HRS.MC.Sec7.E3Aux5

end
