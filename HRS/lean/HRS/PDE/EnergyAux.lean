import HRS.PDE.ForwardEq

/-!
# Auxiliary lemmas for the energy estimates (`HRS/PDE/Energy.lean`)

Pointwise weight inequalities, finite-support (trigonometric polynomial) facts, the
Leibniz rule for coefficient convolutions, and the `L²` bound for multiplication by a bounded
function.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE

variable {d : ℕ}

/-! ### Weights -/

/-- `4π²|k|² = ∑_i (2π k_i)²`. -/
theorem four_pi_enorm_sq (k : Lattice d) :
    4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 = ∑ i, (2 * Real.pi * (k i : ℝ)) ^ 2 := by
  unfold Lattice.enorm Lattice.toEuc
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => by ring

theorem weight_nonneg (α : Fin d → ℕ) (k : Lattice d) :
    0 ≤ ∏ i, (2 * Real.pi * (k i : ℝ)) ^ (2 * α i) :=
  Finset.prod_nonneg fun i _ => by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) _

theorem enormSq_nonneg (k : Lattice d) : 0 ≤ 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 := by positivity

/-- `∏ (2πk_i)^{2γ_i} ≤ (1+4π²|k|²)^{|γ|}`. -/
theorem weight_le_pow (γ : Fin d → ℕ) (k : Lattice d) :
    ∏ i, (2 * Real.pi * (k i : ℝ)) ^ (2 * γ i) ≤
      (1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) ^ (∑ i, γ i) := by
  rw [← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_le_prod₀ (fun i _ => ?_) fun i _ => ?_
  · rw [pow_mul]; exact pow_nonneg (sq_nonneg _) _
  · rw [pow_mul]
    have h1 : (2 * Real.pi * (k i : ℝ)) ^ 2 ≤ 1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 := by
      rw [four_pi_enorm_sq]
      have := Finset.single_le_sum (f := fun i => (2 * Real.pi * (k i : ℝ)) ^ 2)
        (fun i _ => sq_nonneg _) (Finset.mem_univ i)
      linarith
    exact pow_le_pow_left₀ (sq_nonneg _) h1 _

theorem one_le_sobBaseE (k : Lattice d) : 1 ≤ 1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 := by
  have := enormSq_nonneg k; linarith

theorem sobWeight_natCast (m : ℕ) (k : Lattice d) :
    sobWeight (m : ℝ) k = (1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) ^ m := by
  unfold sobWeight; rw [Real.rpow_natCast]

theorem sobWeight_nonnegE (m : ℝ) (k : Lattice d) : 0 ≤ sobWeight m k :=
  Real.rpow_nonneg (by have := one_le_sobBaseE k; linarith) _

theorem sobWeight_monoE {a b : ℝ} (hab : a ≤ b) (k : Lattice d) : sobWeight a k ≤ sobWeight b k :=
  Real.rpow_le_rpow_of_exponent_le (one_le_sobBaseE k) hab

/-- The pointwise comparison `(1+4π²|k|²)^m ≤ (d+1)^m ∑_{|α|≤m} ∏(2πk_i)^{2α_i}`. -/
theorem pow_le_sum_weight (m : ℕ) (k : Lattice d) :
    (1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) ^ m ≤
      ((d : ℝ) + 1) ^ m * ∑ α ∈ multiIndices d m, ∏ i, (2 * Real.pi * (k i : ℝ)) ^ (2 * α i) := by
  set f : Option (Fin d) → ℝ := fun o => o.elim 1 fun i => (2 * Real.pi * (k i : ℝ)) ^ 2 with hf
  obtain ⟨o, -, ho⟩ := Finset.exists_max_image (Finset.univ : Finset (Option (Fin d))) f
    ⟨none, Finset.mem_univ _⟩
  have hsum : 1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 ≤ ((d : ℝ) + 1) * f o := by
    rw [four_pi_enorm_sq]
    have : ∑ o' : Option (Fin d), f o' ≤ ∑ _o' : Option (Fin d), f o :=
      Finset.sum_le_sum fun o' _ => ho o' (Finset.mem_univ _)
    rw [Fintype.sum_option] at this
    simp only [hf, Option.elim_none, Option.elim_some, Finset.sum_const, Finset.card_univ,
      Fintype.card_option, Fintype.card_fin, nsmul_eq_mul] at this
    push_cast at this
    simpa [hf, add_comm] using this
  have hfo : 1 ≤ f o := by
    have := ho none (Finset.mem_univ _)
    simpa [hf] using this
  have hterm : f o ^ m ≤ ∑ α ∈ multiIndices d m, ∏ i, (2 * Real.pi * (k i : ℝ)) ^ (2 * α i) := by
    have hmem : ∀ α : Fin d → ℕ, (∑ i, α i = 0 ∨ ∃ i, α = Pi.single i m) → α ∈ multiIndices d m →
        True := fun _ _ _ => trivial
    rcases hoo : o with _ | i
    · -- f none = 1
      have h0 : (0 : Fin d → ℕ) ∈ multiIndices d m := by
        simp [multiIndices]
      have := Finset.single_le_sum (f := fun α : Fin d → ℕ =>
        ∏ i, (2 * Real.pi * (k i : ℝ)) ^ (2 * α i)) (fun α _ => weight_nonneg α k) h0
      simpa [hf, hoo] using this
    · have hi : (Pi.single i m : Fin d → ℕ) ∈ multiIndices d m := by
        simp only [multiIndices, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
        refine ⟨fun j => ?_, by simp⟩
        by_cases hj : j = i
        · subst hj; simp
        · simp [hj]
      have := Finset.single_le_sum (f := fun α : Fin d → ℕ =>
        ∏ i, (2 * Real.pi * (k i : ℝ)) ^ (2 * α i)) (fun α _ => weight_nonneg α k) hi
      have e : ∏ j, (2 * Real.pi * (k j : ℝ)) ^ (2 * (Pi.single i m : Fin d → ℕ) j) =
          ((2 * Real.pi * (k i : ℝ)) ^ 2) ^ m := by
        rw [Finset.prod_eq_single i]
        · simp [pow_mul]
        · intro j _ hj; simp [hj]
        · simp
      simp only [hf, Option.elim_some]
      rw [← e]; exact this
  calc (1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) ^ m
      ≤ (((d : ℝ) + 1) * f o) ^ m := pow_le_pow_left₀ (by have := one_le_sobBaseE k; linarith) hsum m
    _ = ((d : ℝ) + 1) ^ m * f o ^ m := mul_pow _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hterm (by positivity)

end HRS.PDE
