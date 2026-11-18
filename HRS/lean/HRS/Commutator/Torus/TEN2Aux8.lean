import HRS.Commutator.Torus.TEN2Aux7

/-!
# Torus energy layer (packet T-EN2), helper part 8: occupancy of the cells

Prefix `ten2_`.  `∑_j n_j² ≤ 1/N + N⁻²·#{(i,i') : i ≠ i' in the same cell}`, and points in the same cell are
within `2η√d`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.Commutator.TorusNote

open HRS

variable {d N : ℕ} {s η : ℝ}

theorem ten2_nCells_pos (hη : 0 < η) (hη1 : η ≤ 1) : 1 ≤ nCells η := by
  unfold nCells
  exact (Nat.one_le_floor_iff _).2 (by rw [one_le_inv_iff₀]; exact ⟨hη, hη1⟩)

theorem ten2_inv_nCells_le (hη : 0 < η) (hη1 : η ≤ 1) : 1 / (nCells η : ℝ) ≤ 2 * η := by
  have hm1 : (1 : ℝ) ≤ nCells η := by exact_mod_cast ten2_nCells_pos hη hη1
  have hlt : η⁻¹ < (nCells η : ℝ) + 1 := by
    unfold nCells; exact Nat.lt_floor_add_one _
  rw [div_le_iff₀ (by linarith)]
  have h2 : η⁻¹ ≤ 2 * (nCells η : ℝ) := by
    by_cases h : η⁻¹ ≤ 2
    · linarith
    · push Not at h; linarith
  have : 1 ≤ 2 * η * (nCells η : ℝ) := by
    have := mul_le_mul_of_nonneg_left h2 hη.le
    rw [mul_inv_cancel₀ hη.ne'] at this
    linarith
  linarith

/-- Two cells containing the same point coincide. -/
theorem ten2_cell_unique {m : ℕ} {x : Torus d} {j j' : Fin d → Fin m} (hm : 0 < m)
    (h : x ∈ cellT m j) (h' : x ∈ cellT m j') : j = j' := by
  funext a
  apply Fin.ext
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨h1, h2⟩ := h a
  obtain ⟨h1', h2'⟩ := h' a
  rw [div_le_iff₀ hm'] at h1 h1'
  rw [lt_div_iff₀ hm'] at h2 h2'
  have e1 : ((j a : ℕ) : ℝ) < ((j' a : ℕ) : ℝ) + 1 := by linarith
  have e2 : ((j' a : ℕ) : ℝ) < ((j a : ℕ) : ℝ) + 1 := by linarith
  have e1' : (j a : ℕ) < (j' a : ℕ) + 1 := by exact_mod_cast e1
  have e2' : (j' a : ℕ) < (j a : ℕ) + 1 := by exact_mod_cast e2
  omega

/-- Coordinates of two points of one cell differ by less than `1/m`. -/
theorem ten2_cell_close {m : ℕ} {x y : Torus d} {j : Fin d → Fin m} (hm : 0 < m)
    (hx : x ∈ cellT m j) (hy : y ∈ cellT m j) (a : Fin d) :
    |Torus.rep x a - Torus.rep y a| < 1 / (m : ℝ) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨h1, h2⟩ := hx a
  obtain ⟨h1', h2'⟩ := hy a
  rw [abs_lt]
  have e : ((j a : ℕ) : ℝ) / m + 1 / (m : ℝ) = (((j a : ℕ) : ℝ) + 1) / m := by ring
  constructor <;> linarith

/-- The quotient distance is at most the Euclidean norm of any lift. -/
theorem ten2_tdist_mk_le (y : Euc d) : KernelGrad.tdist (Torus.mk y) 0 ≤ ‖y‖ := by
  set c := KernelGrad.centeredRep (Torus.mk y) with hc
  have hcm : Torus.mk c = Torus.mk y := KernelGrad.mk_centeredRep _
  obtain ⟨k, hk⟩ := ten_mk_sub_lattice hcm
  have hbd : ∀ i, |c i| ≤ 1 / 2 := fun i => KernelGrad.abs_centeredRep_le _ i
  have hcoord : ∀ i, |c i| ≤ |y i| := by
    intro i
    have hi : c i = y i + (k i : ℝ) := by
      have := congrArg (fun v : Euc d => v i) hk
      simpa [Lattice.toEuc] using this
    by_cases hki : k i = 0
    · rw [hi, hki]; simp
    · have h1 : (1 : ℝ) ≤ |(k i : ℝ)| := by
        have : (1 : ℤ) ≤ |k i| := Int.one_le_abs hki
        exact_mod_cast this
      have h2 : |(k i : ℝ)| ≤ |y i| + |c i| := by
        calc |(k i : ℝ)| = |c i - y i| := by rw [hi]; ring_nf
          _ ≤ |c i| + |y i| := abs_sub _ _
          _ = |y i| + |c i| := add_comm _ _
      have := hbd i
      linarith
  rw [KernelGrad.tdist_zero_right, ← hc, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
  exact sq_le_sq.2 (hcoord i)

/-- Points of one cell are `2η√d`-close in the quotient distance. -/
theorem ten2_cell_tdist (hη : 0 < η) (hη1 : η ≤ 1) {x y : Torus d} {j : Fin d → Fin (nCells η)}
    (hx : x ∈ cellT (nCells η) j) (hy : y ∈ cellT (nCells η) j) :
    KernelGrad.tdist (x - y) 0 ≤ 2 * η * Real.sqrt d := by
  have hm := ten2_nCells_pos hη hη1
  have hm' : (0 : ℝ) < nCells η := by exact_mod_cast hm
  have hxy : x - y = Torus.mk (Torus.rep x - Torus.rep y) := by
    rw [sub_eq_add_neg (Torus.rep x), Torus.mk_add, ten_mk_neg, Torus.mk_rep, Torus.mk_rep,
      ← sub_eq_add_neg]
  rw [hxy]
  refine (ten2_tdist_mk_le _).trans ?_
  rw [EuclideanSpace.norm_eq]
  have hc : ∀ a, ‖(Torus.rep x - Torus.rep y) a‖ ^ 2 ≤ (2 * η) ^ 2 := by
    intro a
    have h1 := ten2_cell_close hm hx hy a
    have h2 := ten2_inv_nCells_le hη hη1
    have : ‖(Torus.rep x - Torus.rep y) a‖ ≤ 2 * η := by
      rw [Real.norm_eq_abs]
      have : (Torus.rep x - Torus.rep y) a = Torus.rep x a - Torus.rep y a := rfl
      rw [this]; linarith
    exact pow_le_pow_left₀ (norm_nonneg _) this 2
  calc Real.sqrt (∑ a, ‖(Torus.rep x - Torus.rep y) a‖ ^ 2) ≤ Real.sqrt ((d : ℝ) * (2 * η) ^ 2) := by
        refine Real.sqrt_le_sqrt ?_
        calc ∑ a, ‖(Torus.rep x - Torus.rep y) a‖ ^ 2 ≤ ∑ _a : Fin d, (2 * η) ^ 2 :=
              Finset.sum_le_sum fun a _ => hc a
          _ = (d : ℝ) * (2 * η) ^ 2 := by simp
    _ = 2 * η * Real.sqrt d := by
        rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq (by linarith)]
        ring

end HRS.Commutator.TorusNote
