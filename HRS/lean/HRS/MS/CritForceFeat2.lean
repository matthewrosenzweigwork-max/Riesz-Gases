import HRS.MS.CritForceFeat1

/-!
# S8.2 core X1, part 2: weighted bounds for the Hermite features

`s82_hermite_bound`: `‖D^i φ_α(x)‖ ≤ C λ_α^{(⌊i+d/2⌋+1-m)/2}` with `C` independent of `m, α, x`.
`s82_hermite_memCMj`: `φ_α ∈ C_M^j` (so `φ_α ∈ C_M`) for every `M, j`.
`s82_hermite_weightedSupE_le`: `weightedSupE j (-M) φ_α ≤ ofReal (C_j λ_α^{(⌊j+d/2⌋+1-m)/2})`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82BD

open HRS HRS.Whole HRS.MP.RdInit HRS.MS.S52B

variable {d : ℕ}

theorem s82_one_le_jb (x : Euc d) : 1 ≤ jbracket x := by
  unfold jbracket
  exact Real.one_le_sqrt.2 (by nlinarith [sq_nonneg ‖x‖])

theorem s82_one_le_jb_rpow (x : Euc d) {M : ℝ} (hM : 0 ≤ M) : 1 ≤ jbracket x ^ M :=
  Real.one_le_rpow (s82_one_le_jb x) hM

/-- Hermite feature as a Schwartz function with explicit oscillator norms. -/
theorem s82_hermite_bound (N i : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℝ) (α : MultiIndex d) (x : Euc d),
    (1 + ‖x‖) ^ N * ‖iteratedFDeriv ℝ i (oscTestFun m α) x‖ ≤
      C * oscEigenvalue d α ^ ((((N + ⌊(i : ℝ) + (d : ℝ) / 2⌋₊ + 1 : ℕ) : ℝ) - m) / 2) := by
  obtain ⟨C, hC0, hC⟩ := s52b_weighted (d := d) N i
  refine ⟨C, hC0, fun m α x => ?_⟩
  obtain ⟨f, hf, hfN⟩ := s52b_phi (d := d) m α
  rw [← hf]
  refine (hC f x).trans ?_
  rw [hfN]

theorem s82_hermite_memCMj {M : ℝ} (hM : 0 < M) (j : ℕ) (m : ℝ) (α : MultiIndex d) :
    MemCMj M j (oscTestFun m α) := by
  obtain ⟨f, hf, -⟩ := s52b_phi (d := d) m α
  rw [← hf]
  refine ⟨(f.smooth j), fun i hi idx => ?_⟩
  obtain ⟨C, hC0, hC⟩ := s82_hermite_bound (d := d) 1 i
  obtain ⟨f', hf', hfN'⟩ := s52b_phi (d := d) m α
  have hfeq : (⇑f : Euc d → ℝ) = ⇑f' := hf.trans hf'.symm
  have hb : ∀ x : Euc d, (1 + ‖x‖) * ‖iteratedFDeriv ℝ i (⇑f) x‖ ≤
      C * oscEigenvalue d α ^ ((((1 + ⌊(i : ℝ) + (d : ℝ) / 2⌋₊ + 1 : ℕ) : ℝ) - m) / 2) := by
    intro x
    have := hC m α x
    rw [← hf] at this
    simpa using this
  set K : ℝ := C * oscEigenvalue d α ^ ((((1 + ⌊(i : ℝ) + (d : ℝ) / 2⌋₊ + 1 : ℕ) : ℝ) - m) / 2) with hK
  have hlim : Tendsto (fun x : Euc d => K / (1 + ‖x‖)) (cocompact (Euc d)) (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_left _ 1 tendsto_norm_cocompact_atTop)
  refine squeeze_zero_norm (fun x => ?_) hlim
  have h1 : |partialDeriv idx (⇑f) x| ≤ ‖iteratedFDeriv ℝ i (⇑f) x‖ := mri_abs_partialDeriv_le idx _ x
  have hpos : 0 < 1 + ‖x‖ := by positivity
  have h2 : ‖iteratedFDeriv ℝ i (⇑f) x‖ ≤ K / (1 + ‖x‖) := by
    rw [le_div_iff₀ hpos, mul_comm]; exact hb x
  have h3 : 1 ≤ jbracket x ^ M := s82_one_le_jb_rpow x hM.le
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (lt_of_lt_of_le one_pos h3)]
  calc |partialDeriv idx (⇑f) x| / jbracket x ^ M ≤ |partialDeriv idx (⇑f) x| :=
        div_le_self (abs_nonneg _) h3
    _ ≤ K / (1 + ‖x‖) := h1.trans h2

theorem s82_hermite_memCM {M : ℝ} (hM : 0 < M) (m : ℝ) (α : MultiIndex d) :
    MemCM M (oscTestFun m α) := by
  obtain ⟨f, hf, -⟩ := s52b_phi (d := d) m α
  rw [← hf]
  have h := s82_hermite_memCMj hM 0 m α
  rw [← hf] at h
  refine ⟨f.continuous, ?_⟩
  have := h.2 0 le_rfl (fun l => (Fin.elim0 l : Fin d))
  simpa [partialDeriv] using this

/-- Weighted sup norm of the features, polynomial in `λ_α`. -/
theorem s82_hermite_weightedSupE_le {M : ℝ} (hM : 0 < M) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℝ) (α : MultiIndex d),
      weightedSupE j (-M) (oscTestFun m α) ≤
        ENNReal.ofReal (C * oscEigenvalue d α ^ ((((⌊(j : ℝ) + (d : ℝ) / 2⌋₊ + 1 : ℕ) : ℝ) - m) / 2)) := by
  choose Ci hCi0 hCi using fun i : ℕ => s82_hermite_bound (d := d) 0 i
  refine ⟨∑ i ∈ Finset.range (j + 1), Ci i, Finset.sum_nonneg fun i _ => hCi0 i, fun m α => ?_⟩
  have hlam : (1 : ℝ) ≤ oscEigenvalue d α := by
    unfold oscEigenvalue
    have : (0 : ℝ) ≤ (α.degree : ℝ) := Nat.cast_nonneg _
    have : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg _
    linarith
  unfold weightedSupE derivSupE
  refine iSup_le fun i => iSup_le fun idx => iSup_le fun x => ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have hi : (i : ℕ) ≤ j := Nat.lt_succ_iff.1 i.2
  have hjb : jbracket x ^ (-M) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (s82_one_le_jb x) (by linarith)
  have h1 := mri_abs_partialDeriv_le idx (oscTestFun m α) x
  have h2 := hCi i m α x
  simp only [pow_zero, one_mul, Nat.zero_add] at h2
  have hexp : oscEigenvalue d α ^ ((((⌊((i : ℕ) : ℝ) + (d : ℝ) / 2⌋₊ + 1 : ℕ) : ℝ) - m) / 2) ≤
      oscEigenvalue d α ^ ((((⌊(j : ℝ) + (d : ℝ) / 2⌋₊ + 1 : ℕ) : ℝ) - m) / 2) := by
    refine Real.rpow_le_rpow_of_exponent_le hlam ?_
    have : ⌊((i : ℕ) : ℝ) + (d : ℝ) / 2⌋₊ ≤ ⌊(j : ℝ) + (d : ℝ) / 2⌋₊ :=
      Nat.floor_le_floor (by have : ((i : ℕ) : ℝ) ≤ j := by exact_mod_cast hi
                             linarith)
    have : ((⌊((i : ℕ) : ℝ) + (d : ℝ) / 2⌋₊ + 1 : ℕ) : ℝ) ≤ ((⌊(j : ℝ) + (d : ℝ) / 2⌋₊ + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.add_le_add_right this 1
    linarith
  have hpow : 0 ≤ oscEigenvalue d α ^ ((((⌊(j : ℝ) + (d : ℝ) / 2⌋₊ + 1 : ℕ) : ℝ) - m) / 2) :=
    Real.rpow_nonneg (by linarith) _
  have hCle : Ci i ≤ ∑ i ∈ Finset.range (j + 1), Ci i :=
    Finset.single_le_sum (f := Ci) (fun i _ => hCi0 i) (Finset.mem_range.2 (Nat.lt_succ_of_le hi))
  calc jbracket x ^ (-M) * |partialDeriv idx (oscTestFun m α) x|
      ≤ 1 * |partialDeriv idx (oscTestFun m α) x| :=
        mul_le_mul_of_nonneg_right hjb (abs_nonneg _)
    _ ≤ ‖iteratedFDeriv ℝ (i : ℕ) (oscTestFun m α) x‖ := by rw [one_mul]; exact h1
    _ ≤ Ci i * oscEigenvalue d α ^ ((((⌊((i : ℕ) : ℝ) + (d : ℝ) / 2⌋₊ + 1 : ℕ) : ℝ) - m) / 2) := h2
    _ ≤ (∑ i ∈ Finset.range (j + 1), Ci i) *
          oscEigenvalue d α ^ ((((⌊(j : ℝ) + (d : ℝ) / 2⌋₊ + 1 : ℕ) : ℝ) - m) / 2) :=
        mul_le_mul hCle hexp (Real.rpow_nonneg (by linarith) _) (Finset.sum_nonneg fun i _ => hCi0 i)

end HRS.MS.S82BD
