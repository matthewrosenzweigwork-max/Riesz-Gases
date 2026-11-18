import HRS.Commutator.Torus.TUNITAux4

/-!
# T-UNIT-a helpers, part 5: the particle contribution `(5.atomicclosing)` on `𝕋^d`

Prefix `tunit_`.  Hölder for sequences over the `≈ η^{-d}` cells with `1/2 + 1/p₁ + 1/p₂ = 1`:
`N⁻¹ ∑_i |v_>(x_i)||u(x_i)| ≤ ∑_j n_j sup_{Q_j}|v_>| sup_{Q_j}|u| ≤ (∑ n_j²)^{1/2}
(∑ sup|v_>|^{p₁})^{1/p₁}(∑ sup|u|^{p₂})^{1/p₂}`, computed in `ℝ≥0∞`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators

namespace HRS.Commutator.TorusNote

open HRS HRS.KernelGrad

variable {d : ℕ} {s η : ℝ}

/-- Hölder for three sequences with exponents `2, p₁, p₂`, `1/2 + 1/p₁ + 1/p₂ = 1`. -/
theorem tunit_holder3 {ι : Type*} [MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι]
    (n b c : ι → ℝ≥0∞) {p1 p2 : ℝ} (hp1 : 0 < p1) (hp2 : 0 < p2)
    (hrel : (1 : ℝ) / 2 + 1 / p1 + 1 / p2 = 1) :
    ∑' j, n j * (b j * c j) ≤
      (∑' j, n j ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) *
        ((∑' j, b j ^ p1) ^ (1 / p1) * (∑' j, c j ^ p2) ^ (1 / p2)) := by
  classical
  have h := ENNReal.lintegral_prod_norm_pow_le (μ := Measure.count (α := ι))
    (Finset.univ : Finset (Fin 3))
    (f := ![fun j => n j ^ (2 : ℝ), fun j => b j ^ p1, fun j => c j ^ p2])
    (fun i _ => (measurable_of_countable _).aemeasurable)
    (p := ![(1 : ℝ) / 2, 1 / p1, 1 / p2])
    (by simpa [Fin.sum_univ_three] using hrel)
    (by intro i _; fin_cases i <;> simp <;> positivity)
  simp only [lintegral_count, Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Function.comp_apply,
    Fin.succ_zero_eq_one] at h
  have e : ∀ a, (n a ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) * (b a ^ p1) ^ (1 / p1) * (c a ^ p2) ^ (1 / p2) =
      n a * (b a * c a) := by
    intro a
    rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
      show (2 : ℝ) * (1 / 2) = 1 by norm_num, mul_one_div_cancel hp1.ne', mul_one_div_cancel hp2.ne',
      ENNReal.rpow_one, ENNReal.rpow_one, ENNReal.rpow_one]
    ring
  simp_rw [e] at h
  rw [← mul_assoc]
  exact h

/-- The exponent relation `1/2 + 1/p₁ + 1/p₂ = 1`. -/
theorem tunit_exponent_relation (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    0 < Whole.p1E d s ∧ 0 < Whole.p2E d s ∧
      (1 : ℝ) / 2 + 1 / Whole.p1E d s + 1 / Whole.p2E d s = 1 := by
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have h1 : 0 < (d : ℝ) - s - 2 := by linarith
  have h2 : 0 < s + 2 := by linarith
  have h3 : 0 < (d : ℝ) := by linarith
  refine ⟨by unfold Whole.p1E; positivity, by unfold Whole.p2E; positivity, ?_⟩
  unfold Whole.p1E Whole.p2E
  field_simp
  ring

/-- The sampling inequality: `N⁻¹ ∑_i ‖V x_i‖ₑ ‖u x_i‖ₑ ≤ ‖n‖_{ℓ²} ‖V‖_{cells p₁} ‖u‖_{cells p₂}`. -/
theorem tunit_particle_holder (hη : 0 < η) (hη1 : η ≤ 1) {N : ℕ} (hN : 1 ≤ N) (X : Config d N)
    (V u : Torus d → Euc d) {p1 p2 : ℝ} (hp1 : 0 < p1) (hp2 : 0 < p2)
    (hrel : (1 : ℝ) / 2 + 1 / p1 + 1 / p2 = 1) :
    (N : ℝ≥0∞)⁻¹ * ∑ i, (‖V (X i)‖ₑ * ‖u (X i)‖ₑ) ≤
      (ENNReal.ofReal (∑ j : Fin d → Fin (nCells η), occT η X j ^ 2)) ^ ((1 : ℝ) / 2) *
        (cellSupNorm η p1 V * cellSupNorm η p2 u) := by
  classical
  have hm : 1 ≤ nCells η := ten2_nCells_pos hη hη1
  set m := nCells η with hmdef
  obtain ⟨cj, hcj⟩ : ∃ cj : Fin N → (Fin d → Fin m), ∀ i, X i ∈ cellT m (cj i) :=
    ⟨fun i => (tsamp_cell_cover hm (X i)).choose, fun i => (tsamp_cell_cover hm (X i)).choose_spec⟩
  have hiff : ∀ i j, X i ∈ cellT m j ↔ cj i = j := fun i j =>
    ⟨fun h => ten2_cell_unique (by omega) (hcj i) h, fun h => h ▸ hcj i⟩
  set B : (Fin d → Fin m) → ℝ≥0∞ := fun j => ⨆ x ∈ cellT m j, ‖V x‖ₑ with hB
  set C : (Fin d → Fin m) → ℝ≥0∞ := fun j => ⨆ x ∈ cellT m j, ‖u x‖ₑ with hC
  have h1 : ∀ i, ‖V (X i)‖ₑ * ‖u (X i)‖ₑ ≤ B (cj i) * C (cj i) := by
    intro i
    exact mul_le_mul' (le_iSup₂_of_le (X i) (hcj i) le_rfl) (le_iSup₂_of_le (X i) (hcj i) le_rfl)
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hocc : ∀ j, ENNReal.ofReal (occT η X j) =
      (N : ℝ≥0∞)⁻¹ * ∑ i, (if cj i = j then (1 : ℝ≥0∞) else 0) := by
    intro j
    unfold occT
    rw [ENNReal.ofReal_mul (by positivity), one_div, ENNReal.ofReal_inv_of_pos (by positivity),
      ENNReal.ofReal_natCast]
    congr 1
    rw [Finset.card_filter, Nat.cast_sum]
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : cj i = j
    · have hx : X i ∈ cellT (nCells η) j := (hiff i j).2 h
      simp [h, hx]
    · have hx : X i ∉ cellT (nCells η) j := fun hx => h ((hiff i j).1 hx)
      simp [h, hx]
  have hsum : ∀ H : (Fin d → Fin m) → ℝ≥0∞,
      ∑ j, ENNReal.ofReal (occT η X j) * H j = (N : ℝ≥0∞)⁻¹ * ∑ i, H (cj i) := by
    intro H
    simp_rw [hocc]
    have : ∀ j, (N : ℝ≥0∞)⁻¹ * (∑ i, (if cj i = j then (1 : ℝ≥0∞) else 0)) * H j =
        (N : ℝ≥0∞)⁻¹ * ∑ i, (if cj i = j then H j else 0) := by
      intro j
      rw [mul_assoc, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> simp
    simp_rw [this]
    rw [← Finset.mul_sum, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_ite_eq]
    simp
  have hocc2 : ∑ j, (ENNReal.ofReal (occT η X j)) ^ (2 : ℝ) =
      ENNReal.ofReal (∑ j : Fin d → Fin m, occT η X j ^ 2) := by
    have hnn : ∀ j, 0 ≤ occT η X j := fun j => by unfold occT; positivity
    rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => sq_nonneg _)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ENNReal.ofReal_pow (hnn j), ENNReal.rpow_two]
  have hH := tunit_holder3 (fun j : Fin d → Fin m => ENNReal.ofReal (occT η X j)) B C hp1 hp2 hrel
  simp only [tsum_fintype] at hH
  calc (N : ℝ≥0∞)⁻¹ * ∑ i, (‖V (X i)‖ₑ * ‖u (X i)‖ₑ)
      ≤ (N : ℝ≥0∞)⁻¹ * ∑ i, (B (cj i) * C (cj i)) :=
        mul_le_mul_right (Finset.sum_le_sum fun i _ => h1 i) _
    _ = ∑ j, ENNReal.ofReal (occT η X j) * (B j * C j) := (hsum (fun j => B j * C j)).symm
    _ ≤ (∑ j, (ENNReal.ofReal (occT η X j)) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) *
          ((∑ j, B j ^ p1) ^ (1 / p1) * (∑ j, C j ^ p2) ^ (1 / p2)) := hH
    _ = (ENNReal.ofReal (∑ j : Fin d → Fin m, occT η X j ^ 2)) ^ ((1 : ℝ) / 2) *
          (cellSupNorm η p1 V * cellSupNorm η p2 u) := by
        rw [hocc2]
        rfl

end HRS.Commutator.TorusNote
