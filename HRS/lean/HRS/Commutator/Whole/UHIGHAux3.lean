import HRS.Commutator.Whole.Defs
import HRS.Commutator.Whole.Energy
import HRS.Commutator.Whole.Local
import HRS.Commutator.Whole.UHIGHAux2

/-!
# Packet CMX-HIGH auxiliary 3: the particle contribution `(5.atomicclosing)` (`[N] L699-714`)

Hölder for sequences over unit cubes with `1/2 + 1/p₁ + 1/p₂ = 1`:
`N⁻¹ ∑_i |v_{>1}(x_i)||u(x_i)| ≤ ∑_j n_j sup_{Q_j}|v_{>1}| sup_{Q_j}|u| ≤ (∑ n_j²)^{1/2} (∑ sup|v_{>1}|^{p₁})^{1/p₁}
(∑ sup|u|^{p₂})^{1/p₂}`, computed in `ℝ≥0∞`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff

namespace HRS.Commutator.Whole.UHIGH

open HRS HRS.Whole

variable {d : ℕ} {s : ℝ}

/-- Hölder for three sequences with exponents `2, p₁, p₂`, `1/2 + 1/p₁ + 1/p₂ = 1`. -/
theorem uhigh_holder3 {ι : Type*} [MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι]
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

/-- the cube index of a point. -/
def uhigh_cj {N : ℕ} (X : Fin N → Euc d) (i : Fin N) : Fin d → ℤ := fun k => ⌊X i k⌋

theorem uhigh_mem_cube {N : ℕ} (X : Fin N → Euc d) (i : Fin N) : X i ∈ cube (uhigh_cj X i) :=
  (energyAux_mem_cube_iff (X i) (uhigh_cj X i)).2 rfl

theorem uhigh_ofReal_occ {N : ℕ} (hN : 1 ≤ N) (X : Fin N → Euc d) (j : Fin d → ℤ) :
    ENNReal.ofReal (occ X j) =
      (N : ℝ≥0∞)⁻¹ * ∑ i, (if uhigh_cj X i = j then (1 : ℝ≥0∞) else 0) := by
  classical
  rw [energyAux_occ_eq, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_sum_of_nonneg
    (fun i _ => by split_ifs <;> norm_num)]
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  congr 1
  · rw [one_div, ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_natCast]
  · refine Finset.sum_congr rfl fun i _ => ?_
    unfold uhigh_cj
    split_ifs <;> simp

theorem uhigh_tsum_occ {N : ℕ} (hN : 1 ≤ N) (X : Fin N → Euc d) (H : (Fin d → ℤ) → ℝ≥0∞) :
    ∑' j, ENNReal.ofReal (occ X j) * H j = (N : ℝ≥0∞)⁻¹ * ∑ i, H (uhigh_cj X i) := by
  classical
  simp_rw [uhigh_ofReal_occ hN X]
  have : ∀ j, (N : ℝ≥0∞)⁻¹ * (∑ i, (if uhigh_cj X i = j then (1 : ℝ≥0∞) else 0)) * H j =
      (N : ℝ≥0∞)⁻¹ * ∑ i, (if uhigh_cj X i = j then H j else 0) := by
    intro j
    rw [mul_assoc, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  simp_rw [this]
  rw [ENNReal.tsum_mul_left]
  congr 1
  rw [Summable.tsum_finsetSum (fun i _ => ENNReal.summable)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hite : ∀ b, (if uhigh_cj X i = b then H b else 0) =
      if b = uhigh_cj X i then H (uhigh_cj X i) else 0 := by
    intro b
    by_cases h : b = uhigh_cj X i
    · subst h; simp
    · rw [if_neg h, if_neg (Ne.symm h)]
  simp_rw [hite]
  rw [tsum_ite_eq]

theorem uhigh_occ_summable {N : ℕ} (X : Fin N → Euc d) :
    Summable (fun j : Fin d → ℤ => occ X j ^ 2) := by
  classical
  refine summable_of_ne_finset_zero (s := Finset.univ.image (uhigh_cj X)) fun j hj => ?_
  have : occ X j = 0 := by
    rw [energyAux_occ_eq]
    have : ∀ i, (if (fun k => ⌊X i k⌋) = j then (1 : ℝ) else 0) = 0 := by
      intro i
      rw [if_neg]
      intro h
      exact hj (Finset.mem_image.2 ⟨i, Finset.mem_univ _, h⟩)
    simp [this]
  rw [this]
  norm_num

theorem uhigh_tsum_occ_sq {N : ℕ} (X : Fin N → Euc d) :
    ∑' j, (ENNReal.ofReal (occ X j)) ^ (2 : ℝ) = ENNReal.ofReal (∑' j, occ X j ^ 2) := by
  have hnn : ∀ j, 0 ≤ occ X j := fun j => by
    unfold occ
    positivity
  rw [ENNReal.ofReal_tsum_of_nonneg (fun j => sq_nonneg _) (uhigh_occ_summable X)]
  refine tsum_congr fun j => ?_
  rw [ENNReal.ofReal_pow (hnn j), ENNReal.rpow_two]

/-- The sampling inequality: `N⁻¹ ∑_i ‖V x_i‖ₑ ‖u x_i‖ₑ ≤ ‖n‖_{ℓ²} ‖V‖_{cube p₁} ‖u‖_{cube p₂}`. -/
theorem uhigh_particle_holder {N : ℕ} (hN : 1 ≤ N) (X : Fin N → Euc d) (V u : Euc d → Euc d)
    {p1 p2 : ℝ} (hp1 : 0 < p1) (hp2 : 0 < p2) (hrel : (1 : ℝ) / 2 + 1 / p1 + 1 / p2 = 1) :
    (N : ℝ≥0∞)⁻¹ * ∑ i, (‖V (X i)‖ₑ * ‖u (X i)‖ₑ) ≤
      (ENNReal.ofReal (∑' j, occ X j ^ 2)) ^ ((1 : ℝ) / 2) *
        (cubeSupNorm p1 V * cubeSupNorm p2 u) := by
  set B : (Fin d → ℤ) → ℝ≥0∞ := fun j => ⨆ x ∈ cube j, ‖V x‖ₑ with hB
  set C : (Fin d → ℤ) → ℝ≥0∞ := fun j => ⨆ x ∈ cube j, ‖u x‖ₑ with hC
  have h1 : ∀ i, ‖V (X i)‖ₑ * ‖u (X i)‖ₑ ≤ B (uhigh_cj X i) * C (uhigh_cj X i) := by
    intro i
    exact mul_le_mul' (le_iSup₂_of_le (X i) (uhigh_mem_cube X i) le_rfl)
      (le_iSup₂_of_le (X i) (uhigh_mem_cube X i) le_rfl)
  calc (N : ℝ≥0∞)⁻¹ * ∑ i, (‖V (X i)‖ₑ * ‖u (X i)‖ₑ)
      ≤ (N : ℝ≥0∞)⁻¹ * ∑ i, (B (uhigh_cj X i) * C (uhigh_cj X i)) := by
        exact mul_le_mul_right (Finset.sum_le_sum fun i _ => h1 i) _
    _ = ∑' j, ENNReal.ofReal (occ X j) * (B j * C j) :=
        (uhigh_tsum_occ hN X (fun j => B j * C j)).symm
    _ ≤ (∑' j, (ENNReal.ofReal (occ X j)) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) *
          ((∑' j, B j ^ p1) ^ (1 / p1) * (∑' j, C j ^ p2) ^ (1 / p2)) :=
        uhigh_holder3 _ B C hp1 hp2 hrel
    _ = (ENNReal.ofReal (∑' j, occ X j ^ 2)) ^ ((1 : ℝ) / 2) *
          (cubeSupNorm p1 V * cubeSupNorm p2 u) := by
        rw [uhigh_tsum_occ_sq]
        rfl

end HRS.Commutator.Whole.UHIGH
