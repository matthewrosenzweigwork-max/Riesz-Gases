import HRS.MS.Fp81S21WeightedGenNL
import HRS.MS.Fp81S21WeightedGenNL9
import HRS.MS.WhoAux5

/-! Pointwise source-jet estimates for the cutoff argument. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.Ul HRS.MS.Who HRS.MS.ProClosureS111

/-- A density with Gaussian jet bounds times a directional derivative has
source jets controlled by the input's pointwise weighted-jet norm. -/
theorem fp81s21_b3_source_jet_pointwise {p : Parameters} {δ : ℝ}
    (R : Trajectory p δ) (u : ℝ) {B c : ℝ}
    (hB : 0 ≤ B) (hdata : fp81s21_b3_Data R B c) (hu : 0 ≤ u)
    (f : Euc p.d → ℝ)
    (hf : ContDiff ℝ (fp81s21_b3_q p + 2) f)
    (j : Fin p.d) (m : ℕ) (hm : m ≤ fp81s21_b3_q p + 1) (x : Euc p.d) :
    ‖iteratedFDeriv ℝ m (fp81s21_b3_source R u f j) x‖ ≤
      (2 : ℝ) ^ (fp81s21_b3_q p + 1) * B * ‖ul1w (r26t3_coeff R).M j‖ *
        ((p.d : ℝ) + 1) ^ (fp81s21_b3_q p + 2) *
        Real.exp (-c * ‖x‖ ^ 2) * jbracket x ^ (fp81s21_b3_P p) *
        ‖weightedJets (fp81s21_b3_q p + 2) (fp81s21_b3_P p) f x‖ := by
  let q := fp81s21_b3_q p
  let P := fp81s21_b3_P p
  let v := ul1w (r26t3_coeff R).M j
  let D : ℝ := ‖v‖ * ((p.d : ℝ) + 1) ^ (q + 2) * jbracket x ^ P * ‖weightedJets (q + 2) P f x‖
  have hD : 0 ≤ D := by
    dsimp [D]
    exact mul_nonneg (mul_nonneg (mul_nonneg (norm_nonneg _) (by positivity))
      (Real.rpow_nonneg (who_jb_pos x).le _)) (norm_nonneg _)
  obtain ⟨_, _, hρc, hρb⟩ := hdata u hu
  have hφc : ContDiff ℝ (q + 1) (fun y => fderiv ℝ f y v) :=
    (hf.fderiv_right (by exact_mod_cast (show q + 2 ≤ q + 1 + 1 by omega))).clm_apply contDiff_const
  have hφb : ∀ i ≤ q + 1,
      ‖iteratedFDeriv ℝ i (fun y => fderiv ℝ f y v) x‖ ≤ D := by
    intro i hi
    have hnorm := norm_iteratedFDeriv_clm_apply_const (N := ((q + 1 : ℕ) : WithTop ℕ∞))
      (c := v) (x := x) (n := i)
      (hf.fderiv_right (by exact_mod_cast (show q + 2 ≤ q + 1 + 1 by omega))).contDiffAt
      (by exact_mod_cast hi)
    rw [norm_iteratedFDeriv_fderiv] at hnorm
    exact hnorm.trans (by
      dsimp [D]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (fp81s21_weighted_iterated_le_unweighted f (show i + 1 ≤ q + 2 by omega) x) (norm_nonneg v))
  have heq : fp81s21_b3_source R u f j = fun y => R.ρ u y * fderiv ℝ f y v := by
    funext y
    simp only [fp81s21_b3_source, ul1_matVec, v]
  rw [heq]
  refine (norm_iteratedFDeriv_mul_le (hρc.of_le (by exact_mod_cast (show q + 1 ≤ q + 2 by omega))) hφc x (by exact_mod_cast hm)).trans ?_
  have he : 0 ≤ Real.exp (-c * ‖x‖ ^ 2) := (Real.exp_pos _).le
  have ht : ∀ i ∈ Finset.range (m + 1),
      (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i (R.ρ u) x‖ *
          ‖iteratedFDeriv ℝ (m - i) (fun y => fderiv ℝ f y v) x‖ ≤
        (m.choose i : ℝ) * (B * Real.exp (-c * ‖x‖ ^ 2) * D) := by
    intro i hi
    have hi' : i ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have hh := mul_le_mul (hρb i (by omega) x)
      (hφb (m - i) (by omega)) (norm_nonneg _) (mul_nonneg hB he)
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg (m.choose i))
  calc
    _ ≤ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * (B * Real.exp (-c * ‖x‖ ^ 2) * D) := Finset.sum_le_sum ht
    _ = (2 : ℝ) ^ m * (B * Real.exp (-c * ‖x‖ ^ 2) * D) := by
      rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
      push_cast
      rfl
    _ ≤ (2 : ℝ) ^ (q + 1) * (B * Real.exp (-c * ‖x‖ ^ 2) * D) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hm)
        (mul_nonneg (mul_nonneg hB he) hD)
    _ = _ := by dsimp [D, v, q, P]; ring

#print axioms HRS.Fp81.S21.fp81s21_b3_source_jet_pointwise
end HRS.Fp81.S21
