import HRS.MS.Fp81S21ShiftedMildAssembly5

/-! Finite and countable coordinate square sums in `L³`, in the form needed
for the modewise sixth-moment assembly of the particle window supremum. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace HRS.Fp81.S21

/-- The `L³` norm of a finite sum of coordinate squares is bounded by the
sum of the squared `L⁶` norms of the coordinates. -/
theorem fp81s21_finite_sum_l3_minkowski
    {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (s : Finset ι) (X : ι → Ω → ℝ)
    (hX : ∀ i ∈ s, AEMeasurable (X i) P) :
    eLpNorm (fun ω => ∑ i ∈ s, (X i ω) ^ 2) 3 P ≤
      ∑ i ∈ s, (eLpNorm (X i) 6 P) ^ 2 := by
  have hsum : (fun ω => ∑ i ∈ s, (X i ω) ^ 2) =
      ∑ i ∈ s, fun ω => (X i ω) ^ 2 := by
    funext ω
    simp
  rw [hsum]
  calc
    eLpNorm (∑ i ∈ s, fun ω => (X i ω) ^ 2) 3 P ≤
        ∑ i ∈ s, eLpNorm (fun ω => (X i ω) ^ 2) 3 P := by
      apply eLpNorm_sum_le (p := (3 : ℝ≥0∞)) (μ := P) (s := s)
      norm_num
    _ = ∑ i ∈ s, (eLpNorm (X i) 6 P) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      calc
        eLpNorm (fun ω => (X i ω) ^ 2) 3 P =
            eLpNorm (fun ω => ‖X i ω‖ ^ (2 : ℝ)) 3 P := by
          apply eLpNorm_congr_ae
          filter_upwards with ω
          simpa [Real.norm_eq_abs] using (sq_abs (X i ω)).symm
        _ = eLpNorm (X i) ((3 : ℝ≥0∞) * ENNReal.ofReal 2) P ^ 2 :=
          eLpNorm_norm_rpow (X i) (hX i hi).aestronglyMeasurable (by norm_num)
        _ = (eLpNorm (X i) 6 P) ^ 2 := by norm_num

/-- Countable `L³` triangle inequality for nonnegative series, obtained by
passing to finite partial sums in `ENNReal`. -/
theorem fp81s21_tsum_l3_minkowski
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ≥0∞)
    (hX : ∀ n, AEStronglyMeasurable (X n) P) :
    (∫⁻ ω, (∑' n, X n ω) ^ (3 : ℝ) ∂P) ^ (1 / 3 : ℝ) ≤
      ∑' n, eLpNorm' (X n) 3 P := by
  let S : ℕ → Ω → ℝ≥0∞ := fun k ω => ∑ n ∈ Finset.range k, X n ω
  have hS : ∀ k, AEStronglyMeasurable (S k) P := by
    intro k
    exact (Finset.range k).aestronglyMeasurable_fun_sum fun n hn => hX n
  let B : ℝ≥0∞ := ∑' n, eLpNorm' (X n) 3 P
  have hpartial (k : ℕ) : eLpNorm' (S k) 3 P ≤ B := by
    have hfun : (fun ω => ∑ n ∈ Finset.range k, X n ω) =
        ∑ n ∈ Finset.range k, fun ω => X n ω := by
      funext ω
      simp
    rw [show S k = fun ω => ∑ n ∈ Finset.range k, X n ω from rfl, hfun]
    calc
      eLpNorm' (∑ n ∈ Finset.range k, fun ω => X n ω) 3 P ≤
          ∑ n ∈ Finset.range k, eLpNorm' (X n) 3 P := by
        apply eLpNorm'_sum_le
        · intro n hn
          exact hX n
        · norm_num
      _ ≤ B := ENNReal.sum_le_tsum _
  have hpartialInt (k : ℕ) :
      (∫⁻ ω, (S k ω) ^ (3 : ℝ) ∂P) ≤ B ^ (3 : ℝ) := by
    have hEq : (∫⁻ ω, (S k ω) ^ (3 : ℝ) ∂P) =
        (eLpNorm' (S k) 3 P) ^ (3 : ℝ) := by
      simpa only [enorm_eq_self] using
        (lintegral_rpow_enorm_eq_rpow_eLpNorm' (f := S k) (μ := P)
          (by norm_num : (0 : ℝ) < 3))
    rw [hEq]
    exact ENNReal.rpow_le_rpow (hpartial k) (by norm_num)
  have hpowlim (ω : Ω) :
      (atTop.liminf (fun k => S k ω)) ^ (3 : ℝ) =
        atTop.liminf (fun k => (S k ω) ^ (3 : ℝ)) := by
    have hm := ENNReal.strictMono_rpow_of_pos (by norm_num : (0 : ℝ) < 3)
    have hs := (ENNReal.rpow_left_bijective (by norm_num : (3 : ℝ) ≠ 0)).2
    refine (hm.orderIsoOfSurjective _ hs).liminf_apply ?_ ?_ ?_ ?_
    all_goals isBoundedDefault
  have hIntegral :
      (∫⁻ ω, (∑' n, X n ω) ^ (3 : ℝ) ∂P) ≤ B ^ (3 : ℝ) := by
    calc
      (∫⁻ ω, (∑' n, X n ω) ^ (3 : ℝ) ∂P) =
          ∫⁻ ω, atTop.liminf (fun k => (S k ω) ^ (3 : ℝ)) ∂P := by
        apply lintegral_congr
        intro ω
        rw [ENNReal.tsum_eq_liminf_sum_nat]
        exact hpowlim ω
      _ ≤ atTop.liminf (fun k => ∫⁻ ω, (S k ω) ^ (3 : ℝ) ∂P) := by
        apply lintegral_liminf_le'
        intro k
        exact (hS k).enorm.pow_const _
      _ ≤ B ^ (3 : ℝ) :=
        liminf_le_of_frequently_le' (Filter.Frequently.of_forall hpartialInt)
  rw [one_div, ← ENNReal.le_rpow_inv_iff (by norm_num : 0 < (3 : ℝ)⁻¹), inv_inv]
  exact hIntegral

/-- The `L³` norm of a countable coordinate square sum is controlled by the
sum of the squared `L⁶` norms of its coordinates. -/
theorem fp81s21_tsum_square_l3_minkowski
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ)
    (hX : ∀ n, AEStronglyMeasurable (X n) P) :
    (∫⁻ ω, (∑' n, ‖X n ω‖ₑ ^ (2 : ℝ)) ^ (3 : ℝ) ∂P) ^ (1 / 3 : ℝ) ≤
      ∑' n, (eLpNorm' (X n) 6 P) ^ (2 : ℝ) := by
  have hpow : ∀ n, AEStronglyMeasurable (fun ω => ‖X n ω‖ₑ ^ (2 : ℝ)) P := by
    intro n
    exact ENNReal.continuous_rpow_const.comp_aestronglyMeasurable
      (hX n).enorm.aestronglyMeasurable
  calc
    (∫⁻ ω, (∑' n, ‖X n ω‖ₑ ^ (2 : ℝ)) ^ (3 : ℝ) ∂P) ^ (1 / 3 : ℝ) ≤
        ∑' n, eLpNorm' (fun ω => ‖X n ω‖ₑ ^ (2 : ℝ)) 3 P :=
      fp81s21_tsum_l3_minkowski P (fun n ω => ‖X n ω‖ₑ ^ (2 : ℝ)) hpow
    _ = ∑' n, (eLpNorm' (X n) 6 P) ^ (2 : ℝ) := by
      congr 1
      funext n
      simpa only [show (3 : ℝ) * 2 = 6 by norm_num] using
        (eLpNorm'_enorm_rpow (X n) 3 2 (by norm_num) (μ := P))

#print axioms HRS.Fp81.S21.fp81s21_finite_sum_l3_minkowski
#print axioms HRS.Fp81.S21.fp81s21_tsum_l3_minkowski
#print axioms HRS.Fp81.S21.fp81s21_tsum_square_l3_minkowski
end HRS.Fp81.S21
end
