import HRS.MS.S111K2B02

/-!
# R26-T6C.I08 — finite Euclidean square sums in L3

The proof uses Minkowski in L^(3/2) for the sum of squares,
followed by the square-root power transformation.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T6C
open HRS HRS.Whole

theorem r26t6c_finite_square_L3 {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P] {iota : Type*}
    (A : Finset iota) (f : iota → Omega → ℝ) (b : iota → ℝ)
    (hb : ∀ i ∈ A, 0 ≤ b i) (hf : ∀ i ∈ A, MemLp (f i) 3 P)
    (hfb : ∀ i ∈ A, eLpNorm (f i) 3 P ≤ ENNReal.ofReal (b i)) :
    MemLp (fun w => Real.sqrt (∑ i ∈ A, |f i w| ^ 2)) 3 P ∧
    eLpNorm (fun w => Real.sqrt (∑ i ∈ A, |f i w| ^ 2)) 3 P ≤
      ENNReal.ofReal (Real.sqrt (∑ i ∈ A, b i ^ 2)) := by
  classical
  let S : Omega → ℝ := fun w => ∑ i ∈ A, |f i w| ^ 2
  let F : Omega → ℝ := fun w => Real.sqrt (S w)
  have hS0 : ∀ w, 0 ≤ S w := fun w =>
    Finset.sum_nonneg fun i hi => sq_nonneg _
  have hB0 : 0 ≤ ∑ i ∈ A, b i ^ 2 :=
    Finset.sum_nonneg fun i hi => sq_nonneg _
  have hSm : AEStronglyMeasurable S P := by
    dsimp [S]
    exact Finset.aestronglyMeasurable_fun_sum _ (fun i hi =>
      (by
        have hfi : AEStronglyMeasurable (fun w => |f i w|) P :=
          continuous_abs.comp_aestronglyMeasurable (hf i hi).aestronglyMeasurable
        have heq : (fun w => |f i w| ^ 2) =
            (fun w => |f i w|) * (fun w => |f i w|) := by
          funext w
          simp [Pi.mul_apply, pow_two]
        rw [heq]
        exact hfi.mul hfi))
  have hFm : AEStronglyMeasurable F P :=
    (Real.continuous_sqrt.comp_aestronglyMeasurable hSm)
  have hF0 : ∀ w, 0 ≤ F w := fun w => Real.sqrt_nonneg _
  have hFsq : ∀ w, F w ^ 2 = S w := fun w => Real.sq_sqrt (hS0 w)
  have hp : (3 / 2 : ℝ≥0∞) * ENNReal.ofReal 2 = 3 := by
    simp only [ENNReal.div_eq_inv_mul, ENNReal.ofReal_ofNat]
    rw [mul_assoc, mul_comm (3 : ℝ≥0∞) 2, ← mul_assoc,
      ENNReal.inv_mul_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (by norm_num : (2 : ℝ≥0∞) ≠ ∞), one_mul]
  have hpower : eLpNorm S (3 / 2 : ℝ≥0∞) P =
      eLpNorm F 3 P ^ (2 : ℝ) := by
    have h := eLpNorm_norm_rpow F hFm (by norm_num : (0 : ℝ) < 2)
      (p := (3 / 2 : ℝ≥0∞))
    rw [hp] at h
    rw [← h]
    refine eLpNorm_congr_ae (ae_of_all _ fun w => ?_)
    simp only [Real.norm_eq_abs, abs_of_nonneg (hF0 w)]
    calc
      S w = F w ^ (2 : ℕ) := (hFsq w).symm
      _ = F w ^ (2 : ℝ) := (Real.rpow_natCast _ 2).symm
  have hi : ∀ i ∈ A, eLpNorm (fun w => |f i w| ^ 2) (3 / 2 : ℝ≥0∞) P =
      eLpNorm (f i) 3 P ^ (2 : ℝ) := by
    intro i hi
    have h := eLpNorm_norm_rpow (f i) (hf i hi).aestronglyMeasurable
      (by norm_num : (0 : ℝ) < 2) (p := (3 / 2 : ℝ≥0∞))
    rw [hp] at h
    simpa [Real.norm_eq_abs] using h
  have hsum : eLpNorm S (3 / 2 : ℝ≥0∞) P ≤
      ∑ i ∈ A, eLpNorm (f i) 3 P ^ (2 : ℝ) := by
    calc
      _ ≤ ∑ i ∈ A, eLpNorm (fun w => |f i w| ^ 2)
          (3 / 2 : ℝ≥0∞) P := by
        have hsumf : S = ∑ i ∈ A, (fun w => |f i w| ^ 2) := by
          funext w
          simp only [S, Finset.sum_apply]
        rw [hsumf]
        exact (eLpNorm_sum_le
          (μ := P) (p := (3 / 2 : ℝ≥0∞))
          (f := fun i w => |f i w| ^ 2) (s := A)
          (by
            simp only [ENNReal.div_eq_inv_mul]
            calc
              (1 : ℝ≥0∞) = 2⁻¹ * 2 := by
                rw [ENNReal.inv_mul_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0)
                  (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]
              _ ≤ 2⁻¹ * 3 := mul_le_mul' le_rfl (by norm_num) : (1 : ℝ≥0∞) ≤ 3 / 2))
      _ = _ := Finset.sum_congr rfl fun i hAi => hi i hAi
  have hbound : eLpNorm F 3 P ^ (2 : ℝ) ≤
      ENNReal.ofReal (∑ i ∈ A, b i ^ 2) := by
    rw [← hpower]
    calc
      _ ≤ ∑ i ∈ A, eLpNorm (f i) 3 P ^ (2 : ℝ) := hsum
      _ ≤ ∑ i ∈ A, ENNReal.ofReal (b i) ^ (2 : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        exact ENNReal.rpow_le_rpow (hfb i hi) (by norm_num)
      _ = ENNReal.ofReal (∑ i ∈ A, b i ^ 2) := by
        calc
          _ = ∑ i ∈ A, ENNReal.ofReal (b i ^ 2) := by
            apply Finset.sum_congr rfl
            intro i hAi
            rw [ENNReal.rpow_two, ENNReal.ofReal_pow (hb i hAi)]
          _ = _ := (ENNReal.ofReal_sum_of_nonneg (fun i hAi => sq_nonneg (b i))).symm
  have hnorm : eLpNorm F 3 P ≤
      ENNReal.ofReal (Real.sqrt (∑ i ∈ A, b i ^ 2)) := by
    calc
      _ = (eLpNorm F 3 P ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
        rw [← ENNReal.rpow_mul]
        norm_num
      _ ≤ (ENNReal.ofReal (∑ i ∈ A, b i ^ 2)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow hbound (by norm_num)
      _ = _ := by
        rw [Real.sqrt_eq_rpow]
        exact (ENNReal.ofReal_rpow_of_nonneg hB0
          (by norm_num : 0 ≤ (1 / 2 : ℝ)))
  have hL : MemLp F 3 P :=
    (memLp_iff).2 (hnorm.trans_lt ENNReal.ofReal_lt_top)
  exact ⟨hL, hnorm⟩

end HRS.MS.R26T6C
