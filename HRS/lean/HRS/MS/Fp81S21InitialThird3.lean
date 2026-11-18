import HRS.MS.Fp81S21InitialThird2

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section

namespace HRS.Fp81.S21

open S45 S99
open HRS.Whole
open HRS (Euc)
open HRS.MS.R26T3

/-- Integrate the pointwise third expansion against the actual initial law.
The response envelope justifies the entire first triple-series interchange. -/
theorem fp81s21_initial_third_inner
    {p : Parameters} {δ : ℝ} (R : Trajectory p δ)
    (E : InitialSteinEnv R) {φ : ℕ → Euc p.d → ℝ}
    (hφ : IsSummableFeatureFamily (fp81s21_J1 p.d) φ)
    (F : InitialFamData R φ) {Φ' : SeqL2 → ℝ}
    (hΦ : ContDiff ℝ 3 Φ')
    (hD : ∀ z, ‖iteratedFDeriv ℝ 3 Φ' z‖ ≤ 1) (z : SeqL2) :
    ∫ x, iteratedFDeriv ℝ 3 Φ' z
        ![fp81s21_initial_ellv R φ x, fp81s21_initial_ellv R φ x,
          fp81s21_initial_ellv R φ x] ∂(r26t3_mu R 0) =
      ∑' j, ∑' k, ∑' m, fp81s21_initial_kap3 R φ j k m *
        iteratedFDeriv ℝ 3 Φ' z
          ![s45_e1 m (1 : ℝ), s45_e1 k (1 : ℝ), s45_e1 j (1 : ℝ)] := by
  haveI hμ : IsProbabilityMeasure (r26t3_mu R 0) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu E.reference.prob
  let b : ℕ → ℝ := fun j => cbNorm (fp81s21_J1 p.d) (φ j)
  let B : ℕ → ℝ := fun j => F.K * b j
  have hb0 : ∀ j, 0 ≤ B j := fun j => mul_nonneg F.hK (by
    dsimp [b]
    exact HRS.MS.Tc5.tc5_cb_nonneg _ _)
  have hbs : Summable B := hφ.2.mul_left _
  have ha : ∀ j x, |r26t3_a R (φ j) x| ≤ B j := by
    intro j x
    have hs := HRS.MS.Tc5.tc5_cb_sup_le (F.amem j) x
    calc
      |r26t3_a R (φ j) x| ≤ cbNorm (fp81s21_k0 p.d) (r26t3_a R (φ j)) := by
        simpa [Real.norm_eq_abs] using hs
      _ ≤ B j := by simpa [B, b] using F.anorm j
  let t : ℕ → ℕ → ℕ → ℝ := fun j k m =>
    iteratedFDeriv ℝ 3 Φ' z ![s45_e1 m (1 : ℝ), s45_e1 k (1 : ℝ), s45_e1 j (1 : ℝ)]
  have htb : ∀ j k m, |t j k m| ≤ 1 := by
    intro j k m
    simp only [t]
    rw [← Real.norm_eq_abs]
    refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
    simp only [Fin.prod_univ_three]
    simp [s99_e1_norm]
    exact hD z
  have hpt : ∀ x, iteratedFDeriv ℝ 3 Φ' z
      ![fp81s21_initial_ellv R φ x, fp81s21_initial_ellv R φ x,
        fp81s21_initial_ellv R φ x] =
      ∑' j, ∑' k, ∑' m,
        r26t3_a R (φ j) x * r26t3_a R (φ k) x * r26t3_a R (φ m) x * t j k m := by
    intro x
    exact fp81s21_initial_third_expand R hφ F (iteratedFDeriv ℝ 3 Φ' z) x
  let g : ℕ → ℕ → ℕ → Euc p.d → ℝ := fun j k m x =>
    r26t3_a R (φ j) x * r26t3_a R (φ k) x * r26t3_a R (φ m) x * t j k m
  have hg : ∀ j k m x, |g j k m x| ≤ B j * B k * B m := by
    intro j k m x
    dsimp [g]
    rw [abs_mul, abs_mul, abs_mul]
    calc
      |r26t3_a R (φ j) x| * |r26t3_a R (φ k) x| *
          |r26t3_a R (φ m) x| * |t j k m| ≤ B j * B k * B m * 1 := by
            exact mul_le_mul
              (mul_le_mul
                (mul_le_mul (ha j x) (ha k x) (abs_nonneg _) (hb0 j))
                (ha m x) (abs_nonneg _) (mul_nonneg (hb0 j) (hb0 k)))
              (htb j k m) (abs_nonneg _)
              (mul_nonneg (mul_nonneg (hb0 j) (hb0 k)) (hb0 m))
      _ = _ := by ring
  have hm : ∀ j k m, Measurable (g j k m) := by
    intro j k m
    dsimp [g]
    exact ((((F.amem j).1.continuous.mul (F.amem k).1.continuous).mul
      (F.amem m).1.continuous).mul continuous_const).measurable
  simp_rw [hpt]
  rw [S99.s99_int_tsum3 g hbs hb0 hg hm]
  refine tsum_congr fun j => tsum_congr fun k => tsum_congr fun m => ?_
  rw [integral_mul_const]
  rfl

#print axioms fp81s21_initial_third_inner

end HRS.Fp81.S21

end
