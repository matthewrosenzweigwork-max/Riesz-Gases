import HRS.MS.Fp81S21InitialThird3

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

/-- Interchange the outer Gaussian integral with the actual cubic series.
The coefficient bound and derivative bound give the same summable response envelope. -/
theorem fp81s21_initial_third_outer
    {p : Parameters} {δ : ℝ} (R : Trajectory p δ)
    (E : InitialSteinEnv R) {φ : ℕ → Euc p.d → ℝ}
    (hφ : IsSummableFeatureFamily (fp81s21_J1 p.d) φ)
    (F : InitialFamData R φ) {G : Measure SeqL2} [IsProbabilityMeasure G]
    {Φ' : SeqL2 → ℝ} (hΦ : ContDiff ℝ 3 Φ')
    (hD : ∀ z, ‖iteratedFDeriv ℝ 3 Φ' z‖ ≤ 1) :
    ∫ z, ∑' j, ∑' k, ∑' m,
        fp81s21_initial_kap3 R φ j k m *
          iteratedFDeriv ℝ 3 Φ' z
            ![s45_e1 m (1 : ℝ), s45_e1 k (1 : ℝ), s45_e1 j (1 : ℝ)] ∂G =
      ∑' j, ∑' k, ∑' m, fp81s21_initial_kap3 R φ j k m *
        ∫ z, iteratedFDeriv ℝ 3 Φ' z
          ![s45_e1 m (1 : ℝ), s45_e1 k (1 : ℝ), s45_e1 j (1 : ℝ)] ∂G := by
  let b : ℕ → ℝ := fun j => cbNorm (fp81s21_J1 p.d) (φ j)
  let B : ℕ → ℝ := fun j => F.K * b j
  have hb0 : ∀ j, 0 ≤ B j := fun j => mul_nonneg F.hK (by
    dsimp [b]
    exact HRS.MS.Tc5.tc5_cb_nonneg _ _)
  have hbs : Summable B := hφ.2.mul_left _
  have hkap : ∀ j k m,
      |fp81s21_initial_kap3 R φ j k m| ≤ B j * B k * B m := by
    intro j k m
    have hk := fp81s21_initial_kap3_bound E hφ F j k m
    calc
      |fp81s21_initial_kap3 R φ j k m| ≤
          F.K ^ 3 * (b j * b k * b m) := by simpa [b] using hk
      _ = B j * B k * B m := by dsimp [B]; ring
  let t : SeqL2 → ℕ → ℕ → ℕ → ℝ := fun z j k m =>
    iteratedFDeriv ℝ 3 Φ' z ![s45_e1 m (1 : ℝ), s45_e1 k (1 : ℝ), s45_e1 j (1 : ℝ)]
  have htb : ∀ z j k m, |t z j k m| ≤ 1 := by
    intro z j k m
    simp only [t]
    rw [← Real.norm_eq_abs]
    refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
    simp only [Fin.prod_univ_three]
    simp [s99_e1_norm]
    exact hD z
  have htc : ∀ j k m, Continuous (fun z => t z j k m) := by
    intro j k m
    simp only [t]
    exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 3 => SeqL2) ℝ _).continuous.comp
      (hΦ.continuous_iteratedFDeriv (by norm_num))
  let g : ℕ → ℕ → ℕ → SeqL2 → ℝ := fun j k m z =>
    fp81s21_initial_kap3 R φ j k m * t z j k m
  have hg : ∀ j k m z, |g j k m z| ≤ B j * B k * B m := by
    intro j k m z
    dsimp [g]
    rw [abs_mul]
    calc
      |fp81s21_initial_kap3 R φ j k m| * |t z j k m| ≤
          (B j * B k * B m) * 1 := by
            exact mul_le_mul (hkap j k m) (htb z j k m) (abs_nonneg _)
              (mul_nonneg (mul_nonneg (hb0 j) (hb0 k)) (hb0 m))
      _ = _ := by ring
  have hm : ∀ j k m, Measurable (g j k m) := by
    intro j k m
    dsimp [g]
    exact (continuous_const.mul (htc j k m)).measurable
  rw [S99.s99_int_tsum3 g hbs hb0 hg hm]
  refine tsum_congr fun j => tsum_congr fun k => tsum_congr fun m => ?_
  rw [integral_const_mul]

#print axioms fp81s21_initial_third_outer

end HRS.Fp81.S21

end
