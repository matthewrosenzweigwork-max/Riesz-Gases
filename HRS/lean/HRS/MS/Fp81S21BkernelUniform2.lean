import HRS.MS.Fp81S21BkernelUniform
import HRS.MS.Fp81S21InitialBkernel2

open MeasureTheory
open scoped BigOperators

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section

namespace HRS.Fp81.S21

open S99
open HRS (Euc cbNorm)
open HRS.Whole
open HRS.MS.R26T3

/-- Product-law `L¹` kernel error controls the quadratic-limit error, with
its actual response family and the half in the limit retained. -/
theorem fp81s21_initial_Blimit_l1_bound
    {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    (E : InitialSteinEnv R) {φ : ℕ → Euc p.d → ℝ}
    (hφ : IsSummableFeatureFamily (fp81s21_J1 p.d) φ)
    (F : InitialFamData R φ) {G : Measure SeqL2} [IsProbabilityMeasure G]
    {ψ : SeqL2 → ℝ} (hψ : S99.Bd 4 ψ)
    {h D : Euc p.d → Euc p.d → ℝ}
    (hh : Integrable (Function.uncurry h)
      ((r26t3_mu R 0).prod (r26t3_mu R 0)))
    (hD : Integrable (Function.uncurry D)
      ((r26t3_mu R 0).prod (r26t3_mu R 0)))
    {η : ℝ} (hη : 0 ≤ η)
    (hL1 : (∫ z : Euc p.d × Euc p.d,
      |D z.1 z.2 - h z.1 z.2|
        ∂((r26t3_mu R 0).prod (r26t3_mu R 0))) ≤ η) :
    |fp81s21_initial_Blimit R φ G ψ D -
      fp81s21_initial_Blimit R φ G ψ h| ≤
        (1 / 2) * (F.K ^ 2 * η *
          (featureSum (fp81s21_J1 p.d) φ) ^ 2) := by
  haveI hμ : IsProbabilityMeasure (r26t3_mu R 0) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu E.reference.prob
  let μ : Measure (Euc p.d) := r26t3_mu R 0
  let b : ℕ → ℝ := fun j => cbNorm (fp81s21_J1 p.d) (φ j)
  have hb0 : ∀ j, 0 ≤ b j := fun j => HRS.MS.Tc5.tc5_cb_nonneg _ _
  have hbs : Summable b := hφ.2
  let δ₁ : ℝ := ∫ z : Euc p.d × Euc p.d,
    |D z.1 z.2 - h z.1 z.2| ∂(μ.prod μ)
  have hδ₁0 : 0 ≤ δ₁ := by
    dsimp [δ₁]
    exact integral_nonneg fun z => abs_nonneg _
  have hδ₁le : δ₁ ≤ η := by
    dsimp [δ₁, μ]
    exact hL1
  have hzero : Integrable (Function.uncurry (fun _ _ : Euc p.d => (0 : ℝ)))
      (μ.prod μ) := integrable_const 0
  have hQ0 : ∀ l q,
      fp81s21_initial_Qk R φ (fun _ _ => (0 : ℝ)) l q = 0 := by
    intro l q
    unfold fp81s21_initial_Qk
    simp
  have hQb : ∀ (k : Euc p.d → Euc p.d → ℝ),
      Integrable (Function.uncurry k) (μ.prod μ) →
      ∀ l q, |fp81s21_initial_Qk R φ k l q| ≤
        F.K ^ 2 * (∫ z : Euc p.d × Euc p.d, |k z.1 z.2|
          ∂(μ.prod μ)) * (b l * b q) := by
    intro k hk l q
    have ht := fp81s21_initial_Qk_diff E hφ F hk hzero l q
    rw [hQ0, sub_zero] at ht
    calc
      |fp81s21_initial_Qk R φ k l q| ≤
          (F.K * b l) * (F.K * b q) *
            ∫ z : Euc p.d × Euc p.d, |k z.1 z.2| ∂(μ.prod μ) := by
              simpa [μ] using ht
      _ = F.K ^ 2 *
          (∫ z : Euc p.d × Euc p.d, |k z.1 z.2| ∂(μ.prod μ)) *
            (b l * b q) := by ring
  let Gm : ℕ → ℕ → ℝ := fun l q =>
    ∫ z, S99.pd (S99.pd ψ l) q z ∂G
  have hGb : ∀ l q, |Gm l q| ≤ 1 := by
    intro l q
    have ht := norm_integral_le_of_norm_le_const (μ := G)
      (f := S99.pd (S99.pd ψ l) q) (C := 1)
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs]
        exact ((hψ.pd l).pd q).abs_le z)
    simpa [Real.norm_eq_abs, Gm] using ht
  have hsumDiff := S99.s99_tsum2_sub hb0 hbs
    (A1 := F.K ^ 2 *
      (∫ z : Euc p.d × Euc p.d, |D z.1 z.2| ∂(μ.prod μ)))
    (A2 := F.K ^ 2 *
      (∫ z : Euc p.d × Euc p.d, |h z.1 z.2| ∂(μ.prod μ)))
    (D := F.K ^ 2 * δ₁)
    (f := fun l q => fp81s21_initial_Qk R φ D l q * Gm l q)
    (g := fun l q => fp81s21_initial_Qk R φ h l q * Gm l q)
    (fun l q => by
      rw [abs_mul]
      calc
        |fp81s21_initial_Qk R φ D l q| * |Gm l q|
            ≤ |fp81s21_initial_Qk R φ D l q| * 1 :=
              mul_le_mul_of_nonneg_left (hGb l q) (abs_nonneg _)
        _ ≤ _ := by
          rw [mul_one]
          exact hQb D hD l q)
    (fun l q => by
      rw [abs_mul]
      calc
        |fp81s21_initial_Qk R φ h l q| * |Gm l q|
            ≤ |fp81s21_initial_Qk R φ h l q| * 1 :=
              mul_le_mul_of_nonneg_left (hGb l q) (abs_nonneg _)
        _ ≤ _ := by
          rw [mul_one]
          exact hQb h hh l q)
    (fun l q => by
      rw [← sub_mul, abs_mul]
      have hq := fp81s21_initial_Qk_diff E hφ F hD hh l q
      have hδeq : (∫ z : Euc p.d × Euc p.d,
          |D z.1 z.2 - h z.1 z.2| ∂((r26t3_mu R 0).prod (r26t3_mu R 0))) = δ₁ := by
        rfl
      rw [hδeq] at hq
      have hq' :
          |fp81s21_initial_Qk R φ D l q -
            fp81s21_initial_Qk R φ h l q| ≤
          (F.K * b l) * (F.K * b q) * δ₁ := hq
      calc
        |fp81s21_initial_Qk R φ D l q -
            fp81s21_initial_Qk R φ h l q| * |Gm l q|
            ≤ |fp81s21_initial_Qk R φ D l q -
                fp81s21_initial_Qk R φ h l q| * 1 :=
              mul_le_mul_of_nonneg_left (hGb l q) (abs_nonneg _)
        _ ≤ _ := by
          rw [mul_one]
          calc
            |fp81s21_initial_Qk R φ D l q -
                fp81s21_initial_Qk R φ h l q|
                ≤ (F.K * b l) * (F.K * b q) * δ₁ := hq'
            _ = F.K ^ 2 * δ₁ * (b l * b q) := by ring)
  have hSb : (∑' j, b j) = featureSum (fp81s21_J1 p.d) φ := by
    rfl
  rw [fp81s21_initial_Blimit, fp81s21_initial_Blimit]
  rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have hS0 : 0 ≤ (∑' j, b j) := tsum_nonneg hb0
  have hboundDelta : F.K ^ 2 * δ₁ * (∑' j, b j) ^ 2 ≤
      F.K ^ 2 * η * (∑' j, b j) ^ 2 := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hδ₁le (sq_nonneg F.K)) (sq_nonneg (∑' j, b j))
  calc
    (1 / 2) *
      |∑' l, ∑' q, fp81s21_initial_Qk R φ D l q * Gm l q -
        ∑' l, ∑' q, fp81s21_initial_Qk R φ h l q * Gm l q|
        ≤ (1 / 2) * (F.K ^ 2 * δ₁ * (∑' j, b j) ^ 2) :=
          mul_le_mul_of_nonneg_left hsumDiff (by norm_num)
    _ ≤ (1 / 2) * (F.K ^ 2 * η * (∑' j, b j) ^ 2) :=
          mul_le_mul_of_nonneg_left hboundDelta (by norm_num)
    _ = (1 / 2) * (F.K ^ 2 * η *
          (featureSum (fp81s21_J1 p.d) φ) ^ 2) := by rw [hSb]

#print axioms fp81s21_initial_Blimit_l1_bound

end HRS.Fp81.S21

end
