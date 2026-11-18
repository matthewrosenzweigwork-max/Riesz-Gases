import HRS.MS.Fp81S21GaussG4U8F
import HRS.MS.Fp81S21GaussG4U3
import HRS.MS.Fp81S21GaussIncrement

/-! Conditional physical chart increment bound. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.S111X2 HRS.MS.ProClosureS111

/-- U8 and the centered initial comparison imply the physical chart bound. -/
theorem fp81s21_g4_physical (p : Parameters)
    (hU8 : fp81s21_g4Phys p (fun _ R =>
      ∃ A : ℝ, 0 ≤ A ∧ ∀ f, IsR2Test f → ∀ v w : ℝ, 0 ≤ v → v ≤ w →
        fp81s21_g4_initialValue R f v w ≤ A * (w-v)^2 * fp81s21_g4_J p.d f ∧
        fp81s21_g4_Old R f v w ≤ A * (w-v)^2 * fp81s21_g4_J p.d f ∧
        fp81s21_g4_New R f v w ≤ A * ((w-v)+(w-v)^2) * fp81s21_g4_J p.d f ∧
        ‖movingNoiseFeature R 0 w f - movingNoiseFeature R 0 v f‖^2 ≤
          A * ((w-v)+(w-v)^2) * fp81s21_g4_J p.d f))
    (hU84 : ∀ {δ : ℝ} (R : Trajectory p δ), 0 < δ → δ ≤ 1 / 2 →
      letI : IsProbabilityMeasure (r26t3_mu R 0) := fp81s21_initialMeasure_isProbability p R
      ∀ {Mg : ℝ} {K : Lp ℝ 2 (r26t3_mu R 0) →L[ℝ] Lp ℝ 2 (r26t3_mu R 0)}
        (hK : KRep (rieszKernel p.d p.s) (r26t3_mu R 0) K Mg)
        {f : Euc p.d → ℝ}, IsOscTest (wholeSpaceIndex p.d : ℝ) f →
        ∀ {v w : ℝ}, 0 ≤ v → v ≤ w →
          ‖fp81s21_initialGaussianFeature p R hK w f -
            fp81s21_initialGaussianFeature p R hK v f‖^2 ≤
              p.C₁ * fp81s21_g4_initialValue R f v w) :
    fp81s21_g4Phys p (fun _ R =>
      letI : IsProbabilityMeasure (r26t3_mu R 0) := fp81s21_initialMeasure_isProbability p R
      ∃ Mg : ℝ, ∃ K : Lp ℝ 2 (r26t3_mu R 0) →L[ℝ] Lp ℝ 2 (r26t3_mu R 0),
      ∃ hK : KRep (rieszKernel p.d p.s) (r26t3_mu R 0) K Mg,
      ∀ E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2),
      ∀ H : ℝ, 0 < H → ∃ l : ℕ → ℝ,
        (∀ j, 0 ≤ l j) ∧ Summable l ∧
        ∀ a : ℝ, 0 ≤ a → ∀ s ∈ Icc (0 : ℝ) H, ∀ t ∈ Icc (0 : ℝ) H, ∀ j,
          ‖fp81s21_combinedFeature p R hK (a+t) (E.test j) -
            fp81s21_combinedFeature p R hK (a+s) (E.test j)‖^2 ≤ l j * |t-s|) := by
  obtain ⟨δ0, hδ0, hδhalf, hR⟩ := hU8
  refine ⟨δ0, hδ0, hδhalf, ?_⟩
  intro δ hδ hδle R
  letI : IsProbabilityMeasure (r26t3_mu R 0) := fp81s21_initialMeasure_isProbability p R
  have hhalf : δ ≤ 1 / 2 := hδle.trans hδhalf
  have hC : 0 ≤ p.C₁ := (fp81s21_g4_density_comparison p R hδ hhalf).1.le
  obtain ⟨A, hA, hpieces⟩ := hR δ hδ hδle R
  obtain ⟨Mg, K, hK⟩ := fp81s21_actualInitialKRep_exists p hδ hhalf R
  refine ⟨Mg, K, hK, ?_⟩
  intro E H hH
  let l : ℕ → ℝ := fun j => A * (1+p.C₁) * (1+H) * fp81s21_g4_J p.d (E.test j)
  have hcoef : 0 ≤ A * (1+p.C₁) * (1+H) := by positivity
  refine ⟨l, ?_, ?_, ?_⟩
  · intro j
    exact mul_nonneg hcoef (sq_nonneg _)
  · exact (fp81s21_g4_cost_trace p E).mul_left _
  · intro a ha s hs t ht j
    have hJ : 0 ≤ fp81s21_g4_J p.d (E.test j) := sq_nonneg _
    have hordered : ∀ x y : ℝ, x ∈ Icc (0 : ℝ) H → y ∈ Icc (0 : ℝ) H → x ≤ y →
        ‖fp81s21_combinedFeature p R hK (a+y) (E.test j) -
          fp81s21_combinedFeature p R hK (a+x) (E.test j)‖^2 ≤ l j * (y-x) := by
      intro x y hx hy hxy
      have hd : 0 ≤ y-x := sub_nonneg.mpr hxy
      have hdH : y-x ≤ H := by linarith [hx.1, hy.2]
      have hd2 : (y-x)^2 ≤ H * (y-x) := by nlinarith [mul_le_mul_of_nonneg_right hdH hd]
      have hv : 0 ≤ a+x := add_nonneg ha hx.1
      have hvw : a+x ≤ a+y := by linarith
      obtain ⟨hi, _, _, hn⟩ := hpieces (E.test j) (E.test_smooth j) (a+x) (a+y) hv hvw
      have hin := hU84 R hδ hhalf hK (r2Test_isOscTest _ (E.test_smooth j)) hv hvw
      have hin' := mul_le_mul_of_nonneg_left hi hC
      have hd2J := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd2 hA) hJ
      have hnoiseJ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (add_le_add_left hd2 (y-x)) hA) hJ
      have hextra : 0 ≤ A * p.C₁ * (y-x) * fp81s21_g4_J p.d (E.test j) := by positivity
      rw [fp81s21_combinedFeature_increment_parts]
      dsimp [l]
      simp only [show a+y-(a+x) = y-x by ring] at hi hn hin'
      nlinarith
    rcases le_total s t with hst | hts
    · simpa [abs_of_nonneg (sub_nonneg.mpr hst)] using hordered s t hs ht hst
    · have hrev := hordered t s ht hs hts
      rw [norm_sub_rev] at hrev
      simpa [abs_of_nonpos (sub_nonpos.mpr hts)] using hrev

#print axioms fp81s21_g4_physical
end HRS.Fp81.S21
end
