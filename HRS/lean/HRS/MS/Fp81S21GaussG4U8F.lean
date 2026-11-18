import HRS.MS.Fp81S21GaussG4U854
import HRS.MS.Fp81S21GaussG4U72
import HRS.MS.ProClosureS111PhysicalWick

/-! Conditional compact-test G4 pieces, including moving noise. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.ProClosureS111

/-- The U82 compact reference estimates imply the full compact pieces. -/
theorem fp81s21_g4_compact_pieces (p : Parameters)
    (hU82 : fp81s21_g4Phys p (fun _ R =>
      ∃ A : ℝ, 0 ≤ A ∧
        ∀ f, IsR2Test f → ∀ v w : ℝ, 0 ≤ v → v ≤ w →
          fp81s21_g4_initialValue R f v w ≤ A * (w-v)^2 * fp81s21_g4_J p.d f ∧
          fp81s21_g4_Old R f v w ≤ A * (w-v)^2 * fp81s21_g4_J p.d f ∧
          fp81s21_g4_New R f v w ≤ A * ((w-v)+(w-v)^2) * fp81s21_g4_J p.d f)) :
    fp81s21_g4Phys p (fun _ R =>
      ∃ A : ℝ, 0 ≤ A ∧
        ∀ f, IsR2Test f → ∀ v w : ℝ, 0 ≤ v → v ≤ w →
          fp81s21_g4_initialValue R f v w ≤ A * (w-v)^2 * fp81s21_g4_J p.d f ∧
          fp81s21_g4_Old R f v w ≤ A * (w-v)^2 * fp81s21_g4_J p.d f ∧
          fp81s21_g4_New R f v w ≤ A * ((w-v)+(w-v)^2) * fp81s21_g4_J p.d f ∧
          ‖movingNoiseFeature R 0 w f - movingNoiseFeature R 0 v f‖^2 ≤
            A * ((w-v)+(w-v)^2) * fp81s21_g4_J p.d f) := by
  obtain ⟨δ0, hδ0, hδhalf, hR⟩ := hU82
  refine ⟨δ0, hδ0, hδhalf, ?_⟩
  intro δ hδ hδle R
  have hhalf : δ ≤ 1 / 2 := hδle.trans hδhalf
  obtain ⟨A, hA, hpieces⟩ := hR δ hδ hδle R
  let c : ℝ := 2 * p.β⁻¹ * p.C₁
  have hc : 0 ≤ c := mul_nonneg (mul_nonneg (by norm_num) (inv_nonneg.mpr p.hβ.le))
    (fp81s21_g4_density_comparison p R hδ hhalf).1.le
  let B : ℝ := max A (c * (A+A))
  have hAB : A ≤ B := le_max_left _ _
  have hcB : c * (A+A) ≤ B := le_max_right _ _
  have hB : 0 ≤ B := hA.trans hAB
  refine ⟨B, hB, ?_⟩
  intro f hf v w hv hvw
  have hJ : 0 ≤ fp81s21_g4_J p.d f := sq_nonneg _
  have hd : 0 ≤ w-v := sub_nonneg.mpr hvw
  have hs : 0 ≤ (w-v)^2 := sq_nonneg _
  have hdS : 0 ≤ (w-v)+(w-v)^2 := add_nonneg hd hs
  obtain ⟨hi, ho, hn⟩ := hpieces f hf v w hv hvw
  have hnoise := (fp81s21_g4_noise_increment_reference p R hδ hhalf
    (r2Test_isOscTest (wholeSpaceIndex p.d : ℝ) hf) hv hvw).2
  have hmonoS : A * (w-v)^2 * fp81s21_g4_J p.d f ≤
      B * (w-v)^2 * fp81s21_g4_J p.d f :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAB hs) hJ
  have hmonoD : A * ((w-v)+(w-v)^2) * fp81s21_g4_J p.d f ≤
      B * ((w-v)+(w-v)^2) * fp81s21_g4_J p.d f :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAB hdS) hJ
  have ho' : fp81s21_g4_Old R f v w ≤
      A * ((w-v)+(w-v)^2) * fp81s21_g4_J p.d f := by
    apply ho.trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by linarith) hA) hJ
  refine ⟨hi.trans hmonoS, ho.trans hmonoS, hn.trans hmonoD, ?_⟩
  calc
    _ ≤ c * (fp81s21_g4_Old R f v w + fp81s21_g4_New R f v w) := hnoise
    _ ≤ c * (A * ((w-v)+(w-v)^2) * fp81s21_g4_J p.d f +
      A * ((w-v)+(w-v)^2) * fp81s21_g4_J p.d f) :=
        mul_le_mul_of_nonneg_left (add_le_add ho' hn) hc
    _ = (c * (A+A)) * ((w-v)+(w-v)^2) * fp81s21_g4_J p.d f := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcB hdS) hJ

#print axioms fp81s21_g4_compact_pieces
end HRS.Fp81.S21
end
