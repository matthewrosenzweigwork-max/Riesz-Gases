import HRS.MS.Fp81S21GaussG4U853
import HRS.MS.Fp81S21GaussG4U5
import HRS.MS.Fp81S21GaussG4U6

/-! Domination of the moving-density noise by the reference energies. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3

private theorem fp81s21_g4_moving_time_integrable
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    {f : Euc p.d → ℝ} (hf : IsOscTest (wholeSpaceIndex p.d : ℝ) f)
    {v w : ℝ} (hv : 0 ≤ v) (hvw : v ≤ w) :
    IntegrableOn (fun r => ∫ x,
      ‖gradient (r26t3_U R r w f) x - gradient (r26t3_U R r v f) x‖^2
        ∂r26t3_mu R r) (Icc (0 : ℝ) v) ∧
    IntegrableOn (fun r => ∫ x, ‖gradient (r26t3_U R r w f) x‖^2
        ∂r26t3_mu R r) (Icc v w) := by
  let F : ℝ × Euc p.d → ℝ := fun q =>
    ‖movingNoiseKernel R 0 w f q - movingNoiseKernel R 0 v f q‖^2
  let G : ℝ → ℝ := fun r => ∫ x, F (r, x)
  let A : ℝ → ℝ := fun r => ∫ x,
    ‖gradient (r26t3_U R r w f) x - gradient (r26t3_U R r v f) x‖^2
      ∂r26t3_mu R r
  let B : ℝ → ℝ := fun r => ∫ x,
    ‖gradient (r26t3_U R r w f) x‖^2 ∂r26t3_mu R r
  let c : ℝ := 2 * p.β⁻¹
  have hc : c ≠ 0 := mul_ne_zero (by norm_num) (inv_ne_zero (ne_of_gt p.hβ))
  have hG : Integrable G :=
    (fp81s21_g4_noise_kernel_difference_integrable p R hδ hδhalf hf hv hvw).integral_prod_left
  have hreg := fp81s21_g4_noise_kernel_regions p R hv hvw (f := f)
  have hrow (r : ℝ) (hr : 0 ≤ r) (g : Euc p.d → ℝ) :
      (∫ x, g x * R.ρ r x) = ∫ x, g x ∂r26t3_mu R r := by
    have hρm : Measurable (R.ρ r) := (R.resulting.regular r hr).measurable
    have hρ0 : ∀ x, 0 ≤ R.ρ r x := by
      intro x
      exact ((R.resulting.global (r + 1)).density r ⟨hr, by linarith⟩).nonneg x
    have hh := HRS.MP.RdRem.mrr_integral_withDensityReal (R.ρ r) hρm hρ0 g
    change (∫ x, g x * R.ρ r x) = ∫ x, g x ∂HRS.Whole.withDensityReal (R.ρ r)
    rw [hh]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => mul_comm _ _
  have hA : ∀ r ∈ Icc (0 : ℝ) v, G r = c * A r := by
    intro r hr
    dsimp [G, F, c, A]
    calc
      _ = ∫ x, (2 * p.β⁻¹) *
          (‖gradient (r26t3_U R r w f) x - gradient (r26t3_U R r v f) x‖^2 * R.ρ r x) := by
            apply integral_congr_ae
            exact Eventually.of_forall (hreg.1 r hr)
      _ = _ := by rw [integral_const_mul, hrow r hr.1]
  have hB : ∀ r ∈ Ioc v w, G r = c * B r := by
    intro r hr
    dsimp [G, F, c, B]
    calc
      _ = ∫ x, (2 * p.β⁻¹) *
          (‖gradient (r26t3_U R r w f) x‖^2 * R.ρ r x) := by
            apply integral_congr_ae
            exact Eventually.of_forall (hreg.2.1 r hr)
      _ = _ := by rw [integral_const_mul, hrow r (hv.trans hr.1.le)]
  have hscale : Integrable (fun r => c⁻¹ * G r) := hG.const_mul _
  constructor
  · apply hscale.integrableOn.congr_fun _ measurableSet_Icc
    intro r hr
    change c⁻¹ * G r = A r
    rw [hA r hr]
    simp [hc, mul_assoc]
  · apply (integrableOn_Icc_iff_integrableOn_Ioc).2
    apply hscale.integrableOn.congr_fun _ measurableSet_Ioc
    intro r hr
    change c⁻¹ * G r = B r
    rw [hB r hr]
    simp [hc, mul_assoc]

/-- Exact moving-density increment and its reference-energy bound. -/
theorem fp81s21_g4_noise_increment_reference
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    {f : Euc p.d → ℝ} (hf : IsOscTest (wholeSpaceIndex p.d : ℝ) f)
    {v w : ℝ} (hv : 0 ≤ v) (hvw : v ≤ w) :
    (‖movingNoiseFeature R 0 w f - movingNoiseFeature R 0 v f‖^2 =
      2 * p.β⁻¹ *
        ((∫ r in Icc (0 : ℝ) v, ∫ x,
          ‖gradient (r26t3_U R r w f) x - gradient (r26t3_U R r v f) x‖^2
            ∂r26t3_mu R r) +
         (∫ r in Icc v w, ∫ x,
          ‖gradient (r26t3_U R r w f) x‖^2 ∂r26t3_mu R r))) ∧
    ‖movingNoiseFeature R 0 w f - movingNoiseFeature R 0 v f‖^2 ≤
      (2 * p.β⁻¹ * p.C₁) * (fp81s21_g4_Old R f v w + fp81s21_g4_New R f v w) := by
  have heq := fp81s21_g4_noise_increment_moving p R hδ hδhalf hf hv hvw
  refine ⟨heq, ?_⟩
  obtain ⟨hmo, hmn⟩ := fp81s21_g4_moving_time_integrable p R hδ hδhalf hf hv hvw
  obtain ⟨hro, hrn⟩ := fp81s21_g4_reference_time_integrable p R hf hv hvw
  have ho := fp81s21_g4_density_time_integral_le p R hδ hδhalf (a := 0) (b := v)
    (g := fun r x => ‖gradient (r26t3_U R r w f) x - gradient (r26t3_U R r v f) x‖^2)
    (le_refl 0) (fun _ _ => sq_nonneg _) (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      exact ((fp81s21_g4_gradient_reference_memLp p R hf hr.1 (hr.2.trans hvw)).sub
        (fp81s21_g4_gradient_reference_memLp p R hf hr.1 hr.2)).integrable_norm_pow (by norm_num)) hmo hro
  have hn := fp81s21_g4_density_time_integral_le p R hδ hδhalf (a := v) (b := w)
    (g := fun r x => ‖gradient (r26t3_U R r w f) x‖^2)
    hv (fun _ _ => sq_nonneg _) (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      exact (fp81s21_g4_gradient_reference_memLp p R hf (hv.trans hr.1) hr.2).integrable_norm_pow (by norm_num)) hmn hrn
  rw [heq]
  unfold fp81s21_g4_Old fp81s21_g4_New
  have hc : 0 ≤ 2 * p.β⁻¹ := mul_nonneg (by norm_num) (inv_nonneg.mpr p.hβ.le)
  have hscaled := mul_le_mul_of_nonneg_left (add_le_add ho hn) hc
  nlinarith

#print axioms fp81s21_g4_noise_increment_reference
end HRS.Fp81.S21
end
