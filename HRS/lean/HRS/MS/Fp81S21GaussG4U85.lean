import HRS.MS.Fp81S21MovingNoise
import HRS.MS.Fp81S21GaussG4U83

/-! The space-time representation and measure comparison for G4 noise. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal RealInnerProductSpace
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3

/-- The noise increment is the squared space-time norm of the kernel difference. -/
theorem fp81s21_g4_noise_increment_kernel
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    {f : Euc p.d → ℝ} (hf : IsOscTest (wholeSpaceIndex p.d : ℝ) f)
    {v w : ℝ} (hv : 0 ≤ v) (hvw : v ≤ w) :
    ‖movingNoiseFeature R 0 w f - movingNoiseFeature R 0 v f‖^2 =
      ∫ q, ‖movingNoiseKernel R 0 w f q - movingNoiseKernel R 0 v f q‖^2
        ∂((volume : Measure ℝ).prod (volume : Measure (Euc p.d))) := by
  let μ : Measure (ℝ × Euc p.d) :=
    (volume : Measure ℝ).prod (volume : Measure (Euc p.d))
  have hT : 0 < w + 1 := by linarith
  have hvT : v ∈ Icc (0 : ℝ) (w + 1) := ⟨hv, by linarith⟩
  have hwT : w ∈ Icc (0 : ℝ) (w + 1) := ⟨hv.trans hvw, by linarith⟩
  have hmemW := (movingNoiseFeature_spec p R hδ hδhalf hT).1 0
    ⟨le_rfl, hT.le⟩ w hwT f hf
  have hmemV := (movingNoiseFeature_spec p R hδ hδhalf hT).1 0
    ⟨le_rfl, hT.le⟩ v hvT f hf
  have hfeatureW : (movingNoiseFeature R 0 w f : ℝ × Euc p.d → Euc p.d) =ᵐ[μ]
      movingNoiseKernel R 0 w f := by
    rw [movingNoiseFeature, dif_pos hmemW]
    exact hmemW.coeFn_toLp
  have hfeatureV : (movingNoiseFeature R 0 v f : ℝ × Euc p.d → Euc p.d) =ᵐ[μ]
      movingNoiseKernel R 0 v f := by
    rw [movingNoiseFeature, dif_pos hmemV]
    exact hmemV.coeFn_toLp
  have hsub : (fun q : ℝ × Euc p.d =>
      (movingNoiseFeature R 0 w f - movingNoiseFeature R 0 v f) q) =ᵐ[μ]
      fun q => movingNoiseKernel R 0 w f q - movingNoiseKernel R 0 v f q := by
    filter_upwards [Lp.coeFn_sub (movingNoiseFeature R 0 w f)
      (movingNoiseFeature R 0 v f), hfeatureW, hfeatureV] with q hs hw hv
    rw [hs, Pi.sub_apply, hw, hv]
  calc
    _ = inner ℝ (movingNoiseFeature R 0 w f - movingNoiseFeature R 0 v f)
        (movingNoiseFeature R 0 w f - movingNoiseFeature R 0 v f) :=
      (real_inner_self_eq_norm_sq _).symm
    _ = ∫ q, inner ℝ
        ((movingNoiseFeature R 0 w f - movingNoiseFeature R 0 v f) q)
        ((movingNoiseFeature R 0 w f - movingNoiseFeature R 0 v f) q) ∂μ := by
      rw [L2.inner_def]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hsub] with q hq
      rw [hq, real_inner_self_eq_norm_sq]

/-- A nonnegative reference-integrable field can be integrated against any
trajectory measure, with the comparison constant from the density ratio. -/
theorem fp81s21_g4_density_integral_le
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) {r : ℝ} (hr : 0 ≤ r)
    {g : Euc p.d → ℝ} (hg : Integrable g (fp81s21_g4_mu R))
    (hg0 : ∀ x, 0 ≤ g x) :
    (∫ x, g x ∂r26t3_mu R r) ≤ p.C₁ * ∫ x, g x ∂fp81s21_g4_mu R := by
  obtain ⟨hC, hcomp⟩ := fp81s21_g4_density_comparison p R hδ hδhalf
  have hdom := (hcomp r hr).2
  have hgi : Integrable g (ENNReal.ofReal p.C₁ • fp81s21_g4_mu R) :=
    hg.smul_measure (ENNReal.ofReal_ne_top)
  have hle := integral_mono_measure hdom (Eventually.of_forall hg0) hgi
  rw [integral_smul_measure, ENNReal.toReal_ofReal hC.le, smul_eq_mul] at hle
  exact hle

#print axioms fp81s21_g4_noise_increment_kernel
#print axioms fp81s21_g4_density_integral_le
end HRS.Fp81.S21
end
