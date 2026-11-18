import HRS.MS.S111X1E1
import HRS.MS.S21F_D00

/-!
# S21F, packet R26-T3.C01 (part a): a weighted Schur/Cauchy-Schwarz test in `ℝ≥0∞`

`(∫ w u dμ)² ≤ (∫ w dμ)(∫ w u² dμ)` for measurable `w, u ≥ 0`, and the uniform mass bound of the force envelope
`W(z) = σ(‖z‖^{-(s+1)} 1_{‖z‖<1} + 1)` against a bounded probability density.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set InformationTheory
open scoped ENNReal NNReal BigOperators
open HRS HRS.Whole

namespace HRS.MS.R26T3

theorem s21f_cs_sq {α : Type*} [MeasurableSpace α] (μ : Measure α) {w u : α → ℝ≥0∞}
    (hw : Measurable w) (hu : Measurable u) :
    (∫⁻ y, w y * u y ∂μ) ^ 2 ≤ (∫⁻ y, w y ∂μ) * ∫⁻ y, w y * u y ^ 2 ∂μ := by
  set f : α → ℝ≥0∞ := fun y => w y ^ (1 / 2 : ℝ) with hf
  set g : α → ℝ≥0∞ := fun y => w y ^ (1 / 2 : ℝ) * u y with hg
  have hfm : Measurable f := hw.pow_const _
  have hgm : Measurable g := hfm.mul hu
  have h1 : ∀ y, f y * g y = w y * u y := fun y => by
    simp only [hf, hg]
    rw [← mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  have h2 : ∀ y, f y ^ (2 : ℝ) = w y := fun y => by
    simp only [hf]
    rw [← ENNReal.rpow_mul]; norm_num
  have h3 : ∀ y, g y ^ (2 : ℝ) = w y * u y ^ 2 := fun y => by
    simp only [hg]
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul]
    norm_num
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hfm.aemeasurable hgm.aemeasurable
  simp only [Pi.mul_apply] at h
  simp_rw [h1, h2, h3] at h
  calc (∫⁻ y, w y * u y ∂μ) ^ 2 ≤ ((∫⁻ y, w y ∂μ) ^ (1 / 2 : ℝ) * (∫⁻ y, w y * u y ^ 2 ∂μ) ^ (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left' h 2
    _ = (∫⁻ y, w y ∂μ) * ∫⁻ y, w y * u y ^ 2 ∂μ := by
        rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast ((∫⁻ y, w y * u y ^ 2 ∂μ) ^ (1 / 2 : ℝ)),
          ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
        norm_num

/-- the force envelope `W(z) = σ (‖z‖^{-(s+1)} 1_{‖z‖<1} + 1)` -/
def s21f_W (d : ℕ) (s : ℝ) (z : Euc d) : ℝ :=
  HRS.MS.S111X1.kσ s * (HRS.MH.DualityRd.db1G (s + 1) z + 1)

theorem s21f_W_nonneg (d : ℕ) (s : ℝ) (z : Euc d) : 0 ≤ s21f_W d s z :=
  mul_nonneg (HRS.MS.S111X1.kσ_nonneg s) (by linarith [HRS.MH.DualityRd.db1G_nonneg (d := d) (s + 1) z])

theorem s21f_W_meas (d : ℕ) (s : ℝ) : Measurable (s21f_W d s) :=
  measurable_const.mul ((HRS.MH.DualityRd.db1_measurable_G (d := d) (s + 1)).add_const 1)

theorem s21f_W_even (d : ℕ) (s : ℝ) (z : Euc d) : s21f_W d s (-z) = s21f_W d s z := by
  have h : HRS.MH.DualityRd.db1G (d := d) (s + 1) (-z) = HRS.MH.DualityRd.db1G (s + 1) z := by
    unfold HRS.MH.DualityRd.db1G
    simp only [Set.indicator, Metric.mem_ball, dist_zero_right, norm_neg]
  unfold s21f_W
  rw [h]

theorem s21f_force_mass {d : ℕ} (hd : 1 ≤ d) {s : ℝ} (hsd : s + 1 < d) {ρ : Euc d → ℝ}
    (hρ : HRS.Whole.IsProbDensity ρ) {M : ℝ} (hM : ∀ x, ρ x ≤ M) (x : Euc d) :
    ∫⁻ y, ENNReal.ofReal (s21f_W d s (x - y)) ∂(HRS.Whole.withDensityReal ρ) ≤
      ENNReal.ofReal (HRS.MS.S111X1.kσ s * (M * (∫ z, HRS.MH.DualityRd.db1G (d := d) (s + 1) z) + 1)) := by
  haveI := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  set σ := HRS.MS.S111X1.kσ s with hσ
  have hσ0 : 0 ≤ σ := HRS.MS.S111X1.kσ_nonneg s
  have hM0 : 0 ≤ M := (hρ.nonneg 0).trans (hM 0)
  have hint := HRS.MH.DualityRd.db1G_integrable (d := d) hd hsd
  set a := ∫ z, HRS.MH.DualityRd.db1G (d := d) (s + 1) z with ha
  have ha0 : 0 ≤ a := integral_nonneg fun z => HRS.MH.DualityRd.db1G_nonneg _ _
  have hG : Measurable (HRS.MH.DualityRd.db1G (d := d) (s + 1)) := HRS.MH.DualityRd.db1_measurable_G _
  have hsplit : ∀ z : Euc d, ENNReal.ofReal (s21f_W d s z) =
      ENNReal.ofReal (σ * HRS.MH.DualityRd.db1G (s + 1) z) + ENNReal.ofReal σ := fun z => by
    unfold s21f_W
    rw [← ENNReal.ofReal_add (mul_nonneg hσ0 (HRS.MH.DualityRd.db1G_nonneg _ _)) hσ0]
    congr 1; ring
  have hmeas1 : Measurable fun y : Euc d => ENNReal.ofReal (σ * HRS.MH.DualityRd.db1G (s + 1) (x - y)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul (hG.comp (measurable_const.sub measurable_id)))
  simp_rw [hsplit]
  rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
  have h1 : ∫⁻ y, ENNReal.ofReal (σ * HRS.MH.DualityRd.db1G (s + 1) (x - y)) ∂(HRS.Whole.withDensityReal ρ) ≤
      ENNReal.ofReal M * ENNReal.ofReal (σ * a) := by
    rw [HRS.Whole.withDensityReal, lintegral_withDensity_eq_lintegral_mul _
      (f := fun x => ENNReal.ofReal (ρ x)) (ENNReal.measurable_ofReal.comp hρ.measurable) hmeas1]
    have hmp := (volume : Measure (Euc d)).measurePreserving_sub_left x
    have hlc := hmp.lintegral_comp (f := fun z => ENNReal.ofReal (σ * HRS.MH.DualityRd.db1G (d := d) (s + 1) z))
      (ENNReal.measurable_ofReal.comp (measurable_const.mul hG))
    calc ∫⁻ y, ENNReal.ofReal (ρ y) * ENNReal.ofReal (σ * HRS.MH.DualityRd.db1G (s + 1) (x - y))
        ≤ ∫⁻ y, ENNReal.ofReal M * ENNReal.ofReal (σ * HRS.MH.DualityRd.db1G (s + 1) (x - y)) :=
          lintegral_mono fun y => mul_le_mul_left (ENNReal.ofReal_le_ofReal (hM y)) _
      _ = ENNReal.ofReal M * ∫⁻ y, ENNReal.ofReal (σ * HRS.MH.DualityRd.db1G (s + 1) (x - y)) :=
          lintegral_const_mul _ hmeas1
      _ = ENNReal.ofReal M * ∫⁻ z, ENNReal.ofReal (σ * HRS.MH.DualityRd.db1G (s + 1) z) := by
          rw [show (∫⁻ y, ENNReal.ofReal (σ * HRS.MH.DualityRd.db1G (s + 1) (x - y))) =
            ∫⁻ z, ENNReal.ofReal (σ * HRS.MH.DualityRd.db1G (s + 1) z) from hlc]
      _ = ENNReal.ofReal M * ENNReal.ofReal (σ * a) := by
          congr 1
          rw [← ofReal_integral_eq_lintegral_ofReal (hint.const_mul σ)
            (Eventually.of_forall fun z => mul_nonneg hσ0 (HRS.MH.DualityRd.db1G_nonneg _ _)),
            integral_const_mul]
  refine (add_le_add_left h1 _).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_mul hM0, ← ENNReal.ofReal_add (mul_nonneg hM0 (mul_nonneg hσ0 ha0)) hσ0]
  congr 1; rw [ha]; ring

end HRS.MS.R26T3
