import HRS.MS.Fp81S21GaussG4U852

/-! Reference time-space integrability for the two gradient fields. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3

/-- Classical boundedness provides reference space-time square integrability
for every trajectory, without requiring a uniform smallness radius. -/
theorem fp81s21_g4_gradient_reference_product
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    {f : Euc p.d → ℝ} (hf : IsOscTest (wholeSpaceIndex p.d : ℝ) f)
    {T : ℝ} (hT : 0 ≤ T) :
    MemLp (fun z : ℝ × Euc p.d => gradient (r26t3_U R z.1 T f) z.2) 2
      ((volume.restrict (Icc (0 : ℝ) T)).prod (fp81s21_g4_mu R)) := by
  let μ := fp81s21_g4_mu R
  letI : IsProbabilityMeasure μ := HRS.Whole.Q34.isProbabilityMeasure_nu R.thermal.1.1
  let ν := (volume.restrict (Icc (0 : ℝ) T)).prod μ
  have hu := fp81s21_U_osc_test_classical p R hf hT
  let F : ℝ × Euc p.d → Euc p.d := fun z =>
    if z.1 ∈ Icc (0 : ℝ) T then gradient (r26t3_U R z.1 T f) z.2 else 0
  have hm : Measurable F := HRS.MS.R2Interp.s102_gradJoint_meas hu
  obtain ⟨B, hB, hb⟩ := HRS.MS.S111X1.x1_fderiv_bdd hu
  have hbound : ∀ᵐ z ∂ν, ‖F z‖ ≤ B := by
    filter_upwards with z
    by_cases hz : z.1 ∈ Icc (0 : ℝ) T
    · rw [show F z = gradient (r26t3_U R z.1 T f) z.2 by simp only [F, if_pos hz]]
      exact hb z.1 hz z.2
    · rw [show F z = 0 by simp only [F, if_neg hz], norm_zero]
      exact hB
  have hF : MemLp F 2 ν :=
    (MemLp.of_bound hm.aestronglyMeasurable B hbound).mono_exponent le_top
  have hae : ∀ᵐ z ∂ν, z.1 ∈ Icc (0 : ℝ) T :=
    HRS.MS.R2Interp.s102_ae_mem_prod T
  apply (memLp_congr_ae ?_).1 hF
  filter_upwards [hae] with z hz
  simp only [F, if_pos hz]

/-- Both reference-measure row integrals are integrable in time. -/
theorem fp81s21_g4_reference_time_integrable
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    {f : Euc p.d → ℝ} (hf : IsOscTest (wholeSpaceIndex p.d : ℝ) f)
    {v w : ℝ} (hv : 0 ≤ v) (hvw : v ≤ w) :
    IntegrableOn (fun r => ∫ x,
      ‖gradient (r26t3_U R r w f) x - gradient (r26t3_U R r v f) x‖^2
        ∂fp81s21_g4_mu R) (Icc (0 : ℝ) v) ∧
    IntegrableOn (fun r => ∫ x, ‖gradient (r26t3_U R r w f) x‖^2
        ∂fp81s21_g4_mu R) (Icc v w) := by
  let μ := fp81s21_g4_mu R
  letI : IsProbabilityMeasure μ := HRS.Whole.Q34.isProbabilityMeasure_nu R.thermal.1.1
  have hw := fp81s21_g4_gradient_reference_product p R hf (hv.trans hvw)
  have hv' := fp81s21_g4_gradient_reference_product p R hf hv
  have hsub : ((volume.restrict (Icc (0 : ℝ) v)).prod μ) ≤
      ((volume.restrict (Icc (0 : ℝ) w)).prod μ) :=
    Measure.prod_mono (Measure.restrict_mono (Icc_subset_Icc_right hvw) le_rfl) le_rfl
  have hnew : ((volume.restrict (Icc v w)).prod μ) ≤
      ((volume.restrict (Icc (0 : ℝ) w)).prod μ) :=
    Measure.prod_mono (Measure.restrict_mono (Icc_subset_Icc_left hv) le_rfl) le_rfl
  have h1 := (hw.mono_measure hsub).sub hv'
  have h2 := hw.mono_measure hnew
  exact ⟨(h1.integrable_norm_pow (by norm_num)).integral_prod_left,
    (h2.integrable_norm_pow (by norm_num)).integral_prod_left⟩

#print axioms fp81s21_g4_gradient_reference_product
#print axioms fp81s21_g4_reference_time_integrable
end HRS.Fp81.S21
end
