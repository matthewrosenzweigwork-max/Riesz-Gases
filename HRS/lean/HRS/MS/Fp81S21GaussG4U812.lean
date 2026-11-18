import HRS.MS.Fp81S21GaussG4U81
import HRS.MS.Fp81S21GaussG4U5Energy
import HRS.MS.Fp81S21PropagatorOsc
import HRS.MS.R2InterpAux83
import HRS.MS.S111X1Aux1

/-! Uniform reference-measure stability of the oscillator propagator. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.S111X2

private theorem fp81s21_g4_gradient_product (p : Parameters) {δ T : ℝ}
    (R : Trajectory p δ) (g : Euc p.d → ℝ)
    (hu : IsClassicalAdjointW (r26t3_coeff R) T g
      (fun r => r26t3_U R r T g)) :
    MemLp (fun z : ℝ × Euc p.d => gradient (r26t3_U R z.1 T g) z.2) 2
      ((volume.restrict (Icc (0 : ℝ) T)).prod (HRS.Whole.withDensityReal R.ρβ)) := by
  let μ := HRS.Whole.withDensityReal R.ρβ
  letI : IsProbabilityMeasure μ := HRS.Whole.Q34.isProbabilityMeasure_nu R.thermal.1.1
  let ν := (volume.restrict (Icc (0 : ℝ) T)).prod μ
  let F : ℝ × Euc p.d → Euc p.d := fun z =>
    if z.1 ∈ Icc (0 : ℝ) T then gradient (r26t3_U R z.1 T g) z.2 else 0
  have hm : Measurable F := HRS.MS.R2Interp.s102_gradJoint_meas hu
  obtain ⟨B, hB, hb⟩ := HRS.MS.S111X1.x1_fderiv_bdd hu
  have hbound : ∀ᵐ z ∂ν, ‖F z‖ ≤ B := by
    filter_upwards with z
    by_cases hz : z.1 ∈ Icc (0 : ℝ) T
    · rw [show F z = gradient (r26t3_U R z.1 T g) z.2 by simp only [F, if_pos hz]]
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

theorem fp81s21_g4_propagator_stability (p : Parameters) :
    fp81s21_g4Phys p (fun _ R =>
      ∃ B : ℝ, 0 ≤ B ∧ ∀ g : Euc p.d → ℝ,
        IsOscTest (wholeSpaceIndex p.d : ℝ) g →
        ∀ T : ℝ, 0 ≤ T →
          MemLp (fun z : ℝ × Euc p.d => gradient (r26t3_U R z.1 T g) z.2) 2
            ((volume.restrict (Icc (0 : ℝ) T)).prod (HRS.Whole.withDensityReal R.ρβ)) ∧
          IntegrableOn (fun r => ∫ x, ‖gradient (r26t3_U R r T g) x‖^2
            ∂HRS.Whole.withDensityReal R.ρβ) (Icc (0 : ℝ) T) ∧
          (∫ r in Icc (0 : ℝ) T, ∫ x, ‖gradient (r26t3_U R r T g) x‖^2
            ∂HRS.Whole.withDensityReal R.ρβ) ≤ B * fp81s21_g4_J p.d g ∧
          (∀ r ∈ Icc (0 : ℝ) T,
            MemLp (r26t3_U R r T g) 2 (HRS.Whole.withDensityReal R.ρβ) ∧
            (∫ x, (HRS.Whole.projMean (HRS.Whole.withDensityReal R.ρβ)
              (r26t3_U R r T g) x)^2 ∂HRS.Whole.withDensityReal R.ρβ) ≤
                B * fp81s21_g4_J p.d g)) := by
  obtain ⟨δa, ha, hahalf, henergy⟩ := fp81s21_g4_adjoint_energy p
  obtain ⟨δb, Q, C, c, hb, hbhalf, hQ, hQδ, hC, hc, hdecay⟩ :=
    sol13_uniform_adjoint_energy p
  refine ⟨min δa δb, lt_min ha hb, (min_le_left _ _).trans hahalf, ?_⟩
  intro δ hδ hδmin R
  have hδa := hδmin.trans (min_le_left δa δb)
  have hδb := hδmin.trans (min_le_right δa δb)
  obtain ⟨A, hA, hbudget⟩ := henergy δ hδ hδa R
  obtain ⟨D, hD, hinput⟩ := fp81s21_g4_input_l2 p R
  refine ⟨(1 + A + C) * D, by positivity, ?_⟩
  intro g hg T hT
  let μ := HRS.Whole.withDensityReal R.ρβ
  letI : IsProbabilityMeasure μ := HRS.Whole.Q34.isProbabilityMeasure_nu R.thermal.1.1
  obtain ⟨hgL, hgJ⟩ := hinput g hg
  have hJ : 0 ≤ fp81s21_g4_J p.d g := by unfold fp81s21_g4_J; exact sq_nonneg _
  have hI : 0 ≤ ∫ x, (g x)^2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have hDJ : 0 ≤ D * fp81s21_g4_J p.d g := mul_nonneg hD hJ
  have hcent := s111x2_cs_le_sq hgL
  change (∫ x, (HRS.Whole.projMean μ g x)^2 ∂μ) ≤ _ at hcent
  have hu := fp81s21_U_osc_test_classical p R hg hT
  have hp := fp81s21_g4_gradient_product p R g hu
  have hmem : ∀ r ∈ Icc (0 : ℝ) T, MemLp (r26t3_U R r T g) 2 μ := by
    obtain ⟨B0, B1, B2, hB0, hB1, hB2, hB⟩ := HRS.MS.S111X1.classical_bounds hu
    intro r hr
    exact (MemLp.of_bound (hu.c2 r hr).continuous.aestronglyMeasurable B0
      (Eventually.of_forall fun x => (hB r hr x).1)).mono_exponent le_top
  refine ⟨hp, ?_, ?_, ?_⟩
  · by_cases hzero : T = 0
    · subst T
      simp
    · exact (hbudget T (lt_of_le_of_ne hT (Ne.symm hzero)) g _ hu hgL).1
  · by_cases hzero : T = 0
    · subst T
      simpa using mul_nonneg (by positivity : 0 ≤ (1 + A + C) * D) hJ
    · have hbud := (hbudget T (lt_of_le_of_ne hT (Ne.symm hzero)) g _ hu hgL).2
      have := mul_le_mul_of_nonneg_left hgJ hA.le
      nlinarith
  · intro r hr
    refine ⟨hmem r hr, ?_⟩
    by_cases hzero : T = 0
    · subst T
      have hr0 : r = 0 := by simpa using hr
      subst r
      have heq : r26t3_U R 0 0 g = g := hu.terminal
      rw [heq]
      nlinarith
    · have hd := (hdecay δ hδ hδb R T (lt_of_le_of_ne hT (Ne.symm hzero)) g _ hu).2.2.2 r hr |>.2
      have hexp : Real.exp (-c * (T - r)) ≤ 1 := by
        apply Real.exp_le_one_iff.mpr
        nlinarith [hr.2]
      have hcent0 : 0 ≤ ∫ x, (HRS.Whole.projMean μ g x)^2 ∂μ := integral_nonneg fun x => sq_nonneg _
      have hcoeff : C * Real.exp (-c * (T - r)) ≤ C := by
        nlinarith [Real.exp_pos (-c * (T - r))]
      have h1 := mul_le_mul_of_nonneg_right hcoeff hcent0
      have h2 := mul_le_mul_of_nonneg_left hcent hC.le
      have h3 := mul_le_mul_of_nonneg_left hgJ hC.le
      nlinarith

#print axioms fp81s21_g4_propagator_stability
end HRS.Fp81.S21
end
