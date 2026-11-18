import HRS.MS.Fp81S21GaussG4U6Diff

/-! New-noise gradient energy from the terminal gradient and triangular increment. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2WinErr HRS.MS.R2WinOrbNL HRS.MS.S111X2

def fp81s21_g4_New {p : Parameters} {δ : ℝ} (R : Trajectory p δ)
    (f : Euc p.d → ℝ) (v w : ℝ) : ℝ :=
  ∫ r in Icc v w, ∫ x, ‖gradient (r26t3_U R r w f) x‖^2
    ∂HRS.Whole.withDensityReal R.ρβ

theorem fp81s21_g4_new_combo (p : Parameters) :
    fp81s21_g4Phys p (fun _ R =>
      ∃ A : ℝ, 0 ≤ A ∧ ∀ f, IsR2DualCombo (wholeSpaceIndex p.d : ℝ) f →
        ∀ v w, 0 ≤ v → v ≤ w →
          fp81s21_g4_New R f v w ≤ A * ((w-v)+(w-v)^2) * fp81s21_g4_J p.d f) := by
  obtain ⟨δ0, hδ0, hhalf, hdiff⟩ := fp81s21_g4_triangle_diff p
  refine ⟨δ0, hδ0, hhalf, ?_⟩
  intro δ hδ hδle R
  obtain ⟨B, hB, hbound⟩ := hdiff δ hδ hδle R
  obtain ⟨C, hC, hgrad⟩ := fp81s21_g4_gradient p R
  refine ⟨2 * (B + C), by positivity, ?_⟩
  intro f hf v w hv hvw
  let μ := HRS.Whole.withDensityReal R.ρβ
  letI : IsProbabilityMeasure μ := HRS.Whole.Q34.isProbabilityMeasure_nu R.thermal.1.1
  let τ := (volume : Measure ℝ).restrict (Icc v w)
  let ν := τ.prod μ
  have hw : 0 ≤ w := hv.trans hvw
  have hΔ : 0 ≤ w-v := sub_nonneg.mpr hvw
  have hcost : 0 ≤ fp81s21_g4_J p.d f := by unfold fp81s21_g4_J; exact sq_nonneg _
  have hfosc := HRS.MS.ProClosureS111.dualCombo_isOscTest hf
  obtain ⟨hgm, hgb⟩ := hgrad f hfosc
  rw [fp81s21_g4_cost_eq] at hgb
  have hgi : Integrable (fun x => ‖gradient f x‖^2) μ :=
    (memLp_two_iff_integrable_sq_norm hgm.aestronglyMeasurable).1 hgm
  have hgprod : Integrable (fun z : ℝ × Euc p.d => ‖gradient f z.2‖^2) ν := hgi.comp_snd τ
  obtain ⟨hdi, hdb⟩ := hbound f hf v w hv hvw
  let u := fun r => r26t3_U R r w f
  have hu : IsClassicalAdjointW (r26t3_coeff R) w f u :=
    HRS.MS.Fcau.propagatorW_isClassical (fp81s21_adjoint_of_hermite_combo p R hf hw)
  let g := fun r => u (s111x2_clamp w r)
  obtain ⟨B0, B1, B2, hB0, hB1, hB2, hFam, hFamB⟩ := s111x2_clamp_fam hw hu
  have hcont : Continuous (fun z : ℝ × Euc p.d => gradient (g z.1) z.2) := by
    exact (InnerProductSpace.toDual ℝ (Euc p.d)).symm.continuous.comp hFam.c1
  let F : ℝ × Euc p.d → ℝ := fun z => ‖gradient (g z.1) z.2‖^2
  let M : ℝ × Euc p.d → ℝ := fun z =>
    2 * ‖gradient f z.2‖^2 + 2 * ‖gradient (u z.1) z.2 - gradient f z.2‖^2
  have hMi : Integrable M ν := (hgprod.const_mul 2).add (hdi.const_mul 2)
  have hae : ∀ᵐ z ∂ν, z.1 ∈ Icc v w := by
    dsimp [ν, τ]
    rw [Measure.restrict_prod_eq_prod_univ]
    filter_upwards [ae_restrict_mem (measurableSet_Icc.prod MeasurableSet.univ)] with z hz
    exact hz.1
  have hle : ∀ᵐ z ∂ν, F z ≤ M z := by
    filter_upwards [hae] with z hz
    have hz' : z.1 ∈ Icc (0 : ℝ) w := ⟨hv.trans hz.1, hz.2⟩
    have hclamp := s111x2_clamp_id hz'
    dsimp [F, M, g]
    rw [hclamp]
    have ht := norm_add_le (gradient f z.2) (gradient (u z.1) z.2 - gradient f z.2)
    have he : gradient f z.2 + (gradient (u z.1) z.2 - gradient f z.2) = gradient (u z.1) z.2 := by abel
    rw [he] at ht
    nlinarith [norm_nonneg (gradient (u z.1) z.2), norm_nonneg (gradient f z.2), norm_nonneg (gradient (u z.1) z.2 - gradient f z.2),
      sq_nonneg (‖gradient f z.2‖ - ‖gradient (u z.1) z.2 - gradient f z.2‖)]
  have hFi : Integrable F ν := by
    refine Integrable.mono' hMi (hcont.norm.pow 2).aestronglyMeasurable ?_
    filter_upwards [hle] with z hz
    change |F z| ≤ M z
    rw [abs_of_nonneg (show 0 ≤ F z from sq_nonneg _)]
    exact hz
  have hFM : (∫ z, F z ∂ν) ≤ ∫ z, M z ∂ν := integral_mono_ae hFi hMi hle
  have hnew : (∫ z, F z ∂ν) = fp81s21_g4_New R f v w := by
    rw [integral_prod _ hFi]
    unfold fp81s21_g4_New
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    have hr' : r ∈ Icc (0 : ℝ) w := ⟨hv.trans hr.1, hr.2⟩
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      dsimp [F, g, u]
      rw [s111x2_clamp_id hr']
  have hgval : (∫ z, ‖gradient f z.2‖^2 ∂ν) =
      (w-v) * (∫ x, ‖gradient f x‖^2 ∂μ) := by
    rw [integral_prod _ hgprod]
    change (∫ _r in Icc v w, ∫ x, ‖gradient f x‖^2 ∂μ) = _
    rw [setIntegral_const]
    simp [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal hΔ, smul_eq_mul]
  have hdval : (∫ z, ‖gradient (u z.1) z.2 - gradient f z.2‖^2 ∂ν) =
      ∫ r in Icc v w, ∫ x, ‖gradient (u r) x - gradient f x‖^2 ∂μ :=
    integral_prod _ hdi
  have hMval : (∫ z, M z ∂ν) =
      2 * ((w-v) * (∫ x, ‖gradient f x‖^2 ∂μ)) +
      2 * (∫ r in Icc v w, ∫ x, ‖gradient (u r) x - gradient f x‖^2 ∂μ) := by
    dsimp [M]
    rw [integral_add (hgprod.const_mul 2) (hdi.const_mul 2), integral_const_mul,
      integral_const_mul, hgval, hdval]
  rw [hnew, hMval] at hFM
  have hgb' := mul_le_mul_of_nonneg_left hgb hΔ
  have hnonneg : 0 ≤ (w-v) * fp81s21_g4_J p.d f := mul_nonneg hΔ hcost
  have hnonneg2 : 0 ≤ (w-v)^2 * fp81s21_g4_J p.d f := mul_nonneg (sq_nonneg _) hcost
  nlinarith

#print axioms fp81s21_g4_new_combo
end HRS.Fp81.S21
end
