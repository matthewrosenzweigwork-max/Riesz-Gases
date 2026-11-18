import HRS.MS.Fp81S21B6iiEmp

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter
open scoped ENNReal RealInnerProductSpace
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111

private theorem fp81s21_six_normalized
    {d r r' : ℕ} {Pw Ps : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (hr : r + 2 = r') (hp : Pw + 2 = Ps)
    (hP : (d : ℝ) < 2 * Pw) (hPs : (d : ℝ) < 2 * Ps)
    (Es : r26t6_WeightedChart d r Ps) (E : r26t6_WeightedChart d r' Pw)
    (P : Measure Ω) (qs : ℝ → Ω → r26t6_Coeff) (M : ℝ)
    (hs : fp81s21_Six P qs M) :
    fp81s21_Six P (fun u ω => fp81s21_embedField_normalized hr hp hP hPs Es E (qs u ω)) M := by
  subst r'
  subst Ps
  exact fp81s21_Six_embedField hP hPs Es E P qs M hs

/-- A jointly measurable common-time version inherits all fixed-time moment
certificates from any representative of the same empirical field. -/
theorem fp81s21_emp_common_time_transfer
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ) (N : ℕ) (hN : 2 ≤ N)
    (A : Particle R N)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (μ : ℝ → Measure (Euc p.d))
    (hμ : ∀ u, 0 ≤ u → μ u = r26t3_mu R u)
    (hi : ∀ u, Integrable (fun x : Euc p.d => jbracket x ^ ((p.d : ℝ) + 4)) (μ u))
    (hm : ∀ j, Measurable (fun u => HRS.Whole.pair (μ u) (Es.test j)))
    (qold : ℝ → A.Ω → r26t6_Coeff) (M2 M6 : ℝ)
    (hrep : fp81s21_MomentRep Es A.P (fp81s21_particleEmpField R N A) qold M2)
    (hsix : fp81s21_Six A.P qold M6) :
    ∃ qs : ℝ → A.Ω → r26t6_Coeff,
      fp81s21_MomentRep Es A.P (fp81s21_particleEmpField R N A) qs M2 ∧
      fp81s21_Six A.P qs M6 ∧
      fp81s21_MomentRep E A.P (fp81s21_particleEmpField R N A)
        (fun u ω => fp81s21_gaussian_chartEmbed p Es E (qs u ω)) M2 ∧
      fp81s21_Six A.P (fun u ω => fp81s21_gaussian_chartEmbed p Es E (qs u ω)) M6 ∧
      (∀ᵐ ω ∂A.P, ∀ u : ℝ, 0 ≤ u → ∀ f : Euc p.d → ℝ,
        IsR2Test f → fp81s21_chartAction Es (qs u ω) f =
          fp81s21_particleEmpField R N A u ω f) ∧
      (∀ᵐ ω ∂A.P, ∀ u : ℝ, 0 ≤ u → ∀ f : Euc p.d → ℝ,
        IsR2Test f → fp81s21_chartAction E
          (fp81s21_gaussian_chartEmbed p Es E (qs u ω)) f =
          fp81s21_particleEmpField R N A u ω f) := by
  obtain ⟨qs, hmeas, hcommon⟩ := fp81s21_emp_common_time_of_reference p R N hN A Es μ hμ hi hm
  have heq (u : ℝ) (hu : 0 ≤ u) : qs u =ᵐ[A.P] qold u := by
    filter_upwards [hcommon, (hrep.2 u hu).2.2] with ω ha hb
    apply fp81s21_emp_coeff_unique Es
    intro f hf
    rw [ha u hu f hf, hb.1 f hf]
  have hnew : fp81s21_MomentRep Es A.P (fp81s21_particleEmpField R N A) qs M2 := by
    refine ⟨hmeas, ?_⟩
    intro u hu
    have he := heq u hu
    obtain ⟨hmem, hbound, hfield⟩ := hrep.2 u hu
    refine ⟨(memLp_congr_ae he).2 hmem, ?_, ?_⟩
    · calc
        _ = ∫ ω, ‖qold u ω‖ ^ 2 ∂A.P := integral_congr_ae (he.mono fun _ h => by simpa only using congrArg (fun z : r26t6_Coeff => ‖z‖ ^ 2) h)
        _ ≤ M2 := hbound
    · filter_upwards [he, hfield] with ω heω hfieldω
      simpa [heω] using hfieldω
  have hnew6 : fp81s21_Six A.P qs M6 := by
    intro u hu
    have he := heq u hu
    obtain ⟨_, hi6, hb6⟩ := hsix u hu
    have hn : (fun ω => ‖qs u ω‖ ^ 6) =ᵐ[A.P] (fun ω => ‖qold u ω‖ ^ 6) :=
      he.mono fun _ h => by simpa only using congrArg (fun z : r26t6_Coeff => ‖z‖ ^ 6) h
    refine ⟨(hmeas.comp (measurable_const.prodMk measurable_id)).aemeasurable,
      (integrable_congr hn).2 hi6, ?_⟩
    calc
      _ = ∫ ω, ‖qold u ω‖ ^ 6 ∂A.P := integral_congr_ae hn
      _ ≤ M6 := hb6
  have hw : fp81s21_MomentRep E A.P (fp81s21_particleEmpField R N A)
      (fun u ω => fp81s21_gaussian_chartEmbed p Es E (qs u ω)) M2 := by
    simpa [fp81s21_gaussian_chartEmbed] using
      fp81s21_MomentRep_embedField_normalized (by omega) (by ring)
        (by nlinarith [p.hd]) (by nlinarith [p.hd]) Es E A.P _ qs M2 hnew
  have hw6 : fp81s21_Six A.P (fun u ω => fp81s21_gaussian_chartEmbed p Es E (qs u ω)) M6 := by
    simpa [fp81s21_gaussian_chartEmbed] using
      fp81s21_six_normalized (by omega) (by ring)
        (by nlinarith [p.hd]) (by nlinarith [p.hd]) Es E A.P qs M6 hnew6
  refine ⟨qs, hnew, hnew6, hw, hw6, hcommon, ?_⟩
  filter_upwards [hcommon] with ω hω
  intro u hu f hf
  calc
    _ = fp81s21_chartAction Es (qs u ω) f := by
      simpa [fp81s21_gaussian_chartEmbed] using
        fp81s21_embedField_normalized_action (by omega) (by ring)
          (by nlinarith [p.hd]) (by nlinarith [p.hd]) Es E (qs u ω) f hf
    _ = _ := hω u hu f hf

#print axioms fp81s21_emp_common_time_transfer
end HRS.Fp81.S21
end
