import HRS.MS.Fp81S21TimeRep13

/-! Helpers for the physical particle-to-time-section bridge. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory
open scoped ENNReal RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.R2Interp
open HRS.MS.ProClosureS111

/-- The clipped moving particle density is jointly continuous in time and
space on the whole real time axis. -/
theorem fp81s21_particle_density_clip_continuous
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2) :
    Continuous (fun q : ℝ × Euc p.d =>
      R.ρ ((max q.1 0).toNNReal) q.2) := by
  have hsd : p.s < (p.d : ℝ) := by linarith [p.hs]
  have hρeq : R.ρβ = HRS.Whole.thermalDensity p.d p.s p.a p.β :=
    HRS.MS.Mov0.mv0_rho_eq p.hd p.hs0 hsd p.ha p.hβ R.thermal
  have hρβc : Continuous R.ρβ := by
    obtain ⟨-, ψ', hψ'⟩ := HRS.MS.S21.s21_schwartz_thermal
      p.hd p.hs0 hsd p.ha p.hβ
    rw [hρeq, ← hψ']
    exact ψ'.continuous
  have hρβpos : ∀ x, 0 < R.ρβ x :=
    fun x => HRS.Whole.u4_thermal_pos R.thermal x
  have hm : (p.d : ℝ) / 2 < ((102 * p.d + 1020 : ℕ) : ℝ) := by
    rw [HRS.MS.R2WinOrbNL.s103n_cast_m]
    nlinarith
  have hclass := HRS.MS.R2WinOrbNL.s103n_small_class R.resulting
    (r := p.C₁ * δ) le_rfl
  have hjoint := HRS.MS.R2S11.s11_class_continuous hρβc hρβpos hm hclass
  have hmap : Continuous (fun q : ℝ × Euc p.d =>
      ((max q.1 0).toNNReal, q.2)) := by
    fun_prop
  exact hjoint.comp hmap

/-- Compact chart actions determine their coefficient vector. -/
theorem fp81s21_coeff_eq_of_chartAction_eq
    {d r : ℕ} {Pw : ℝ} (hP : (d : ℝ) < 2 * Pw)
    (E : r26t6_WeightedChart d r Pw) (z₁ z₂ : r26t6_Coeff)
    (hact : ∀ f, IsR2Test f →
      fp81s21_chartAction E z₁ f = fp81s21_chartAction E z₂ f) :
    z₁ = z₂ := by
  have hcompact : ∀ f, IsR2Test f →
      fp81s21_chartAction E (z₁ - z₂) f = 0 := by
    intro f hf
    have hlin : fp81s21_chartAction E (z₁ - z₂) f =
        fp81s21_chartAction E z₁ f - fp81s21_chartAction E z₂ f := by
      simp [fp81s21_chartAction, inner_sub_left]
    rw [hlin, hact f hf]
    ring
  have hdual :
      dualNormE r Pw (fp81s21_chartAction E (z₁ - z₂)) = 0 := by
    unfold dualNormE
    apply le_antisymm
    · refine iSup_le fun f => iSup_le fun hf => ?_
      have htest : IsR2Test f := ⟨hf.1, hf.2.1⟩
      rw [hcompact f htest]
      simp
    · exact bot_le
  have hnorm : ENNReal.ofReal ‖z₁ - z₂‖ = 0 := by
    rw [← fp81s21_chartAction_dualNorm hP E (z₁ - z₂)]
    exact hdual
  have hnorm' : ‖z₁ - z₂‖ = 0 := by
    have h := congrArg ENNReal.toReal hnorm
    rw [ENNReal.toReal_ofReal (norm_nonneg _), ENNReal.toReal_zero] at h
    exact h
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm')

/-- A sectionwise almost-everywhere coefficient identity becomes a product
identity through the measurable equality event. -/
theorem fp81s21_product_ae_of_section_ae
    {T Ω F : Type*} [MeasurableSpace T] [MeasurableSpace Ω]
    [MeasurableSpace F] [MeasurableEq F]
    (dt : Measure T) [SFinite dt] (P : Measure Ω) [SFinite P]
    (q q₀ : T × Ω → F) (hq : Measurable q) (hq₀ : Measurable q₀)
    (hsec : ∀ᵐ t ∂dt, (fun ω => q (t, ω)) =ᵐ[P]
      (fun ω => q₀ (t, ω))) :
    q =ᵐ[dt.prod P] q₀ := by
  apply (Measure.ae_prod_iff_ae_ae
    (measurableSet_eq_fun hq hq₀)).2
  exact hsec

#print axioms HRS.Fp81.S21.fp81s21_particle_density_clip_continuous
#print axioms HRS.Fp81.S21.fp81s21_coeff_eq_of_chartAction_eq
#print axioms HRS.Fp81.S21.fp81s21_product_ae_of_section_ae

end HRS.Fp81.S21
