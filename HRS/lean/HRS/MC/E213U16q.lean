import HRS.MC.E213U16p

/-!
# Packet e213u16, file q: integrability of the conditioning integrands
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace HRS.MC.E213U16

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Q HRS.MC.E213U13 HRS.MC.E213Plan
open HRS.MC.E213U10

variable {d : ℕ}

section UcanF

variable {S : PreparedData d} {β₀ m : ℝ} (hE : EdgeworthHyp S β₀ m)

theorem u16_Ucan_eq (T : ℝ) (a : ℝ) (ha : 0 ≤ a) (Φ : PathSpace d m T → ℝ) (τ : ℝ) :
    Ucan hE T a ha Φ τ = fun y => ∫ z, Φ (y + winRestr a ha z) ∂(canonFut hE (a + T) τ) := rfl

theorem u16_Ucan_fderiv_bound (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) (Φ : PathSpace d m T → ℝ)
    (hΦ : MemCb 5 Φ) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) (a + T)) (y δ : PathSpace d m T) :
    |fderiv ℝ (Ucan hE T a ha Φ τ) y δ| ≤ cbNorm 5 Φ * ‖δ‖ := by
  have hH : 0 < a + T := by linarith
  haveI : IsProbabilityMeasure (canonFut hE (a + T) τ) :=
    (HRS.MC.E213U5.e213u5_canonFut_spec hE (a + T) hH τ hτ).2
  rw [u16_Ucan_eq, u16_heat_fderiv (canonFut hE (a + T) τ) (winRestr a ha) hΦ y δ]
  have := norm_integral_le_of_norm_le_const (μ := canonFut hE (a + T) τ)
    (f := fun z => fderiv ℝ Φ (y + winRestr a ha z) δ) (C := cbNorm 5 Φ * ‖δ‖)
    (Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs]
      exact ((fderiv ℝ Φ _).le_opNorm δ).trans (mul_le_mul_of_nonneg_right (u16_norm_fderiv_le hΦ _) (norm_nonneg _)))
  simpa [Real.norm_eq_abs] using this

theorem u16_Ucan_fderiv_cont (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) (Φ : PathSpace d m T → ℝ)
    (hΦ : MemCb 5 Φ) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) (a + T)) :
    Continuous fun p : PathSpace d m T × PathSpace d m T => fderiv ℝ (Ucan hE T a ha Φ τ) p.1 p.2 := by
  have hH : 0 < a + T := by linarith
  haveI : IsProbabilityMeasure (canonFut hE (a + T) τ) :=
    (HRS.MC.E213U5.e213u5_canonFut_spec hE (a + T) hH τ hτ).2
  have hc := (HRS.MC.E213U5.e213u5_heat_deriv (canonFut hE (a + T) τ) (winRestr a ha) hΦ).1
  have hc' : ContDiff ℝ 5 (Ucan hE T a ha Φ τ) := hc
  exact (hc'.continuous_fderiv (by norm_num)).comp continuous_fst |>.clm_apply continuous_snd

end UcanF


section IncInt

variable {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} (gd : GaussData S β₀ hE)

theorem u16_Y_aem (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) (a + T)) :
    AEMeasurable (fun ω => winPred (regime S β₀ hE) m T a ha (gd.Zwin (a + T) 0 ω) τ) gd.P₀ := by
  obtain ⟨Y', hY', hae⟩ := u16_Y_past gd T hT a ha hτ
  exact (hY'.mono (pastSig_le gd hτ) le_rfl).aemeasurable.congr hae.symm

theorem u16_Delta_aem (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) {u τ : ℝ} (hu : 0 ≤ u) (huτ : u ≤ τ)
    (hτ : τ ≤ a + T) :
    AEMeasurable (fun ω => winDrift (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (gd.B v ω)) u τ) gd.P₀ := by
  obtain ⟨D', hD', hae⟩ := u16_winDrift_past gd T hT a ha hu huτ hτ
  exact (hD'.mono (pastSig_le gd ⟨hu.trans huτ, hτ⟩) le_rfl).aemeasurable.congr hae.symm

theorem u16_Zwin_aem (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) : AEMeasurable (gd.Zwin T a) gd.P₀ := by
  have hH : 0 < a + T := by linarith
  have h := (winRestr a ha).continuous.measurable.comp_aemeasurable (u16_Z_aemeasurable gd (a + T) hH)
  refine h.congr ?_
  filter_upwards [u16_Zwin_restr gd T hT a ha] with ω hω
  exact hω.symm

theorem u16_incL_integrable (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) (Φ : PathSpace d m T → ℝ) (hΦ : MemCb 5 Φ)
    {u τ : ℝ} (hu : 0 ≤ u) (huτ : u ≤ τ) (hτ : τ ≤ a + T) :
    Integrable (fun ω => fderiv ℝ Φ (gd.Zwin T a ω)
        (winDrift (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (gd.B v ω)) u τ)) gd.P₀ := by
  obtain ⟨K, hK, hKb⟩ := u16_Dinc_bound gd T hT a ha
  have hmeas : AEStronglyMeasurable (fun ω => fderiv ℝ Φ (gd.Zwin T a ω)
        (winDrift (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (gd.B v ω)) u τ)) gd.P₀ := by
    have hc : Continuous fun p : PathSpace d m T × PathSpace d m T => fderiv ℝ Φ p.1 p.2 :=
      ((hΦ.1.continuous_fderiv (by norm_num)).comp continuous_fst).clm_apply continuous_snd
    have := hc.aestronglyMeasurable.comp_aemeasurable
      ((u16_Zwin_aem gd T hT a ha).prodMk (u16_Delta_aem gd T hT a ha hu huτ hτ))
    exact this
  refine ((u16_Gblk_integrable gd (a + T)).const_mul (cbNorm 5 Φ * K)).mono' hmeas ?_
  filter_upwards [hKb] with ω hω
  calc ‖fderiv ℝ Φ (gd.Zwin T a ω) (winDrift (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (gd.B v ω)) u τ)‖
      ≤ ‖fderiv ℝ Φ (gd.Zwin T a ω)‖ * ‖winDrift (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (gd.B v ω)) u τ‖ :=
        (fderiv ℝ Φ _).le_opNorm _
    _ ≤ cbNorm 5 Φ * (K * Gblk gd (a + T) ω) :=
        mul_le_mul (u16_norm_fderiv_le hΦ _) (hω u τ hu huτ hτ) (norm_nonneg _)
          ((norm_nonneg _).trans (u16_norm_fderiv_le hΦ 0))
    _ = cbNorm 5 Φ * K * Gblk gd (a + T) ω := by ring

theorem u16_incR_integrable (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) (Φ : PathSpace d m T → ℝ) (hΦ : MemCb 5 Φ)
    {u τ : ℝ} (hu : 0 ≤ u) (huτ : u ≤ τ) (hτ : τ ≤ a + T) :
    Integrable (fun ω => fderiv ℝ (Ucan hE T a ha Φ τ) (winPred (regime S β₀ hE) m T a ha (gd.Zwin (a + T) 0 ω) τ)
        (winDrift (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (gd.B v ω)) u τ)) gd.P₀ := by
  obtain ⟨K, hK, hKb⟩ := u16_Dinc_bound gd T hT a ha
  have hτI : τ ∈ Set.Icc (0 : ℝ) (a + T) := ⟨hu.trans huτ, hτ⟩
  have hmeas : AEStronglyMeasurable (fun ω => fderiv ℝ (Ucan hE T a ha Φ τ)
      (winPred (regime S β₀ hE) m T a ha (gd.Zwin (a + T) 0 ω) τ)
        (winDrift (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (gd.B v ω)) u τ)) gd.P₀ := by
    have := (u16_Ucan_fderiv_cont hE T hT a ha Φ hΦ hτI).aestronglyMeasurable.comp_aemeasurable
      ((u16_Y_aem gd T hT a ha hτI).prodMk (u16_Delta_aem gd T hT a ha hu huτ hτ))
    exact this
  refine ((u16_Gblk_integrable gd (a + T)).const_mul (cbNorm 5 Φ * K)).mono' hmeas ?_
  filter_upwards [hKb] with ω hω
  rw [Real.norm_eq_abs]
  calc _ ≤ cbNorm 5 Φ * ‖winDrift (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (gd.B v ω)) u τ‖ :=
        u16_Ucan_fderiv_bound hE T hT a ha Φ hΦ hτI _ _
    _ ≤ cbNorm 5 Φ * (K * Gblk gd (a + T) ω) :=
        mul_le_mul_of_nonneg_left (hω u τ hu huτ hτ) ((norm_nonneg _).trans (u16_norm_fderiv_le hΦ 0))
    _ = cbNorm 5 Φ * K * Gblk gd (a + T) ω := by ring

end IncInt

end HRS.MC.E213U16

end
