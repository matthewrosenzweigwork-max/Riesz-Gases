import HRS.MC.E213U16i

/-!
# Packet e213u16, file j: measurability of the predicted window and of the future noise
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace HRS.MC.E213U16

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Q HRS.MC.E213U13 HRS.MC.E213Plan
open HRS.MC.E213U10

variable {d : ℕ}

section Fut

variable {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} (gd : GaussData S β₀ hE)

/-- The future noise is (a.e. equal to) a `futSig`-measurable map. -/
theorem u16_Gam_fut {H : ℝ} (hH : 0 < H) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) H) :
    ∃ γ' : gd.Ω₀ → PathSpace d m H, Measurable[futSig gd τ H] γ' ∧ Gam gd H τ =ᵐ[gd.P₀] γ' := by
  refine u16_path_meas (μ := gd.P₀) (W := Gam gd H τ) (futSig gd τ H) hH fun t ht ψ hψ => ?_
  by_cases h : τ < t
  · refine ⟨Ys gd τ H (⟨t, h, ht.2⟩, ⟨ψ, hψ⟩), futSig_meas_Ys gd τ H _, ?_⟩
    filter_upwards [u16_Gam_eval_ae gd hH hτ ht hψ] with ω hω
    rw [hω, if_pos h, u16_Ys_eq gd hτ.1]
  · refine ⟨fun _ => 0, @measurable_const _ _ _ (futSig gd τ H) _, ?_⟩
    filter_upwards [u16_Gam_eval_ae gd hH hτ ht hψ] with ω hω
    rw [hω, if_neg h]

end Fut


section Past

variable {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} (gd : GaussData S β₀ hE)

theorem u16_PZ_eval_ae {H : ℝ} (hH : 0 < H) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) H) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) H) {ψ : Torus d → ℝ} (hψ : Torus.IsSmooth ψ) :
    ∀ᵐ ω ∂gd.P₀, NegSobolev.eval (pathAt (predicted (regime S β₀ hE).D (regime S β₀ hE).ρ (gd.Zwin H 0 ω) τ) t) ψ =
      if t ≤ τ then NegSobolev.eval (gd.η t ω) ψ else NegSobolev.eval (gd.η τ ω) (propagator S.dyn S.ρ τ t ψ) := by
  filter_upwards [HRS.MC.E213U11.u11_eta_cont gd H] with ω hc
  rw [u16_predicted_pathAt hE hH _ hτ ht]
  by_cases h : t ≤ τ
  · rw [if_pos h, if_pos h, u16_Z_at gd hH hc ht, HRS.MD.EQGaussLift.eqgl_eval_embed (rLvl_le hE)]
  · rw [if_neg h, if_neg h, u16_Z_at gd hH hc hτ,
      u16_V_eval (HRS.MC.E213A.regimeOfPrepared S β₀ hE) m hE.m_gt hτ.1 (not_le.1 h).le _ hψ,
      HRS.MD.EQGaussLift.eqgl_eval_embed (rLvl_le hE)]
    rfl

/-- The predicted path `𝖳_τ Z` is (a.e. equal to) a `pastSig`-measurable map. -/
theorem u16_PZ_past {H : ℝ} (hH : 0 < H) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) H) :
    ∃ P' : gd.Ω₀ → PathSpace d m H, Measurable[pastSig gd τ] P' ∧
      (fun ω => predicted (regime S β₀ hE).D (regime S β₀ hE).ρ (gd.Zwin H 0 ω) τ) =ᵐ[gd.P₀] P' := by
  refine u16_path_meas (μ := gd.P₀) (W := fun ω => predicted (regime S β₀ hE).D (regime S β₀ hE).ρ (gd.Zwin H 0 ω) τ)
    (pastSig gd τ) hH fun t ht ψ hψ => ?_
  by_cases h : t ≤ τ
  · refine ⟨Xs gd τ (⟨t, ht.1, h⟩, ⟨ψ, hψ⟩), pastSig_meas_Xs gd τ _, ?_⟩
    filter_upwards [u16_PZ_eval_ae gd hH hτ ht hψ] with ω hω
    rw [hω, if_pos h]
    rfl
  · refine ⟨Xs gd τ (⟨τ, hτ.1, le_rfl⟩, ⟨propagator S.dyn S.ρ τ t ψ, u16_prop_smooth hE hψ hτ.1 (not_le.1 h).le⟩),
      pastSig_meas_Xs gd τ _, ?_⟩
    filter_upwards [u16_PZ_eval_ae gd hH hτ ht hψ] with ω hω
    rw [hω, if_neg h]
    rfl

/-- The predicted window `Y^τ = R_a 𝖳_τ Z` is (a.e. equal to) a `pastSig`-measurable map. -/
theorem u16_Y_past (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) (a + T)) :
    ∃ Y' : gd.Ω₀ → PathSpace d m T, Measurable[pastSig gd τ] Y' ∧
      (fun ω => winPred (regime S β₀ hE) m T a ha (gd.Zwin (a + T) 0 ω) τ) =ᵐ[gd.P₀] Y' := by
  have hH : 0 < a + T := by linarith
  obtain ⟨P', hP', hae⟩ := u16_PZ_past gd hH hτ
  refine ⟨fun ω => winRestr a ha (P' ω), @Measurable.comp _ _ _ (pastSig gd τ) _ _ _ _
    (winRestr a ha).continuous.measurable hP', ?_⟩
  filter_upwards [hae] with ω hω
  simp only [winPred]
  rw [hω]

end Past


section ZwinRestr

variable {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} (gd : GaussData S β₀ hE)

theorem u16_Zwin_at (T a : ℝ) (ha : 0 ≤ a) {ω : gd.Ω₀}
    (hc : ContinuousOn (fun t => gd.η t ω) (Set.Icc 0 (a + T))) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    pathAt (gd.Zwin T a ω) t = NegSobolev.embed m (gd.η (a + t) ω) := by
  unfold pathAt
  rw [dif_pos ht]
  have h1 := e213q_procWin_at (m := rLvl d) (Z := gd.η) T a ha ω hc ⟨t, ht⟩
  unfold GaussData.Zwin
  rw [HRS.MD.EQInterp.epath_at', h1]

/-- `Z_a = R_a Z` almost surely. -/
theorem u16_Zwin_restr (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) :
    ∀ᵐ ω ∂gd.P₀, gd.Zwin T a ω = winRestr a ha (gd.Zwin (a + T) 0 ω) := by
  filter_upwards [HRS.MC.E213U11.u11_eta_cont gd (a + T)] with ω hc
  refine u10_path_ext fun t ht => ?_
  have hat : a + t ∈ Set.Icc (0 : ℝ) (a + T) := ⟨add_nonneg ha ht.1, by linarith [ht.2]⟩
  rw [u16_Zwin_at gd T a ha hc ht, winRestr_pathAt a ha _ ht, u16_Z_at gd (by linarith) hc hat]

end ZwinRestr

end HRS.MC.E213U16

end
