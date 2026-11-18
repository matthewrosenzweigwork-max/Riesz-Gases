import HRS.MC.E213U16u

/-!
# Packet e213u16, file v: second derivative of the heat function; one-step identity for the covariance increments
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace HRS.MC.E213U16

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Q HRS.MC.E213U13 HRS.MC.E213Plan
open HRS.MC.E213U10 HRS.MC.E213U11

variable {d : ℕ}

section HeatIter2

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [MeasurableSpace Z] [OpensMeasurableSpace Z]
  [SecondCountableTopology Z]

theorem u16_norm_iter2_le {Φ : B → ℝ} (hΦ : MemCb 5 Φ) (x : B) : ‖iteratedFDeriv ℝ 2 Φ x‖ ≤ cbNorm 5 Φ :=
  HRS.Sec7.Tilt715Aux.norm_iter_le_cbNorm hΦ (j := 2) (by norm_num) x

theorem u16_iter2_cont {Φ : B → ℝ} (hΦ : MemCb 5 Φ) : Continuous (iteratedFDeriv ℝ 2 Φ) :=
  hΦ.1.continuous_iteratedFDeriv (by norm_num)

theorem u16_heat_iter2 (ν : Measure Z) [IsProbabilityMeasure ν] (R : Z →L[ℝ] B) {Φ : B → ℝ} (hΦ : MemCb 5 Φ)
    (y : B) (Δ : (B [×2]→L[ℝ] ℝ) →L[ℝ] ℝ) :
    Δ (iteratedFDeriv ℝ 2 (fun y => ∫ z, Φ (y + R z) ∂ν) y) = ∫ z, Δ (iteratedFDeriv ℝ 2 Φ (y + R z)) ∂ν := by
  obtain ⟨-, h⟩ := HRS.MC.E213U5.e213u5_heat_deriv ν R hΦ
  rw [h 2 (by norm_num) y]
  have hcont : Continuous fun z => iteratedFDeriv ℝ 2 Φ (y + R z) :=
    (u16_iter2_cont hΦ).comp (continuous_const.add R.continuous)
  have hc : Integrable (fun z => iteratedFDeriv ℝ 2 Φ (y + R z)) ν :=
    Integrable.of_bound hcont.aestronglyMeasurable (cbNorm 5 Φ)
      (Eventually.of_forall fun z => u16_norm_iter2_le hΦ _)
  exact (ContinuousLinearMap.integral_comp_comm Δ hc).symm

end HeatIter2


section OneStepJ

variable {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} (gd : GaussData S β₀ hE)

theorem u16_Wnorm_integrable (L : ℝ) (hL : 0 < L) :
    Integrable (fun ω => ‖procWin (rLvl d) L 0 gd.η ω‖) gd.P₀ := by
  obtain ⟨C, -, hC⟩ := u11_eta_moment gd L hL 1 le_rfl
  have := (hC 0 le_rfl).2.1
  simpa using this

theorem u16_Wtau_aem (L : ℝ) (hL : 0 < L) : AEMeasurable (procWin (rLvl d) L 0 gd.η) gd.P₀ := by
  obtain ⟨C, -, hC⟩ := u11_eta_moment gd L hL 1 le_rfl
  exact (hC 0 le_rfl).1

theorem u16_Ucan_iter2_bound (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a)
    (Φ : PathSpace d m T → ℝ) (hΦ : MemCb 5 Φ) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) (a + T))
    (y : PathSpace d m T) : ‖iteratedFDeriv ℝ 2 (Ucan hE T a ha Φ τ) y‖ ≤ cbNorm 5 Φ := by
  have hH : 0 < a + T := by linarith
  haveI : IsProbabilityMeasure (canonFut hE (a + T) τ) :=
    (HRS.MC.E213U5.e213u5_canonFut_spec hE (a + T) hH τ hτ).2
  obtain ⟨-, h⟩ := HRS.MC.E213U5.e213u5_heat_deriv (canonFut hE (a + T) τ) (winRestr a ha) hΦ
  rw [u16_Ucan_eq, h 2 (by norm_num) y]
  have := norm_integral_le_of_norm_le_const (μ := canonFut hE (a + T) τ)
    (f := fun z => iteratedFDeriv ℝ 2 Φ (y + winRestr a ha z)) (C := cbNorm 5 Φ)
    (Eventually.of_forall fun z => u16_norm_iter2_le hΦ _)
  simpa using this

theorem u16_Ucan_iter2_cont (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a)
    (Φ : PathSpace d m T → ℝ) (hΦ : MemCb 5 Φ) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) (a + T)) :
    Continuous (iteratedFDeriv ℝ 2 (Ucan hE T a ha Φ τ)) := by
  have hH : 0 < a + T := by linarith
  haveI : IsProbabilityMeasure (canonFut hE (a + T) τ) :=
    (HRS.MC.E213U5.e213u5_canonFut_spec hE (a + T) hH τ hτ).2
  have hc := (HRS.MC.E213U5.e213u5_heat_deriv (canonFut hE (a + T) τ) (winRestr a ha) hΦ).1
  have hc' : ContDiff ℝ 5 (Ucan hE T a ha Φ τ) := hc
  exact hc'.continuous_iteratedFDeriv (by norm_num)

set_option maxHeartbeats 800000 in
theorem u16_cond_incJ (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) (Φ : PathSpace d m T → ℝ) (hΦ : MemCb 5 Φ)
    {u τ : ℝ} (hu : 0 ≤ u) (huτ : u ≤ τ) (hτ : τ ≤ a + T) (hτ0 : 0 < τ) :
    ∫ ω, winJ (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (gd.η v ω)) (Set.Ioc u τ)
        (iteratedFDeriv ℝ 2 Φ (gd.Zwin T a ω)) ∂gd.P₀ =
      ∫ ω, winJ (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (gd.η v ω)) (Set.Ioc u τ)
        (iteratedFDeriv ℝ 2 (Ucan hE T a ha Φ τ)
          (winPred (regime S β₀ hE) m T a ha (gd.Zwin (a + T) 0 ω) τ)) ∂gd.P₀ := by
  classical
  have hH : 0 < a + T := by linarith
  have hτI : τ ∈ Set.Icc (0 : ℝ) (a + T) := ⟨hτ0.le, hτ⟩
  obtain ⟨Λ, W', ⟨CΛ, hCΛ0, hCΛ⟩, hW', haeW, hJ⟩ := u16_Jinc_past gd T hT a ha hu huτ hτ hτ0
  set Y : gd.Ω₀ → PathSpace d m T := fun ω => winPred (regime S β₀ hE) m T a ha (gd.Zwin (a + T) 0 ω) τ with hY
  set Wt : gd.Ω₀ → PathSpace d (rLvl d) τ := fun ω => procWin (rLvl d) τ 0 gd.η ω with hWt
  set Γ : gd.Ω₀ → PathSpace d m (a + T) := Gam gd (a + T) τ with hΓ
  obtain ⟨Y', hY', haeY⟩ := u16_Y_past gd T hT a ha hτI
  obtain ⟨γ', hγ', haeγ⟩ := u16_Gam_fut gd hH hτI
  have hind : IndepFun (fun ω => (Y ω, Wt ω)) Γ gd.P₀ := by
    refine u16_indepFun_of_sig gd hH hτI ⟨fun ω => (Y' ω, W' ω), ?_, haeY.prodMk haeW⟩ ⟨γ', hγ', haeγ⟩
    letI : MeasurableSpace gd.Ω₀ := pastSig gd τ
    exact hY'.prodMk hW'
  have hvm : AEMeasurable (fun ω => (Y ω, Wt ω)) gd.P₀ :=
    ((hY'.mono (pastSig_le gd hτI) le_rfl).prodMk (hW'.mono (pastSig_le gd hτI) le_rfl)).aemeasurable.congr
      (haeY.prodMk haeW).symm
  have hΓm : AEMeasurable Γ gd.P₀ := u16_Gam_aemeasurable gd (a + T) hH hτI
  haveI : IsProbabilityMeasure (canonFut hE (a + T) τ) := (HRS.MC.E213U5.e213u5_canonFut_spec hE (a + T) hH τ hτI).2
  set F : PathSpace d m T × PathSpace d (rLvl d) τ → PathSpace d m (a + T) → ℝ :=
    fun p w => Λ p.2 (iteratedFDeriv ℝ 2 Φ (p.1 + winRestr a ha w)) with hF
  have hFc : Continuous (Function.uncurry F) := by
    have h1 : Continuous fun q : (PathSpace d m T × PathSpace d (rLvl d) τ) × PathSpace d m (a + T) =>
        iteratedFDeriv ℝ 2 Φ (q.1.1 + winRestr a ha q.2) :=
      (u16_iter2_cont hΦ).comp (continuous_fst.comp continuous_fst |>.add
        ((winRestr a ha).continuous.comp continuous_snd))
    exact (Λ.continuous.comp (continuous_snd.comp continuous_fst)).clm_apply h1
  have hWi := u16_Wnorm_integrable gd τ hτ0
  have hcb : 0 ≤ cbNorm 5 Φ := (norm_nonneg _).trans (u16_norm_fderiv_le hΦ 0)
  have hint : Integrable (fun ω => F (Y ω, Wt ω) (Γ ω)) gd.P₀ := by
    have hmeas : AEStronglyMeasurable (fun ω => F (Y ω, Wt ω) (Γ ω)) gd.P₀ := by
      have := hFc.aestronglyMeasurable.comp_aemeasurable (hvm.prodMk hΓm)
      exact this
    refine (hWi.const_mul (CΛ * cbNorm 5 Φ)).mono' hmeas (Eventually.of_forall fun ω => ?_)
    calc ‖F (Y ω, Wt ω) (Γ ω)‖ ≤ ‖Λ (Wt ω)‖ * ‖iteratedFDeriv ℝ 2 Φ (Y ω + winRestr a ha (Γ ω))‖ :=
          (Λ (Wt ω)).le_opNorm _
      _ ≤ (CΛ * ‖Wt ω‖) * cbNorm 5 Φ :=
          mul_le_mul (hCΛ _) (u16_norm_iter2_le hΦ _) (norm_nonneg _) (by positivity)
      _ = CΛ * cbNorm 5 Φ * ‖Wt ω‖ := by ring
  have hacl := u16_acl hvm hΓm hind (F := F) hFc.stronglyMeasurable hint
  rw [u16_Gam_law gd hH hτI] at hacl
  have hZ : ∀ᵐ ω ∂gd.P₀, gd.Zwin T a ω = Y ω + winRestr a ha (Γ ω) := by
    filter_upwards [u16_Zwin_restr gd T hT a ha] with ω hω
    rw [hω]
    simp only [hY, hΓ, winPred, Gam]
    rw [← map_add]
    congr 1
    abel
  calc ∫ ω, winJ (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (gd.η v ω)) (Set.Ioc u τ)
        (iteratedFDeriv ℝ 2 Φ (gd.Zwin T a ω)) ∂gd.P₀ = ∫ ω, F (Y ω, Wt ω) (Γ ω) ∂gd.P₀ := by
        refine integral_congr_ae ?_
        filter_upwards [hZ, hJ] with ω hω hJω
        simp only [hF]
        rw [hω, hJω]
    _ = ∫ ω, (∫ w, F (Y ω, Wt ω) w ∂(canonFut hE (a + T) τ)) ∂gd.P₀ := hacl
    _ = ∫ ω, Λ (Wt ω) (iteratedFDeriv ℝ 2 (Ucan hE T a ha Φ τ) (Y ω)) ∂gd.P₀ := by
        refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
        simp only [hF]
        exact (u16_heat_iter2 (canonFut hE (a + T) τ) (winRestr a ha) hΦ (Y ω) (Λ (Wt ω))).symm
    _ = _ := by
        refine integral_congr_ae ?_
        filter_upwards [hJ] with ω hJω
        rw [hJω]

end OneStepJ

end HRS.MC.E213U16

end
