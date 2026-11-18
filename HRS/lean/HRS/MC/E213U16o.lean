import HRS.MC.E213U16n

/-!
# Packet e213u16, file o: first derivative of the heat function; the one-step conditioning identity
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace HRS.MC.E213U16

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Q HRS.MC.E213U13 HRS.MC.E213Plan
open HRS.MC.E213U10

variable {d : ℕ}

section HeatFderiv

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [MeasurableSpace Z] [OpensMeasurableSpace Z]
  [SecondCountableTopology Z]

theorem u16_norm_fderiv_le {Φ : B → ℝ} (hΦ : MemCb 5 Φ) (x : B) : ‖fderiv ℝ Φ x‖ ≤ cbNorm 5 Φ := by
  have h := HRS.Sec7.Tilt715Aux.norm_iter_le_cbNorm hΦ (j := 1) (by norm_num) x
  have e := HRS.MC.E213U7.e213u7_curry_iter Φ x
  rw [← e]
  simpa using h

theorem u16_heat_fderiv (ν : Measure Z) [IsProbabilityMeasure ν] (R : Z →L[ℝ] B) {Φ : B → ℝ} (hΦ : MemCb 5 Φ)
    (y δ : B) :
    fderiv ℝ (fun y => ∫ z, Φ (y + R z) ∂ν) y δ = ∫ z, fderiv ℝ Φ (y + R z) δ ∂ν := by
  obtain ⟨-, h⟩ := HRS.MC.E213U5.e213u5_heat_deriv ν R hΦ
  have h1 := h 1 (by norm_num) y
  have hcont : Continuous fun z => fderiv ℝ Φ (y + R z) :=
    (hΦ.1.continuous_fderiv (by norm_num)).comp (continuous_const.add R.continuous)
  have hc : Integrable (fun z => fderiv ℝ Φ (y + R z)) ν :=
    Integrable.of_bound hcont.aestronglyMeasurable (cbNorm 5 Φ)
      (Eventually.of_forall fun z => u16_norm_fderiv_le hΦ _)
  have e : ∀ x, continuousMultilinearCurryFin1 ℝ B ℝ (iteratedFDeriv ℝ 1 Φ x) = fderiv ℝ Φ x :=
    fun x => HRS.MC.E213U7.e213u7_curry_iter Φ x
  calc fderiv ℝ (fun y => ∫ z, Φ (y + R z) ∂ν) y δ
      = (continuousMultilinearCurryFin1 ℝ B ℝ
          (iteratedFDeriv ℝ 1 (fun y => ∫ z, Φ (y + R z) ∂ν) y)) δ := by
        rw [HRS.MC.E213U7.e213u7_curry_iter]
    _ = (continuousMultilinearCurryFin1 ℝ B ℝ (∫ z, iteratedFDeriv ℝ 1 Φ (y + R z) ∂ν)) δ := by rw [h1]
    _ = (∫ z, continuousMultilinearCurryFin1 ℝ B ℝ (iteratedFDeriv ℝ 1 Φ (y + R z)) ∂ν) δ := by
        have := (continuousMultilinearCurryFin1 ℝ B ℝ).toContinuousLinearEquiv.integral_comp_comm
          (fun z => iteratedFDeriv ℝ 1 Φ (y + R z)) (μ := ν)
        exact congrArg (fun F => F δ) this.symm
    _ = ∫ z, fderiv ℝ Φ (y + R z) δ ∂ν := by
        simp_rw [e]
        exact ContinuousLinearMap.integral_apply hc δ

end HeatFderiv


section OneStep

variable {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} (gd : GaussData S β₀ hE)

set_option maxHeartbeats 800000 in
theorem u16_cond_inc (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) (Φ : PathSpace d m T → ℝ) (hΦ : MemCb 5 Φ)
    {u τ : ℝ} (hu : 0 ≤ u) (huτ : u ≤ τ) (hτ : τ ≤ a + T) :
    ∫ ω, fderiv ℝ Φ (gd.Zwin T a ω)
        (winDrift (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (gd.B v ω)) u τ) ∂gd.P₀ =
      ∫ ω, fderiv ℝ (Ucan hE T a ha Φ τ) (winPred (regime S β₀ hE) m T a ha (gd.Zwin (a + T) 0 ω) τ)
        (winDrift (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (gd.B v ω)) u τ) ∂gd.P₀ := by
  classical
  have hH : 0 < a + T := by linarith
  have hτI : τ ∈ Set.Icc (0 : ℝ) (a + T) := ⟨hu.trans huτ, hτ⟩
  set Y : gd.Ω₀ → PathSpace d m T := fun ω => winPred (regime S β₀ hE) m T a ha (gd.Zwin (a + T) 0 ω) τ with hY
  set Δ : gd.Ω₀ → PathSpace d m T := fun ω =>
    winDrift (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (gd.B v ω)) u τ with hΔ
  set Γ : gd.Ω₀ → PathSpace d m (a + T) := Gam gd (a + T) τ with hΓ
  obtain ⟨Y', hY', haeY⟩ := u16_Y_past gd T hT a ha hτI
  obtain ⟨Δ', hΔ', haeΔ⟩ := u16_winDrift_past gd T hT a ha hu huτ hτ
  obtain ⟨γ', hγ', haeγ⟩ := u16_Gam_fut gd hH hτI
  have hind : IndepFun (fun ω => (Y ω, Δ ω)) Γ gd.P₀ := by
    refine u16_indepFun_of_sig gd hH hτI ⟨fun ω => (Y' ω, Δ' ω), ?_, haeY.prodMk haeΔ⟩ ⟨γ', hγ', haeγ⟩
    letI : MeasurableSpace gd.Ω₀ := pastSig gd τ
    exact hY'.prodMk hΔ'
  have hvm : AEMeasurable (fun ω => (Y ω, Δ ω)) gd.P₀ :=
    ((hY'.mono (pastSig_le gd hτI) le_rfl).prodMk (hΔ'.mono (pastSig_le gd hτI) le_rfl)).aemeasurable.congr
      (haeY.prodMk haeΔ).symm
  have hΓm : AEMeasurable Γ gd.P₀ := u16_Gam_aemeasurable gd (a + T) hH hτI
  haveI : IsProbabilityMeasure (canonFut hE (a + T) τ) := (HRS.MC.E213U5.e213u5_canonFut_spec hE (a + T) hH τ hτI).2
  set F : PathSpace d m T × PathSpace d m T → PathSpace d m (a + T) → ℝ :=
    fun p w => fderiv ℝ Φ (p.1 + winRestr a ha w) p.2 with hF
  have hFc : Continuous (Function.uncurry F) := by
    have h1 : Continuous fun q : (PathSpace d m T × PathSpace d m T) × PathSpace d m (a + T) =>
        fderiv ℝ Φ (q.1.1 + winRestr a ha q.2) :=
      (hΦ.1.continuous_fderiv (by norm_num)).comp (continuous_fst.comp continuous_fst |>.add
        ((winRestr a ha).continuous.comp continuous_snd))
    exact h1.clm_apply (continuous_snd.comp continuous_fst)
  -- integrability
  obtain ⟨K, hK, hKb⟩ := u16_Dinc_bound gd T hT a ha
  have hint : Integrable (fun ω => F (Y ω, Δ ω) (Γ ω)) gd.P₀ := by
    have hmeas : AEStronglyMeasurable (fun ω => F (Y ω, Δ ω) (Γ ω)) gd.P₀ := by
      have := hFc.aestronglyMeasurable.comp_aemeasurable (hvm.prodMk hΓm)
      exact this
    refine ((u16_Gblk_integrable gd (a + T)).const_mul (cbNorm 5 Φ * K)).mono' hmeas ?_
    filter_upwards [hKb] with ω hω
    calc ‖F (Y ω, Δ ω) (Γ ω)‖ ≤ ‖fderiv ℝ Φ (Y ω + winRestr a ha (Γ ω))‖ * ‖Δ ω‖ :=
          (fderiv ℝ Φ _).le_opNorm _
      _ ≤ cbNorm 5 Φ * (K * Gblk gd (a + T) ω) :=
          mul_le_mul (u16_norm_fderiv_le hΦ _) (hω u τ hu huτ hτ) (norm_nonneg _)
            ((norm_nonneg _).trans (u16_norm_fderiv_le hΦ 0))
      _ = cbNorm 5 Φ * K * Gblk gd (a + T) ω := by ring
  have hacl := u16_acl hvm hΓm hind (F := F) hFc.stronglyMeasurable hint
  rw [u16_Gam_law gd hH hτI] at hacl
  have hZ : ∀ᵐ ω ∂gd.P₀, gd.Zwin T a ω = Y ω + winRestr a ha (Γ ω) := by
    filter_upwards [u16_Zwin_restr gd T hT a ha] with ω hω
    rw [hω]
    simp only [hY, hΓ, winPred, Gam]
    rw [← map_add]
    congr 1
    abel
  calc ∫ ω, fderiv ℝ Φ (gd.Zwin T a ω) (Δ ω) ∂gd.P₀ = ∫ ω, F (Y ω, Δ ω) (Γ ω) ∂gd.P₀ := by
        refine integral_congr_ae ?_
        filter_upwards [hZ] with ω hω
        simp only [hF]
        rw [hω]
    _ = ∫ ω, (∫ w, F (Y ω, Δ ω) w ∂(canonFut hE (a + T) τ)) ∂gd.P₀ := hacl
    _ = _ := by
        refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
        simp only [hF]
        exact (u16_heat_fderiv (canonFut hE (a + T) τ) (winRestr a ha) hΦ (Y ω) (Δ ω)).symm

end OneStep

end HRS.MC.E213U16

end
