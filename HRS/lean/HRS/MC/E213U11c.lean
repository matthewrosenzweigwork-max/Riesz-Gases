import HRS.MC.E213U11b
import HRS.Uniform.Q45Ten1

/-!
# Packet e213u11, file c: measurability of the window drift `D_a` of the canonical data
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E213U11

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan

variable {d : ℕ}

section DriftMeas

variable {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} (gd : GaussData S β₀ hE)

theorem u11_B_integrable (H : ℝ) (hH : 0 < H) :
    ∀ᵐ ω ∂gd.P₀, IntegrableOn (fun v => ‖gd.B v ω‖) (Set.Icc 0 H) := by
  filter_upwards [gd.B_L2 H hH 0 le_rfl] with ω hω
  have h := hω.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  simp only [zero_add] at h
  exact (show IntegrableOn (fun t => gd.B t ω) (Set.Icc 0 H) volume from h).norm

theorem u11_B_measurable (ω : gd.Ω₀) : Measurable (fun v => gd.B v ω) :=
  gd.B_meas.comp (measurable_id.prodMk measurable_const)

theorem u11_B_nearCoef_measurable (ω : gd.Ω₀) : Measurable (nearCoef 0 fun v => gd.B v ω) := by
  unfold nearCoef
  exact Measurable.ite measurableSet_Ici (u11_B_measurable gd ω) measurable_const


theorem u11_Dwin_aesm (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) :
    AEStronglyMeasurable (gd.Dwin T a) gd.P₀ := by
  classical
  obtain ⟨C, c, hC, hc, Vev, hsp⟩ := HRS.MC.E213U1.u1_vev hE
  have hsp' := hsp
  set H : ℝ := a + T with hHdef
  have hH : 0 < H := by rw [hHdef]; linarith
  set ι := HRS.MD.EQInterp.embedCLM (rLvl_le hE) with hι
  set Y : ℝ → gd.Ω₀ → NegSobolev d m := fun t ω =>
    ∫ u in Set.Ioc 0 (min H t), Vprop (regime S β₀ hE).D (regime S β₀ hE).ρ m t u
      (NegSobolev.embed m (gd.B u ω)) with hY
  have hgood := u11_B_integrable gd H hH
  have hYt : ∀ t ∈ Set.Icc (0 : ℝ) H, AEMeasurable (Y t) gd.P₀ := by
    intro t ht
    set G : gd.Ω₀ → NegSobolev d m := fun ω =>
      ∫ v in Set.Ioc 0 H, HRS.MC.E213U1.u1_F Vev (fun v => ι (gd.B v ω)) t v with hG
    have hGm : Measurable G := by
      have hΦ := HRS.MC.E213U1.u1_clamp_joint (hE := hE) hC hc hsp' ht.1 ht.2
      have hmeas : Measurable (Function.uncurry fun (ω : gd.Ω₀) (v : ℝ) =>
          HRS.MC.E213U1.u1_F Vev (fun v => ι (gd.B v ω)) t v) := by
        have : Function.uncurry (fun (ω : gd.Ω₀) (v : ℝ) =>
            HRS.MC.E213U1.u1_F Vev (fun v => ι (gd.B v ω)) t v) =
            fun p : gd.Ω₀ × ℝ => Set.indicator (Set.Iic t)
              (fun v => Vev t (HRS.MC.E213U1.u1_cl t v) (ι (gd.B v p.1))) p.2 := by
          funext p; rfl
        rw [this]
        have h1 : Measurable fun p : gd.Ω₀ × ℝ => (p.2, ι (gd.B p.2 p.1)) :=
          measurable_snd.prodMk (ι.continuous.measurable.comp (gd.B_meas.comp (measurable_snd.prodMk measurable_fst)))
        have h2 : Measurable fun p : gd.Ω₀ × ℝ => Vev t (HRS.MC.E213U1.u1_cl t p.2) (ι (gd.B p.2 p.1)) :=
          hΦ.measurable.comp h1
        refine Measurable.ite (measurableSet_preimage measurable_snd measurableSet_Iic) h2 measurable_const
      exact (hmeas.stronglyMeasurable.integral_prod_right (ν := volume.restrict (Set.Ioc 0 H))).measurable
    refine hGm.aemeasurable.congr ?_
    filter_upwards [hgood] with ω hω
    have := (HRS.MC.E213U1.u1_Fint hE hC hc hsp' T a hT ha (fun v => gd.B v ω)
      (u11_B_nearCoef_measurable gd ω) hω 0 H le_rfl le_rfl t ht).1
    exact this.symm
  have hcont : ∀ᵐ ω ∂gd.P₀, ContinuousOn (fun t => Y t ω) (Set.Icc 0 H) := by
    filter_upwards [hgood] with ω hω
    have := HRS.MC.E213U1.winDrift_cont_proof hE T hT a ha (fun v => gd.B v ω)
      (u11_B_nearCoef_measurable gd ω) hω 0 H le_rfl hH.le le_rfl
    exact continuousOn_iff_continuous_restrict.2 this
  have hW := HRS.Uniform.Q45.aemeasurable_windowPath' gd.P₀ hH Y hYt hcont
  have hD : gd.Dwin T a = fun ω => winRestr a ha (HRS.Uniform.windowPath 0 H Y ω) := by
    funext ω
    unfold GaussData.Dwin winDrift driftInc Sec7.pathOf HRS.Uniform.windowPath
    rw [dif_pos ha]
    congr 1
    refine HRS.MC.Sec7.S7FCF5I.S7FCF5I_dite_congr _ _ ?_
    funext t
    simp only [zero_add]
    rfl
  rw [hD]
  exact ((winRestr a ha).continuous.aemeasurable.comp_aemeasurable hW).aestronglyMeasurable

end DriftMeas

end HRS.MC.E213U11

end
