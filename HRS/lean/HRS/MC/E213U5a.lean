import HRS.MC.E213U4
import HRS.MC.E213P
import HRS.MC.S7UCZ2
import HRS.MC.S7FCD4

/-!
# Packet e213u5 (Theorem 2.13, Wave 2): `Z_universal` and `chaos_conv`
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E213U5

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan

variable {d : ℕ}

section Gaussian

variable {S : PreparedData d} {β₀ m : ℝ}

section GD

variable {hE : EdgeworthHyp S β₀ m} (gd : GaussData S β₀ hE)

theorem Z_universal_proof (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a)
    (ν : Measure (NegSobolev d m)) (hν : IsCenteredGaussianWithCov m ν (preparedCov d S.s β₀ S.μ0))
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Z₀ : Ω' → NegSobolev d m) (Z : ℝ → Ω' → NegSobolev d m) (hZ : IsPreparedLinear S m (a + T) ν P' Z₀ Z) :
    AEMeasurable (HRS.Main.windowPath m T a Z) P' ∧ AEMeasurable (gd.Zwin T a) gd.P₀ ∧
      law P' (HRS.Main.windowPath m T a Z) = law gd.P₀ (gd.Zwin T a) ∧
      ∀ g : PathSpace d m T → ℝ, Continuous g →
        ∫ ω, g (HRS.Main.windowPath m T a Z ω) ∂P' = ∫ ω, g (gd.Zwin T a ω) ∂gd.P₀ := by
  obtain ⟨Y₀, -, hlin⟩ := gd.limit
  have hmeas : AEMeasurable (procWin (rLvl d) T a gd.η) gd.P₀ :=
    HRS.MC.Sec7.S7UCU.S7UCU_procWin_aemeasurable gd.P₀ (rLvl d) T hT gd.η a ha (fun t => (hlin 0).meas t)
      (hlin (a + T)).cont
  have hZw : AEMeasurable (gd.Zwin T a) gd.P₀ :=
    (HRS.MD.EQInterp.epath (rLvl_le hE) T).continuous.aemeasurable.comp_aemeasurable hmeas
  have hlaw : law P' (HRS.Main.windowPath m T a Z) = law gd.P₀ (gd.Zwin T a) := by
    rw [HRS.MC.E213P.e213p_window_law S β₀ m hE (rLvl d) rfl T a hT ha gd.P₀ gd.η gd.limit ν hν P' Z₀ Z hZ]
    exact AEMeasurable.map_map_of_aemeasurable (HRS.MD.EQInterp.epath (rLvl_le hE) T).continuous.aemeasurable
      hmeas
  have hWm : AEMeasurable (HRS.Main.windowPath m T a Z) P' :=
    HRS.MC.Sec7.S7UCU.S7UCU_procWin_aemeasurable P' m T hT Z a ha (fun t => hZ.sol.meas t) hZ.sol.cont
  refine ⟨hWm, hZw, hlaw, fun g hg => ?_⟩
  have e1 := integral_map (μ := P') hWm hg.aestronglyMeasurable (f := g)
  have e2 := integral_map (μ := gd.P₀) hZw hg.aestronglyMeasurable (f := g)
  have : ∫ x, g x ∂(law P' (HRS.Main.windowPath m T a Z)) = ∫ x, g x ∂(law gd.P₀ (gd.Zwin T a)) := by rw [hlaw]
  exact e1.symm.trans (this.trans e2)

theorem chaos_conv_proof (fam : PrepFamily S β₀ hE) :
    (∀ Rw : ℝ, 0 < Rw → ∀ p : ℝ, 1 ≤ p →
      Tendsto (fun N : ℕ => ⨆ a : {a : ℝ // 0 ≤ a},
        wassersteinE p (law (fam.P N) (pairN (rLvl d) Rw a.1 (regime S β₀ hE).D.s (regime S β₀ hE).ρ (fam.P N) (fam.X N)))
          (law gd.P₀ (pairLim (rLvl d) Rw a.1 gd.η gd.B))) atTop (𝓝 0)) ∧
    (∀ Rw : ℝ, 0 < Rw →
      Tendsto (fun N : ℕ => ⨆ a : {a : ℝ // 0 ≤ a},
        wassersteinE 2 (law (fam.P N) (HRS.Main.windowFluc (rLvl d) Rw a.1 (Real.sqrt N) (fam.X N) (regime S β₀ hE).ρ))
          (law gd.P₀ (procWin (rLvl d) Rw a.1 gd.η))) atTop (𝓝 0)) := by
  have hUC : HRS.MC.Sec7.UCPlan.UCField (regime S β₀ hE) (rLvl d) gd.P₀ gd.η gd.B :=
    ⟨gd.B_meas, gd.B_wick, fun T hT a ha => gd.B_L2 T hT a ha⟩
  refine ⟨fun Rw hRw p hp => ?_, fun Rw hRw => ?_⟩
  · exact HRS.MC.Sec7.S7UCZ.s7_UC_Wq_every_B_proof (regime S β₀ hE) (rLvl d) rfl Rw hRw fam.P fam.X₀ fam.W fam.X
      fam.hreal gd.P₀ gd.η gd.limit gd.B hUC p hp
  · exact HRS.MC.Sec7.S7FCD4.s7_FC_D4_eta_W2_proof (regime S β₀ hE) (rLvl d) rfl Rw hRw fam.P fam.X₀ fam.W fam.X
      fam.hreal gd.P₀ gd.η gd.limit

end GD

end Gaussian

end HRS.MC.E213U5

end
