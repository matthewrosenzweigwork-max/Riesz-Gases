import HRS.MC.E214O3

/-!
# Packet E214O, part 4: `Dwin_relax_proof`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E214O

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan HRS.MC.E213Final
open HRS.MC.E214Plan

variable {d : ℕ}

section DwinRelax

variable {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} {sd : StatDatum S β₀ m hE}

/-- The `L^p` norm of a unit-block `L²`-norm of the stationary Wick field is bounded. -/
theorem o_Bblock_eLpNorm (gd : GaussData sd.Ss S.β sd.hEs) (p : ℝ) (hp : 1 ≤ p) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ k : ℕ, eLpNorm (fun ω => ‖toL2 (rLvl d) 1 (fun t => gd.B ((k : ℝ) + t) ω)‖)
      (ENNReal.ofReal p) gd.P₀ ≤ ENNReal.ofReal M := by
  obtain ⟨Mq, hMq0, hMq⟩ := HRS.MC.E213U11.u11_B_moment gd 1 one_pos p hp
  refine ⟨Mq ^ (1 / p), by positivity, fun k => ?_⟩
  obtain ⟨hm, hi, hb⟩ := hMq (k : ℝ) (Nat.cast_nonneg k)
  refine o_eLpNorm_of_moment gd.P₀ _ hm.norm.aestronglyMeasurable (by linarith) ?_ ?_
  · simpa only [norm_norm] using hi
  · simpa only [norm_norm] using hb

theorem Dwin_relax_proof (pg : PairGD sd) (T : ℝ) (hT : 0 < T) (p : ℝ) (hp : 1 ≤ p) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ a : ℝ, 0 ≤ a →
      eLpNorm (fun ω => pg.gd.Dwin T a ω - pg.gds.Dwin T a ω) (ENNReal.ofReal p) pg.P ≤
        ENNReal.ofReal (C * Real.exp (-c * a)) := by
  obtain ⟨C₁, c₁, hC₁, hc₁, hL1⟩ := HRS.MC.E214M.winDrift_L1_proof hE T hT
  obtain ⟨C₂, c₂, κ, hC₂, hc₂, hκ, hcmp⟩ := HRS.MC.E214K.winDrift_compare_proof sd T hT
  obtain ⟨CB, cB, hCB, hcB, hBe⟩ := HRS.MC.E214L.pair_B_exp_proof pg p hp
  obtain ⟨M, hM0, hM⟩ := o_Bblock_eLpNorm pg.gds p hp
  have hΦ : ∀ a : ℝ, 0 ≤ a → AEStronglyMeasurable (fun ω => pg.gd.Dwin T a ω - pg.gds.Dwin T a ω) pg.P := by
    intro a ha
    have h1 : AEStronglyMeasurable (pg.gd.Dwin T a) pg.P := HRS.MC.E213U11.u11_Dwin_aesm pg.gd T hT a ha
    have h2 : AEStronglyMeasurable (pg.gds.Dwin T a) pg.P := HRS.MC.E213U11.u11_Dwin_aesm pg.gds T hT a ha
    exact h1.sub h2
  refine o_relax pg.P (V := PathSpace d m T) hp hT hC₁.le hc₁ hC₂.le hc₂ hκ hCB.le hcB hM0
    (fun v ω => ‖pg.B v ω - pg.Bs v ω‖) (fun v ω => norm_nonneg _) ?_ hBe
    (fun k ω => ‖toL2 (rLvl d) 1 (fun t => pg.Bs ((k : ℝ) + t) ω)‖) hM
    (fun a ω => pg.gd.Dwin T a ω - pg.gds.Dwin T a ω) hΦ ?_
  · intro n
    have hB2 : Measurable fun x : pg.Ω × ℝ => pg.B x.2 x.1 := pg.B_meas.comp measurable_swap
    have hBs2 : Measurable fun x : pg.Ω × ℝ => pg.Bs x.2 x.1 := pg.Bs_meas.comp measurable_swap
    exact (hB2.sub hBs2).norm.aemeasurable
  · intro a ha
    have hHn : a + T ≤ (⌈a + T⌉₊ : ℝ) := Nat.le_ceil _
    have hn : (0 : ℝ) < (⌈a + T⌉₊ : ℝ) := by
      have : 0 < ⌈a + T⌉₊ := Nat.ceil_pos.2 (by linarith)
      exact_mod_cast this
    filter_upwards [HRS.MC.E213U11.u11_B_integrable pg.gd (⌈a + T⌉₊ : ℝ) hn,
      HRS.MC.E213U11.u11_B_integrable pg.gds (⌈a + T⌉₊ : ℝ) hn, HRS.MC.E213U11.u11_B_blocks pg.gds] with
      ω hi1 hi2 hblk
    show ‖pg.gd.Dwin T a ω - pg.gds.Dwin T a ω‖ ≤ _
    unfold GaussData.Dwin
    rw [dif_pos ha, dif_pos ha]
    exact o_drift_det sd T hT hC₂.le hc₂.le hκ.le hL1 hcmp a ha (fun v => pg.B v ω) (fun v => pg.Bs v ω)
      (HRS.MC.E213U11.u11_B_nearCoef_measurable pg.gd ω) (HRS.MC.E213U11.u11_B_nearCoef_measurable pg.gds ω)
      ⌈a + T⌉₊ hHn hi1 hi2 hblk

end DwinRelax

end HRS.MC.E214O

end
