import HRS.MC.E214O5
import HRS.MC.E214L2

/-!
# Packet E214O, part 6: `Jwin_relax_cond_proof`

The plan statement `Jwin_relax` with the extra hypothesis `WinJCompare sd T hT` (the covariance-tensor comparison
`winJ_compare`, the one unproved analytic input).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E214O

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan HRS.MC.E213Final
open HRS.MC.E214Plan

variable {d : ℕ}

section JwinRelax

variable {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} {sd : StatDatum S β₀ m hE}

/-- The `L^p` norm of a unit-block supremum of the stationary field is bounded. -/
theorem o_etablock_eLpNorm (gd : GaussData sd.Ss S.β sd.hEs) (p : ℝ) (hp : 1 ≤ p) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ k : ℕ, eLpNorm (fun ω => ‖procWin (rLvl d) 1 (k : ℝ) gd.η ω‖)
      (ENNReal.ofReal p) gd.P₀ ≤ ENNReal.ofReal M := by
  obtain ⟨Mq, hMq0, hMq⟩ := HRS.MC.E213U11.u11_eta_moment gd 1 one_pos p hp
  refine ⟨Mq ^ (1 / p), by positivity, fun k => ?_⟩
  obtain ⟨hm, hi, hb⟩ := hMq (k : ℝ) (Nat.cast_nonneg k)
  refine o_eLpNorm_of_moment gd.P₀ _ hm.norm.aestronglyMeasurable (by linarith) ?_ ?_
  · simpa only [norm_norm] using hi
  · simpa only [norm_norm] using hb

theorem Jwin_relax_cond_proof (pg : PairGD sd) (T : ℝ) (hT : 0 < T) (hJ : WinJCompare sd T hT) (p : ℝ)
    (hp : 1 ≤ p) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ a : ℝ, 0 ≤ a →
      eLpNorm (fun ω => pg.gd.Jwin T a ω - pg.gds.Jwin T a ω) (ENNReal.ofReal p) pg.P ≤
        ENNReal.ofReal (C * Real.exp (-c * a)) := by
  obtain ⟨C₁, c₁, hC₁, hc₁, hL1⟩ := HRS.MC.E214M.winJ_L1_proof hE T hT
  obtain ⟨C₂, c₂, κ, hC₂, hc₂, hκ, hcmp⟩ := hJ
  obtain ⟨CF, cF, hCF, hcF, hFt⟩ := HRS.MC.E214L.pair_fixed_time_proof pg p hp
  obtain ⟨M, hM0, hM⟩ := o_etablock_eLpNorm pg.gds p hp
  obtain ⟨-, -, -, hη, hηs, -⟩ := id pg.pair
  have hc_ae : ∀ᵐ ω ∂pg.P, ContinuousOn (fun t => pg.η t ω) (Set.Ici 0) :=
    HRS.MC.E214G.ae_continuousOn_Ici_of_nat' pg.P pg.η (fun n => (hη (n : ℝ)).cont)
  have hcs_ae : ∀ᵐ ω ∂pg.P, ContinuousOn (fun t => pg.ηs t ω) (Set.Ici 0) :=
    HRS.MC.E214G.ae_continuousOn_Ici_of_nat' pg.P pg.ηs (fun n => (hηs (n : ℝ)).cont)
  have hΦ : ∀ a : ℝ, 0 ≤ a → AEStronglyMeasurable (fun ω => pg.gd.Jwin T a ω - pg.gds.Jwin T a ω) pg.P := by
    intro a ha
    have h1 : AEStronglyMeasurable (pg.gd.Jwin T a) pg.P := (HRS.MC.E213U11.u11_Jwin_aesm_mem pg.gd T hT a ha).1
    have h2 : AEStronglyMeasurable (pg.gds.Jwin T a) pg.P := (HRS.MC.E213U11.u11_Jwin_aesm_mem pg.gds T hT a ha).1
    exact h1.sub h2
  refine o_relax pg.P (V := TensorDual (PathSpace d m T) 2) hp hT hC₁.le hc₁ hC₂.le hc₂ hκ hCF.le hcF hM0
    (fun v ω => ‖pg.η v ω - pg.ηs v ω‖) (fun v ω => norm_nonneg _) ?_
    (ae_restrict_of_forall_mem measurableSet_Ici (fun t ht => hFt t ht))
    (fun k ω => ‖procWin (rLvl d) 1 (k : ℝ) pg.ηs ω‖) hM
    (fun a ω => pg.gd.Jwin T a ω - pg.gds.Jwin T a ω) hΦ ?_
  · intro n
    refine o_aemeasurable_prod pg.P (fun t ω => ‖pg.η t ω - pg.ηs t ω‖)
      (fun t => (((hη 0).meas t).sub ((hηs 0).meas t)).norm) ?_ n
    filter_upwards [hc_ae, hcs_ae] with ω h1 h2
    exact (h1.sub h2).norm
  · intro a ha
    have hHn : a + T ≤ (⌈a + T⌉₊ : ℝ) := Nat.le_ceil _
    filter_upwards [hc_ae, hcs_ae] with ω h1 h2
    show ‖pg.gd.Jwin T a ω - pg.gds.Jwin T a ω‖ ≤ _
    unfold GaussData.Jwin
    rw [dif_pos ha, dif_pos ha]
    exact o_J_det sd T hT hC₂.le hc₂.le hκ.le hL1 hcmp a ha (fun v => pg.η v ω) (fun v => pg.ηs v ω) h1 h2
      ⌈a + T⌉₊ hHn (fun k => ‖procWin (rLvl d) 1 (k : ℝ) pg.ηs ω‖)
      (fun k _ v hv => HRS.MC.E213U11.u11_procWin_norm_ge pg.ηs 1 (k : ℝ) ω
        (h2.mono (fun x hx => le_trans (Nat.cast_nonneg k) hx.1)) zero_le_one hv)

end JwinRelax

end HRS.MC.E214O

end
