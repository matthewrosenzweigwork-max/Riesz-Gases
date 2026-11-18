import HRS.MC.E213U16m
import HRS.MC.E213U7

/-!
# Packet e213u16, file n: bounds for the drift increments and the one-step conditioning identity
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace HRS.MC.E213U16

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Q HRS.MC.E213U13 HRS.MC.E213Plan
open HRS.MC.E213U10

variable {d : ℕ}

section DBound

variable {S : PreparedData d} {β₀ m : ℝ}

/-- The norm of a window drift increment is bounded by `K ∫_{(u,u']} ‖b‖`. -/
theorem u16_winDrift_norm_bound (hE : EdgeworthHyp S β₀ m) (T : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (a : ℝ) (ha : 0 ≤ a) (bq : ℝ → NegSobolev d (rLvl d))
      (_ : IntegrableOn (fun v => ‖bq v‖) (Set.Icc 0 (a + T))) (u u' : ℝ), 0 ≤ u → u ≤ u' → u' ≤ a + T →
      ‖winDrift (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (bq v)) u u'‖ ≤
        K * ∫ v in Set.Ioc u u', ‖bq v‖ := by
  obtain ⟨C, c, hC, hc, hV⟩ := HRS.MC.E213D.vprop_stable_of_prepared S β₀ hE m
  refine ⟨C, hC, fun a ha bq hbi u u' hu huu hu' => ?_⟩
  have hsub : Set.Ioc u u' ⊆ Set.Icc 0 (a + T) := fun v hv => ⟨hu.trans hv.1.le, hv.2.trans hu'⟩
  have hgi : IntegrableOn (fun v => C * ‖bq v‖) (Set.Ioc u u') := (hbi.mono_set hsub).const_mul C
  have key := HRS.MC.E213U1.u1_winDrift_norm_le hE T a ha (fun v => NegSobolev.embed m (bq v)) u u'
    (fun v => C * ‖bq v‖) (fun v => mul_nonneg hC.le (norm_nonneg _)) hgi (by
      intro s hs v hv
      have hv0 : 0 ≤ v := hu.trans hv.1.le
      have hvt : v ≤ a + s := hv.2.trans (min_le_right _ _)
      refine (hV v (a + s) hv0 hvt _).trans ?_
      have h1 : Real.exp (-c * (a + s - v)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
      calc C * Real.exp (-c * (a + s - v)) * ‖NegSobolev.embed m (bq v)‖
          ≤ C * 1 * ‖bq v‖ := by
            gcongr
            exact NegSobolev.norm_embed_le m (rLvl_le hE) (bq v)
        _ = C * ‖bq v‖ := by ring)
  refine key.trans (le_of_eq ?_)
  rw [integral_const_mul]

end DBound

section DBoundAE

variable {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} (gd : GaussData S β₀ hE)

/-- A uniform a.s. bound on all drift increments by the block sums. -/
theorem u16_Dinc_bound (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) :
    ∃ K : ℝ, 0 < K ∧ ∀ᵐ ω ∂gd.P₀, ∀ u u' : ℝ, 0 ≤ u → u ≤ u' → u' ≤ a + T →
      ‖winDrift (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (gd.B v ω)) u u'‖ ≤
        K * Gblk gd (a + T) ω := by
  obtain ⟨K, hK, hbd⟩ := u16_winDrift_norm_bound (S := S) (β₀ := β₀) hE T
  have hH : 0 < a + T := by linarith
  refine ⟨K, hK, ?_⟩
  filter_upwards [HRS.MC.E213U11.u11_B_integrable gd (a + T) hH, u16_B_int_bound gd (a + T) hH] with ω hint hG u u' hu huu hu'
  refine (hbd a ha (fun v => gd.B v ω) hint u u' hu huu hu').trans ?_
  refine mul_le_mul_of_nonneg_left ?_ hK.le
  refine le_trans ?_ hG
  refine setIntegral_mono_set (hint.mono_set Set.Ioc_subset_Icc_self) (Eventually.of_forall fun v => norm_nonneg _)
    (Eventually.of_forall ?_)
  intro v hv
  exact ⟨hu.trans_lt hv.1, hv.2.trans hu'⟩

end DBoundAE


section DPast

variable {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} (gd : GaussData S β₀ hE)

theorem u16_winDrift_past (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) {u τ : ℝ} (hu : 0 ≤ u) (huτ : u ≤ τ)
    (hτ : τ ≤ a + T) :
    ∃ D' : gd.Ω₀ → PathSpace d m T, Measurable[pastSig gd τ] D' ∧
      (fun ω => winDrift (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (gd.B v ω)) u τ) =ᵐ[gd.P₀] D' := by
  obtain ⟨D', hD', hae⟩ := u16_driftInc_past gd T hT a ha hu huτ hτ
  refine ⟨fun ω => winRestr a ha (D' ω), @Measurable.comp _ _ _ (pastSig gd τ) _ _ _ _
    (winRestr a ha).continuous.measurable hD', ?_⟩
  filter_upwards [hae] with ω hω
  simp only [winDrift]
  rw [hω]

end DPast

end HRS.MC.E213U16

end
