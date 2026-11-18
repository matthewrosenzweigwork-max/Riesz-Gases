import HRS.MC.E213U16l

/-!
# Packet e213u16, file m: the drift increments `𝒟(u,τ)` are `ℱ_τ`-measurable
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace HRS.MC.E213U16

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Q HRS.MC.E213U13 HRS.MC.E213Plan
open HRS.MC.E213U10

variable {d : ℕ}

section DriftPast

variable {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} (gd : GaussData S β₀ hE)

theorem u16_driftInc_at (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) {ω : gd.Ω₀}
    (hint : IntegrableOn (fun v => ‖gd.B v ω‖) (Set.Icc 0 (a + T))) {u u' : ℝ} (hu : 0 ≤ u) (huu : u ≤ u')
    (hu' : u' ≤ a + T) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) (a + T)) :
    pathAt (driftInc (regime S β₀ hE).D (regime S β₀ hE).ρ m (a + T) (fun v => NegSobolev.embed m (gd.B v ω)) u u') t =
      ∫ v in Set.Ioc u (min u' t), Vprop (regime S β₀ hE).D (regime S β₀ hE).ρ m t v
        (NegSobolev.embed m (gd.B v ω)) := by
  have hc := HRS.MC.E213U1.winDrift_cont_proof hE T hT a ha (fun v => gd.B v ω)
    (HRS.MC.E213U11.u11_B_nearCoef_measurable gd ω) hint u u' hu huu hu'
  refine (HRS.MC.E213U4.u4_pathAt_coe _ ⟨t, ht⟩).trans ?_
  unfold driftInc
  exact HRS.MC.E213O.e213o_pathOf_at' _ hc ⟨t, ht⟩


theorem u16_driftInc_past (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) {u τ : ℝ} (hu : 0 ≤ u) (huτ : u ≤ τ)
    (hτ : τ ≤ a + T) :
    ∃ D' : gd.Ω₀ → PathSpace d m (a + T), Measurable[pastSig gd τ] D' ∧
      (fun ω => driftInc (regime S β₀ hE).D (regime S β₀ hE).ρ m (a + T)
        (fun v => NegSobolev.embed m (gd.B v ω)) u τ) =ᵐ[gd.P₀] D' := by
  classical
  obtain ⟨C, c, hC, hc, Vev, hsp⟩ := HRS.MC.E213U1.u1_vev hE
  have hsp' := hsp
  have hH : 0 < a + T := by linarith
  have hτI : τ ∈ Set.Icc (0 : ℝ) (a + T) := ⟨hu.trans huτ, hτ⟩
  set ι := HRS.MD.EQInterp.embedCLM (rLvl_le hE) with hι
  refine u16_path_meas (μ := gd.P₀) (pastSig gd τ) hH fun t ht ψ hψ => ?_
  set f : ℝ → gd.Ω₀ → ℝ := fun v ω =>
    u16_ev m hψ (HRS.MC.E213U1.u1_F Vev (fun v => ι (gd.B v ω)) t v) with hf
  have hΦ := HRS.MC.E213U1.u1_clamp_joint (hE := hE) hC hc hsp ht.1 ht.2
  set ν : Measure ℝ := volume.restrict (Set.Ioc u τ) with hν
  have hsubI : Set.Ioc u τ ⊆ Set.Icc 0 (a + T) := fun v hv => ⟨hu.trans hv.1.le, hv.2.trans hτ⟩
  -- joint measurability
  have hfm : StronglyMeasurable (Function.uncurry f) := by
    have h1 : Measurable fun p : ℝ × gd.Ω₀ => (p.1, ι (gd.B p.1 p.2)) :=
      measurable_fst.prodMk (ι.continuous.measurable.comp gd.B_meas)
    have h2 : Measurable fun p : ℝ × gd.Ω₀ => Vev t (HRS.MC.E213U1.u1_cl t p.1) (ι (gd.B p.1 p.2)) :=
      hΦ.measurable.comp h1
    have h3 : Measurable fun p : ℝ × gd.Ω₀ => HRS.MC.E213U1.u1_F Vev (fun v => ι (gd.B v p.2)) t p.1 :=
      Measurable.ite (measurableSet_preimage measurable_fst measurableSet_Iic) h2 measurable_const
    exact ((u16_ev m hψ).continuous.measurable.comp h3).stronglyMeasurable
  -- the pointwise bound
  have hbnd : ∀ (v : ℝ) (ω : gd.Ω₀), ‖HRS.MC.E213U1.u1_F Vev (fun v => ι (gd.B v ω)) t v‖ ≤ C * ‖gd.B v ω‖ := by
    intro v ω
    obtain ⟨hbd, -, -⟩ := hsp
    by_cases hvt : v ≤ t
    · simp only [HRS.MC.E213U1.u1_F, Set.indicator_of_mem (Set.mem_Iic.2 hvt)]
      have hm := HRS.MC.E213U1.u1_cl_mem (t := t) v ht.1
      calc ‖Vev t (HRS.MC.E213U1.u1_cl t v) (ι (gd.B v ω))‖
          ≤ ‖Vev t (HRS.MC.E213U1.u1_cl t v)‖ * ‖ι (gd.B v ω)‖ := (Vev t _).le_opNorm _
        _ ≤ (C * Real.exp (-c * (t - HRS.MC.E213U1.u1_cl t v))) * ‖gd.B v ω‖ := by
            refine mul_le_mul (hbd _ _ hm.1 hm.2) ?_ (norm_nonneg _) (by positivity)
            exact NegSobolev.norm_embed_le m (rLvl_le hE) (gd.B v ω)
        _ ≤ C * 1 * ‖gd.B v ω‖ := by
            have : Real.exp (-c * (t - HRS.MC.E213U1.u1_cl t v)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [hm.2])
            gcongr
        _ = C * ‖gd.B v ω‖ := by ring
    · simp only [HRS.MC.E213U1.u1_F, Set.indicator_of_notMem (show v ∉ Set.Iic t from hvt), norm_zero]
      positivity
  have hfi : Integrable (Function.uncurry f) (ν.prod gd.P₀) := by
    have hj : Integrable (fun p : ℝ × gd.Ω₀ => ‖gd.B p.1 p.2‖) (ν.prod gd.P₀) :=
      (u16_B_joint gd (a + T) hH).mono_measure
        (Measure.prod_mono (Measure.restrict_mono hsubI le_rfl) le_rfl)
    refine (hj.const_mul (‖u16_ev m hψ‖ * C)).mono' hfm.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
    calc ‖Function.uncurry f p‖ = ‖u16_ev m hψ (HRS.MC.E213U1.u1_F Vev (fun v => ι (gd.B v p.2)) t p.1)‖ := rfl
      _ ≤ ‖u16_ev m hψ‖ * ‖HRS.MC.E213U1.u1_F Vev (fun v => ι (gd.B v p.2)) t p.1‖ := (u16_ev m hψ).le_opNorm _
      _ ≤ ‖u16_ev m hψ‖ * (C * ‖gd.B p.1 p.2‖) := by gcongr; exact hbnd p.1 p.2
      _ = ‖u16_ev m hψ‖ * C * ‖gd.B p.1 p.2‖ := by ring
  -- slices
  have hslice : ∀ᵐ v ∂ν, AEStronglyMeasurable[pastSig gd τ] (f v) gd.P₀ := by
    have hsub2 : Set.Ioc u τ ⊆ Set.Icc 0 τ := fun v hv => ⟨hu.trans hv.1.le, hv.2⟩
    have hB := ae_restrict_of_ae_restrict_of_subset hsub2 (u16_B_past gd hH hτI)
    filter_upwards [hB] with v ⟨B', hB', hae⟩
    set Fv : NegSobolev d (rLvl d) → ℝ := fun x =>
      if v ≤ t then u16_ev m hψ (Vev t (HRS.MC.E213U1.u1_cl t v) (ι x)) else 0 with hFv
    have hFc : Continuous Fv := by
      by_cases hvt : v ≤ t
      · simp only [hFv, if_pos hvt]
        exact (u16_ev m hψ).continuous.comp ((Vev t _).continuous.comp ι.continuous)
      · simp only [hFv, if_neg hvt]
        exact continuous_const
    refine ⟨fun ω => Fv (B' ω), ?_, ?_⟩
    · letI : MeasurableSpace gd.Ω₀ := pastSig gd τ
      exact (hFc.measurable.comp hB').stronglyMeasurable
    · filter_upwards [hae] with ω hω
      simp only [hf, hFv, HRS.MC.E213U1.u1_F, Set.indicator, Set.mem_Iic, ← hω]
      split_ifs <;> simp
  obtain ⟨g, hg, hae⟩ := u16_aesm_integral_slice (μ := gd.P₀) (pastSig_le gd hτI) hfm hfi hslice
  refine ⟨g, hg.measurable, ?_⟩
  filter_upwards [hae, HRS.MC.E213U11.u11_B_integrable gd (a + T) hH] with ω hω hint
  rw [u16_driftInc_at gd T hT a ha hint hu huτ hτ ht]
  obtain ⟨p, q, -⟩ := HRS.MC.E213U1.u1_Fint hE hC hc hsp' T a hT ha (fun v => gd.B v ω)
    (HRS.MC.E213U11.u11_B_nearCoef_measurable gd ω) hint u τ hu hτ t ht
  rw [p, ← u16_ev_apply m hψ, ← ContinuousLinearMap.integral_comp_comm _ q]
  exact hω

end DriftPast

end HRS.MC.E213U16

end
