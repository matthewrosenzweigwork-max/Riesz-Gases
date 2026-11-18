import HRS.MC.E213U18g
import HRS.MC.L2C0
import HRS.MC.S7PIS1Eval

/-!
# Packet e213u18 (part h): the window drift as a Bochner integral of a measurable family of functionals of `ℬ^v`

For `t ∈ [a,a+T]` and smooth `φ`: a.s. `⟨D_a^{t-a}, φ⟩ = ∫_{(0,a+T]} Λ_v(ℬ^v) dv`, where `Λ_v` is a measurable bounded
family of functionals with `Λ_v(x) = x(U^{v,t}φ)` for `0 ≤ v ≤ t` and `Λ_v = 0` for `v > t`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E213U18

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan HRS.MC.E213U11
  HRS.MC.E213U10 HRS.MC.E213U1 HRS.MC.E213U13

variable {d : ℕ}

section DData

variable {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} (gd : GaussData S β₀ hE)

theorem u18_D_data (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) {t : ℝ} (ht : t ∈ Set.Icc a (a + T))
    {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ Λ : ℝ → NegSobolev d (rLvl d) →L[ℝ] ℝ,
      (∀ v, ‖Λ v‖ ≤ K) ∧ Measurable (fun p : ℝ × NegSobolev d (rLvl d) => Λ p.1 p.2) ∧
      (∀ v, t < v → Λ v = 0) ∧
      (∀ v, 0 ≤ v → v ≤ t → ∀ x, Λ v x = NegSobolev.eval x (propagator S.dyn S.ρ v t φ)) ∧
      ∀ᵐ ω ∂gd.P₀, NegSobolev.eval (pathEval (gd.Dwin T a ω) (t - a)) φ =
        ∫ v in Set.Ioc 0 (a + T), Λ v (gd.B v ω) := by
  classical
  obtain ⟨C, c, hC, hc, Vev, hsp⟩ := HRS.MC.E213U1.u1_vev hE
  have hH : 0 < a + T := by linarith
  have ht0 : 0 ≤ t := ha.trans ht.1
  have htH : t ≤ a + T := ht.2
  set ι := HRS.MD.EQInterp.embedCLM (rLvl_le hE) with hι
  set Lφ := HRS.MC.Sec7.S7PIR.S7PIR_evalCLM m hφ with hLφ
  let Λ : ℝ → NegSobolev d (rLvl d) →L[ℝ] ℝ := fun v =>
    if v ≤ t then Lφ.comp ((Vev t (u1_cl t v)).comp ι) else 0
  have hΛapp : ∀ v x, Λ v x = if v ≤ t then Lφ (Vev t (u1_cl t v) (ι x)) else 0 := by
    intro v x
    by_cases hv : v ≤ t <;> simp [Λ, hv]
  have hιnorm : ‖ι‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    rw [one_mul]
    exact NegSobolev.norm_embed_le m (rLvl_le hE) x
  have hΛnorm : ∀ v, ‖Λ v‖ ≤ ‖Lφ‖ * C := by
    intro v
    by_cases hv : v ≤ t
    · have : Λ v = Lφ.comp ((Vev t (u1_cl t v)).comp ι) := by simp [Λ, hv]
      rw [this]
      have hcl := u1_cl_mem (t := t) v ht0
      have hV : ‖Vev t (u1_cl t v)‖ ≤ C := by
        refine (hsp.1 _ _ hcl.1 hcl.2).trans ?_
        have : Real.exp (-c * (t - u1_cl t v)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [hcl.2])
        calc C * Real.exp (-c * (t - u1_cl t v)) ≤ C * 1 := by gcongr
          _ = C := mul_one C
      calc ‖Lφ.comp ((Vev t (u1_cl t v)).comp ι)‖ ≤ ‖Lφ‖ * ‖(Vev t (u1_cl t v)).comp ι‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ ‖Lφ‖ * (‖Vev t (u1_cl t v)‖ * ‖ι‖) := by
            gcongr; exact ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ ‖Lφ‖ * (C * 1) := by
            gcongr
        _ = ‖Lφ‖ * C := by rw [mul_one]
    · have : Λ v = 0 := by simp [Λ, hv]
      rw [this, norm_zero]
      exact mul_nonneg (norm_nonneg _) hC.le
  have hΛm : Measurable (fun p : ℝ × NegSobolev d (rLvl d) => Λ p.1 p.2) := by
    have hcont : Continuous fun p : ℝ × NegSobolev d (rLvl d) => Lφ (Vev t (u1_cl t p.1) (ι p.2)) :=
      Lφ.continuous.comp ((u1_clamp_joint (H := a + T) hC hc hsp ht0 htH).comp
        (continuous_fst.prodMk (ι.continuous.comp continuous_snd)))
    have : (fun p : ℝ × NegSobolev d (rLvl d) => Λ p.1 p.2) =
        fun p => if p.1 ≤ t then Lφ (Vev t (u1_cl t p.1) (ι p.2)) else 0 := by
      funext p; exact hΛapp _ _
    rw [this]
    exact Measurable.ite (measurableSet_le measurable_fst measurable_const) hcont.measurable measurable_const
  refine ⟨‖Lφ‖ * C, mul_nonneg (norm_nonneg _) hC.le, Λ, hΛnorm, hΛm, ?_, ?_, ?_⟩
  · intro v hv
    have : ¬ v ≤ t := not_le.2 hv
    simp [Λ, this]
  · intro v hv0 hvt x
    rw [hΛapp, if_pos hvt, u1_cl_eq hv0 hvt]
    show NegSobolev.eval (Vev t v (ι x)) φ = _
    rw [← hsp.2.1 v t hv0 hvt (ι x)]
    rw [HRS.MC.Sec7.S7PIS1.s7_PIS_V_eval_proof (regime S β₀ hE) m hE.m_gt (a + T) hH v t hv0 hvt htH (ι x) φ hφ]
    exact HRS.AdjK.adjka_eval_embed (rLvl_le hE) x _
  · filter_upwards [u11_B_integrable gd (a + T) hH] with ω hω
    have hτ : t - a ∈ Set.Icc (0 : ℝ) T := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hmeasB := u11_B_nearCoef_measurable gd ω
    have hcontω := HRS.MC.E213U1.winDrift_cont_proof hE T hT a ha (fun v => gd.B v ω) hmeasB hω 0 (a + T)
      le_rfl hH.le le_rfl
    have hD : gd.Dwin T a ω = winRestr a ha (Sec7.pathOf m (a + T) (fun s => ∫ v in Set.Ioc 0 (min (a + T) s),
        Vprop (regime S β₀ hE).D (regime S β₀ hE).ρ m s v (NegSobolev.embed m (gd.B v ω)))) := by
      unfold GaussData.Dwin winDrift driftInc
      rw [dif_pos ha]
    rw [u18_pathEval_eq, show pathAt (gd.Dwin T a ω) (t - a) = (gd.Dwin T a ω).at' ⟨t - a, hτ⟩ from
      u10_pathAt_eq _ ⟨t - a, hτ⟩]
    rw [hD, winRestr_at', e213o_pathOf_at' _ hcontω]
    have hs : (e213o_shift ha ⟨t - a, hτ⟩ : ℝ) ∈ Set.Icc (0 : ℝ) (a + T) := (e213o_shift ha ⟨t - a, hτ⟩).2
    have e : (e213o_shift ha ⟨t - a, hτ⟩ : ℝ) = t := by
      show a + (t - a) = t
      ring
    have hF := HRS.MC.E213U1.u1_Fint hE hC hc hsp T a hT ha (fun v => gd.B v ω) hmeasB hω 0 (a + T)
      le_rfl le_rfl _ hs
    rw [hF.1]
    show Lφ _ = _
    rw [← ContinuousLinearMap.integral_comp_comm _ hF.2.1]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp only [u1_F, Set.indicator_apply, Set.mem_Iic, e, hΛapp]
    split_ifs
    · rfl
    · exact map_zero _

end DData

end HRS.MC.E213U18

end
