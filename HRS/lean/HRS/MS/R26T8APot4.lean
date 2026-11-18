import HRS.MS.R26T8APot3

/-!
# S8.2 nonlocal layer: separated regime of a convolution (derivatives fall on a smooth kernel)
`r26t8a_far_conv`: for `V(Y,z) = int K(z-v) S(Y,v) dv` with `K` smooth away from `0`, `S` of class `C^p` in `Y`
and supported in `|v| <= R0`, with `z` separated from the support, the mixed jet `nest p q V X z` is bounded
by `BK' * B * vol(closedBall 0 R0)`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ContDiff

namespace HRS.MS.R26T8A
open HRS

section Pot4

variable {d : ℕ}

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem r26t8a_far_conv (K : Euc d → ℝ) (p q : ℕ) (hKd : ContDiffOn ℝ (q : WithTop ℕ∞) K {x | x ≠ 0})
    (S : Euc d × Euc d → ℝ) (hS : ContDiff ℝ (p : WithTop ℕ∞) S)
    (R0 : ℝ) (hSv : ∀ Y w, R0 < ‖w‖ → S (Y, w) = 0) (X z : Euc d)
    (ρ0 : ℝ) (hρ0 : 0 < ρ0) (ε : ℝ) (hε : 0 < ε)
    (hsep : ∀ z' ∈ ball z ε, ∀ v : Euc d, ‖v‖ ≤ R0 → ρ0 ≤ ‖z' - v‖)
    (BK : ℝ) (hBK : ∀ j ≤ q, ∀ x : Euc d, ρ0 ≤ ‖x‖ → ‖iteratedFDeriv ℝ j K x‖ ≤ BK)
    (ρ1 BK' : ℝ) (hsep1 : ∀ v : Euc d, ‖v‖ ≤ R0 → ρ1 ≤ ‖z - v‖)
    (hBK' : ∀ x : Euc d, ρ1 ≤ ‖x‖ → ‖iteratedFDeriv ℝ q K x‖ ≤ BK')
    (B : ℝ) (hB : ∀ i ≤ p, ∀ Y, ‖Y - X‖ < 1 → ∀ w, ‖r26t8a_nest i 0 S Y w‖ ≤ B) :
    ‖r26t8a_nest p q (fun Yw : Euc d × Euc d => ∫ v, K (Yw.2 - v) * S (Yw.1, v)) X z‖ ≤
      BK' * B * (volume : Measure (Euc d)).real (closedBall (0 : Euc d) R0) := by
  set μ : Measure (Euc d) := volume.restrict (closedBall (0 : Euc d) R0) with hμ
  have hfin : (volume : Measure (Euc d)) (closedBall (0 : Euc d) R0) < ⊤ :=
    (isCompact_closedBall _ _).measure_lt_top
  haveI : IsFiniteMeasure μ := ⟨by rw [hμ, Measure.restrict_apply_univ]; exact hfin⟩
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (Nat.zero_le _) X (by simp) 0)
  have hzmem : z ∈ ball z ε := mem_ball_self hε
  have hae : ∀ᵐ v ∂μ, ‖v‖ ≤ R0 := by
    filter_upwards [ae_restrict_mem (measurableSet_closedBall (x := (0 : Euc d)) (ε := R0))] with v hv
    simpa using hv
  have hS0 : ∀ Y, ‖Y - X‖ < 1 → ∀ v, ‖S (Y, v)‖ ≤ B := by
    intro Y hY v
    have := hB 0 (Nat.zero_le _) Y hY v
    rwa [← r26t8a_nest_norm_zero, norm_iteratedFDeriv_zero] at this
  have hSc : ∀ Y : Euc d, Continuous fun v => S (Y, v) := fun Y =>
    (hS.continuous).comp (continuous_const.prodMk continuous_id)
  have hKat : ∀ x : Euc d, ρ0 ≤ ‖x‖ → ContDiffAt ℝ (q : WithTop ℕ∞) K x := fun x hx =>
    hKd.contDiffAt (isOpen_ne.mem_nhds (fun h => by rw [h, norm_zero] at hx; linarith))
  have hKcont : ∀ i ≤ q, ContinuousOn (iteratedFDeriv ℝ i K) {x | x ≠ 0} := fun i hi =>
    ContinuousOn.continuousOn_iteratedFDeriv hKd isOpen_ne (by exact_mod_cast hi)
  have hne : ∀ x : Euc d, ρ0 ≤ ‖x‖ → x ≠ 0 := fun x hx h => by
    rw [h, norm_zero] at hx; linarith
  -- stage 1: derivatives in the relative variable
  have hstage1 : ∀ Y : Euc d, ‖Y - X‖ < 1 →
      iteratedFDeriv ℝ q (fun z'' => ∫ v, K (z'' - v) * S (Y, v)) z =
        ∫ v, S (Y, v) • iteratedFDeriv ℝ q K (z - v) ∂μ := by
    intro Y hY
    have hjet : ∀ v : Euc d, ‖v‖ ≤ R0 → ∀ i ≤ q, ∀ x ∈ ball z ε,
        iteratedFDeriv ℝ i (fun z'' : Euc d => S (Y, v) • K (z'' - v)) x =
          S (Y, v) • iteratedFDeriv ℝ i K (x - v) := by
      intro v hv i hi x hx
      have hc : ContDiffAt ℝ (i : WithTop ℕ∞) (fun z'' : Euc d => K (z'' - v)) x :=
        ((hKat (x - v) (hsep x hx v hv)).of_le (by exact_mod_cast hi)).comp x
          (contDiffAt_id.sub contDiffAt_const)
      rw [iteratedFDeriv_const_smul_apply' hc, iteratedFDeriv_comp_sub (f := K) i v x]
    have hrw : (fun z'' => ∫ v, K (z'' - v) * S (Y, v)) =
        fun z'' => ∫ v, S (Y, v) • K (z'' - v) ∂μ := by
      funext z''
      rw [hμ, setIntegral_eq_integral_of_forall_compl_eq_zero]
      · congr 1; funext v; rw [smul_eq_mul, mul_comm]
      · intro v hv
        have : R0 < ‖v‖ := by simpa using hv
        rw [hSv Y v this, zero_smul]
    have hG : ∀ᵐ v ∂μ, ∀ x ∈ ball z ε,
        ContDiffAt ℝ (q : WithTop ℕ∞) (fun z'' : Euc d => S (Y, v) • K (z'' - v)) x := by
      filter_upwards [hae] with v hv x hx
      exact ((hKat (x - v) (hsep x hx v hv)).comp x (contDiffAt_id.sub contDiffAt_const)).const_smul (S (Y, v))
    have hbd : ∀ i ≤ q, ∀ᵐ v ∂μ, ∀ x ∈ ball z ε,
        ‖iteratedFDeriv ℝ i (fun z'' : Euc d => S (Y, v) • K (z'' - v)) x‖ ≤ B * BK := by
      intro i hi
      filter_upwards [hae] with v hv x hx
      rw [hjet v hv i hi x hx, norm_smul]
      exact mul_le_mul (hS0 Y hY v) (hBK i hi _ (hsep x hx v hv)) (norm_nonneg _) hB0
    have hmeas : ∀ i ≤ q, ∀ x ∈ ball z ε, AEStronglyMeasurable
        (fun v => iteratedFDeriv ℝ i (fun z'' : Euc d => S (Y, v) • K (z'' - v)) x) μ := by
      intro i hi x hx
      have hcont : ContinuousOn (fun v : Euc d => S (Y, v) • iteratedFDeriv ℝ i K (x - v))
          (closedBall (0 : Euc d) R0) := by
        refine (hSc Y).continuousOn.smul ?_
        refine (hKcont i hi).comp (continuous_const.sub continuous_id).continuousOn ?_
        intro v hv
        exact hne _ (hsep x hx v (by simpa using hv))
      refine (hcont.aestronglyMeasurable measurableSet_closedBall).congr ?_
      filter_upwards [hae] with v hv
      exact (hjet v hv i hi x hx).symm
    have key := r26t8a_iter_integral (E := Euc d) (μ := μ) (U := ball z ε) isOpen_ball
      (fun v z'' => S (Y, v) • K (z'' - v)) q hG (integrable_const (B * BK)) hbd hmeas q le_rfl z hzmem
    rw [hrw]
    refine key.trans ?_
    refine integral_congr_ae ?_
    filter_upwards [hae] with v hv
    exact hjet v hv q le_rfl z hzmem
  -- stage 2: derivatives in the center variable
  obtain ⟨Tm, hTmdef⟩ : ∃ Tm : Euc d → ContinuousMultilinearMap ℝ (fun _ : Fin q => Euc d) ℝ,
      ∀ v, Tm v = iteratedFDeriv ℝ q K (z - v) := ⟨_, fun _ => rfl⟩
  have hSY : ∀ v : Euc d, ContDiff ℝ (p : WithTop ℕ∞) (fun Y => S (Y, v)) := fun v =>
    hS.comp (contDiff_id.prodMk contDiff_const)
  have hjet2 : ∀ v : Euc d, ∀ i ≤ p, ∀ Y : Euc d,
      iteratedFDeriv ℝ i (fun Y' : Euc d => S (Y', v) • Tm v) Y =
        ((ContinuousLinearMap.id ℝ ℝ).smulRight (Tm v)).compContinuousMultilinearMap
          (iteratedFDeriv ℝ i (fun Y' => S (Y', v)) Y) := by
    intro v i hi Y
    exact iteratedFDeriv_smul_const_apply (((hSY v).of_le (by exact_mod_cast hi)).contDiffAt)
  have hnorm2 : ∀ v : Euc d, ∀ i ≤ p, ∀ Y : Euc d, ‖Y - X‖ < 1 →
      ‖iteratedFDeriv ℝ i (fun Y' : Euc d => S (Y', v) • Tm v) Y‖ ≤ ‖Tm v‖ * B := by
    intro v i hi Y hY
    have e : (fun Y' : Euc d => S (Y', v) • Tm v) =
        (ContinuousLinearMap.toSpanSingleton ℝ (Tm v)) ∘ (fun Y' => S (Y', v)) := by
      funext Y'; simp
    rw [e]
    have h1 := (ContinuousLinearMap.toSpanSingleton ℝ (Tm v)).norm_iteratedFDeriv_comp_left
      (f := fun Y' => S (Y', v)) (x := Y) (N := (p : WithTop ℕ∞))
      ((hSY v).contDiffAt) (by exact_mod_cast hi) (n := i)
    rw [ContinuousLinearMap.norm_toSpanSingleton] at h1
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    have := hB i hi Y hY v
    rwa [r26t8a_nest_zero] at this
  have hTm : ∀ v : Euc d, ‖v‖ ≤ R0 → ‖Tm v‖ ≤ BK := fun v hv => by
    rw [hTmdef]; exact hBK q le_rfl _ (hsep z hzmem v hv)
  have hTm' : ∀ v : Euc d, ‖v‖ ≤ R0 → ‖Tm v‖ ≤ BK' := fun v hv => by
    rw [hTmdef]; exact hBK' _ (hsep1 v hv)
  have hG2 : ∀ᵐ v ∂μ, ∀ Y ∈ ball X 1,
      ContDiffAt ℝ (p : WithTop ℕ∞) (fun Y' : Euc d => S (Y', v) • Tm v) Y :=
    Filter.Eventually.of_forall fun v Y _ => (hSY v).smul_const (Tm v) |>.contDiffAt
  have hbd2 : ∀ i ≤ p, ∀ᵐ v ∂μ, ∀ Y ∈ ball X 1,
      ‖iteratedFDeriv ℝ i (fun Y' : Euc d => S (Y', v) • Tm v) Y‖ ≤ BK * B := by
    intro i hi
    filter_upwards [hae] with v hv Y hY
    exact (hnorm2 v i hi Y (by simpa [dist_eq_norm] using hY)).trans
      (mul_le_mul_of_nonneg_right (hTm v hv) hB0)
  have hmeas2 : ∀ i ≤ p, ∀ Y ∈ ball X 1, AEStronglyMeasurable
      (fun v => iteratedFDeriv ℝ i (fun Y' : Euc d => S (Y', v) • Tm v) Y) μ := by
    intro i hi Y _
    haveI : SecondCountableTopologyEither (Euc d) (ℝ →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin q => Euc d) ℝ) :=
      ⟨Or.inl inferInstance⟩
    haveI : SecondCountableTopologyEither (Euc d) (ContinuousMultilinearMap ℝ (fun _ : Fin i => Euc d) (ContinuousMultilinearMap ℝ (fun _ : Fin q => Euc d) ℝ)) :=
      ⟨Or.inl inferInstance⟩
    have hf : AEStronglyMeasurable Tm μ := by
      have hc : ContinuousOn Tm (closedBall (0 : Euc d) R0) := by
        have hfe : Tm = fun v => iteratedFDeriv ℝ q K (z - v) := funext hTmdef
        rw [hfe]
        refine (hKcont q le_rfl).comp (continuous_const.sub continuous_id).continuousOn ?_
        intro v hv
        exact hne _ (hsep z hzmem v (by simpa using hv))
      exact hc.aestronglyMeasurable measurableSet_closedBall
    have hg : AEStronglyMeasurable (fun v : Euc d => iteratedFDeriv ℝ i (fun Y' => S (Y', v)) Y) μ := by
      have hc : Continuous fun v : Euc d => iteratedFDeriv ℝ i (fun Y' => S (Y', v)) Y :=
        (r26t8a_partialY_continuous i S ((hS.of_le (by exact_mod_cast hi)))).comp
          (continuous_const.prodMk continuous_id : Continuous fun v : Euc d => (Y, v))
      exact hc.aestronglyMeasurable
    have hcomb := ContinuousLinearMap.aestronglyMeasurable_comp₂ (𝕜 := ℝ)
      (G := ContinuousMultilinearMap ℝ (fun _ : Fin i => Euc d)
        (ContinuousMultilinearMap ℝ (fun _ : Fin q => Euc d) ℝ))
      (ContinuousMultilinearMap.smulRightL ℝ (fun _ : Fin i => Euc d)
        (ContinuousMultilinearMap ℝ (fun _ : Fin q => Euc d) ℝ)) hg hf
    refine hcomb.congr (Filter.Eventually.of_forall fun v => ?_)
    show _ = iteratedFDeriv ℝ i (fun Y' : Euc d => S (Y', v) • Tm v) Y
    rw [hjet2 v i hi Y]
    ext m n
    simp [ContinuousMultilinearMap.smulRightL]
  have key2 : iteratedFDeriv ℝ p (fun Y => ∫ v, S (Y, v) • Tm v ∂μ) X =
      ∫ v, iteratedFDeriv ℝ p (fun Y' : Euc d => S (Y', v) • Tm v) X ∂μ :=
    r26t8a_iter_integral (E := Euc d) (F := ContinuousMultilinearMap ℝ (fun _ : Fin q => Euc d) ℝ)
    (μ := μ) (U := ball X 1) isOpen_ball
    (fun v Y' => S (Y', v) • Tm v) p hG2 (integrable_const (BK * B)) hbd2 hmeas2 p le_rfl X
    (mem_ball_self one_pos)
  have hev : (fun Y : Euc d => iteratedFDeriv ℝ q (fun w => ∫ v, K (w - v) * S (Y, v)) z) =ᶠ[𝓝 X]
      fun Y => ∫ v, S (Y, v) • Tm v ∂μ := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self (one_pos : (0 : ℝ) < 1))] with Y hY
    rw [hstage1 Y (by simpa [dist_eq_norm] using hY)]
    simp only [hTmdef]
  have h1 : r26t8a_nest p q (fun Yw : Euc d × Euc d => ∫ v, K (Yw.2 - v) * S (Yw.1, v)) X z =
      ∫ v, iteratedFDeriv ℝ p (fun Y' : Euc d => S (Y', v) • Tm v) X ∂μ := by
    have : r26t8a_nest p q (fun Yw : Euc d × Euc d => ∫ v, K (Yw.2 - v) * S (Yw.1, v)) X z =
        iteratedFDeriv ℝ p (fun Y : Euc d => ∫ v, S (Y, v) • Tm v ∂μ) X := by
      unfold r26t8a_nest
      exact (hev.iteratedFDeriv ℝ p).self_of_nhds
    rw [this]
    exact key2
  rw [h1, hμ]
  refine norm_setIntegral_le_of_norm_le_const hfin (fun v hv => ?_)
  exact (hnorm2 v p le_rfl X (by simp)).trans
    (mul_le_mul_of_nonneg_right (hTm' v (by simpa using hv)) hB0)

end Pot4

end HRS.MS.R26T8A
