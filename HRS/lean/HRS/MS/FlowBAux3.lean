import HRS.MS.FlowBAux2
import Mathlib.Analysis.Calculus.MeanValue

/-!
# MS-FLOW-B, continuity and differentiability of the Nemytskii-integral operator

For `Ψ : ℝ → E → E[×r]→L E` continuous in `y`, strongly measurable in `s`, bounded on balls
("good"), the map `α ↦ Vop T r (s ↦ Ψ s (α s))` is continuous; if `Ψ s` is differentiable with
derivative `(Ψ' s y).curryLeft` and `Ψ'` is good, it is Fréchet differentiable with derivative
`(Vop T (r+1) (s ↦ Ψ' s (α s))).curryLeft`.  Both by dominated convergence.
-/

open MeasureTheory Filter Topology Set Metric
open scoped BoundedContinuousFunction

namespace HRS.MS.FlowB

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- "Good" kernels of Nemytskii type. -/
structure Good {r : ℕ} (Ψ : ℝ → E → ML E r) : Prop where
  cont : ∀ s, Continuous (Ψ s)
  meas : ∀ y, StronglyMeasurable (fun s => Ψ s y)
  bdd : ∀ R : ℝ, ∃ c, ∀ s y, ‖y‖ ≤ R → ‖Ψ s y‖ ≤ c

theorem Good.hasB {r : ℕ} {Ψ : ℝ → E → ML E r} (h : Good Ψ) (α : ℝ →ᵇ E) :
    HasB (fun s => Ψ s (α s)) where
  sm := sm_comp_path Ψ h.cont h.meas α.continuous
  bdd := by
    obtain ⟨c, hc⟩ := h.bdd ‖α‖
    exact ⟨c, fun s => hc s _ (α.norm_coe_le_norm s)⟩

theorem Good.continuous_Vop {T : ℝ} (hT : 0 ≤ T) {r : ℕ} {Ψ : ℝ → E → ML E r} (h : Good Ψ) :
    Continuous (fun α : ℝ →ᵇ E => Vop T r (fun s => Ψ s (α s))) := by
  refine continuous_iff_continuousAt.2 fun α => ?_
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  obtain ⟨c, hc⟩ := h.bdd (‖α‖ + 1)
  have hdom : Tendsto (fun α' : ℝ →ᵇ E => ∫ s in (0 : ℝ)..T, ‖Ψ s (α' s) - Ψ s (α s)‖)
      (𝓝 α) (𝓝 0) := by
    have := intervalIntegral.tendsto_integral_filter_of_dominated_convergence (a := 0) (b := T)
      (μ := volume) (l := 𝓝 α) (F := fun α' s => ‖Ψ s (α' s) - Ψ s (α s)‖)
      (f := fun _ => (0 : ℝ)) (fun _ => 2 * c) ?_ ?_ ?_ ?_
    · simpa using this
    · exact Eventually.of_forall fun α' =>
        (((h.hasB α').sm.sub (h.hasB α).sm).norm).aestronglyMeasurable
    · have hev : ∀ᶠ α' in 𝓝 α, dist α' α < 1 := Metric.ball_mem_nhds α one_pos
      filter_upwards [hev] with α' hα'
      refine Eventually.of_forall fun s _ => ?_
      have h1 : ‖α' s‖ ≤ ‖α‖ + 1 := by
        have : ‖α'‖ ≤ ‖α‖ + 1 := by
          have := norm_le_norm_add_norm_sub' α' α
          rw [← dist_eq_norm] at this
          linarith
        exact (α'.norm_coe_le_norm s).trans this
      have h2 : ‖α s‖ ≤ ‖α‖ + 1 := (α.norm_coe_le_norm s).trans (by linarith)
      rw [norm_norm]
      calc ‖Ψ s (α' s) - Ψ s (α s)‖ ≤ ‖Ψ s (α' s)‖ + ‖Ψ s (α s)‖ := norm_sub_le _ _
        _ ≤ c + c := add_le_add (hc s _ h1) (hc s _ h2)
        _ = 2 * c := by ring
    · exact intervalIntegrable_const
    · refine Eventually.of_forall fun s _ => ?_
      have h1 : Tendsto (fun α' : ℝ →ᵇ E => α' s) (𝓝 α) (𝓝 (α s)) :=
        (continuous_eval_const s).tendsto α
      have h2 := ((h.cont s).tendsto (α s)).comp h1
      have h3 := (h2.sub_const (Ψ s (α s))).norm
      simpa using h3
  refine squeeze_zero (fun _ => norm_nonneg _) (fun α' => ?_) hdom
  rw [← Vop_sub (h.hasB α') (h.hasB α)]
  exact norm_Vop_le hT ((h.hasB α').sub (h.hasB α))

/-- Mean value bound on a convex set. -/
theorem mv_bound {r : ℕ} {f : E → ML E r} {f' : E → E →L[ℝ] ML E r}
    (hd : ∀ z, HasFDerivAt f (f' z) z) {S : Set E} (hS : Convex ℝ S) {C : ℝ}
    (hb : ∀ z ∈ S, ‖f' z‖ ≤ C) {y h : E} (hy : y ∈ S) (hyh : y + h ∈ S) :
    ‖f (y + h) - f y‖ ≤ C * ‖h‖ := by
  have := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z _ => (hd z).hasFDerivWithinAt) hb hS hy hyh
  simpa using this

theorem norm_curryLeft' {r : ℕ} (f : ML E (r + 1)) : ‖f.curryLeft‖ = ‖f‖ :=
  (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (r + 1) => E) E).norm_map f

theorem Good.hasFDerivAt_Vop {T : ℝ} (hT : 0 ≤ T) {r : ℕ} {Ψ : ℝ → E → ML E r}
    {Ψ' : ℝ → E → ML E (r + 1)} (hΨ : Good Ψ) (hΨ' : Good Ψ')
    (hd : ∀ s y, HasFDerivAt (Ψ s) ((Ψ' s y).curryLeft) y) (α : ℝ →ᵇ E) :
    HasFDerivAt (fun α' : ℝ →ᵇ E => Vop T r (fun s => Ψ s (α' s)))
      ((Vop T (r + 1) (fun s => Ψ' s (α s))).curryLeft) α := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨c', hc'⟩ := hΨ'.bdd (‖α‖ + 1)
  have hc'0 : 0 ≤ c' := (norm_nonneg _).trans (hc' 0 0 (by simp; positivity))
  -- the remainder kernel
  let B : (ℝ →ᵇ E) → ℝ → ML E r := fun γ s =>
    Ψ s (α s + γ s) - Ψ s (α s) - (Ψ' s (α s)).curryLeft (γ s)
  have hBB : ∀ γ, HasB (B γ) := fun γ =>
    ((hΨ.hasB (α + γ)).sub (hΨ.hasB α)).sub ((hΨ'.hasB α).curryLeft γ)
  have hRem : ∀ γ : ℝ →ᵇ E,
      Vop T r (fun s => Ψ s ((α + γ) s)) - Vop T r (fun s => Ψ s (α s)) -
        (Vop T (r + 1) (fun s => Ψ' s (α s))).curryLeft γ = Vop T r (B γ) := by
    intro γ
    rw [Vop_curryLeft (hΨ'.hasB α) γ, ← Vop_sub (hΨ.hasB (α + γ)) (hΨ.hasB α),
      ← Vop_sub ((hΨ.hasB (α + γ)).sub (hΨ.hasB α)) ((hΨ'.hasB α).curryLeft γ)]
    rfl
  -- pointwise bounds
  have hbound : ∀ γ : ℝ →ᵇ E, ‖γ‖ < 1 → ∀ s, ‖B γ s‖ ≤ 2 * c' * ‖γ‖ := by
    intro γ hγ s
    have hγs : ‖γ s‖ ≤ ‖γ‖ := γ.norm_coe_le_norm s
    have hy : α s ∈ closedBall (0 : E) (‖α‖ + 1) := by
      simp only [mem_closedBall, dist_zero_right]; linarith [α.norm_coe_le_norm s]
    have hyh : α s + γ s ∈ closedBall (0 : E) (‖α‖ + 1) := by
      simp only [mem_closedBall, dist_zero_right]
      linarith [norm_add_le (α s) (γ s), α.norm_coe_le_norm s]
    have h1 := mv_bound (f := Ψ s) (f' := fun z => (Ψ' s z).curryLeft) (hd s)
      (convex_closedBall (0 : E) (‖α‖ + 1)) (C := c') (fun z hz => by
        rw [norm_curryLeft']
        exact hc' s z (by simpa using hz)) hy hyh
    have h2 : ‖(Ψ' s (α s)).curryLeft (γ s)‖ ≤ c' * ‖γ s‖ :=
      (norm_curryLeft_apply_le _ _).trans (mul_le_mul_of_nonneg_right
        (hc' s _ (by linarith [α.norm_coe_le_norm s])) (norm_nonneg _))
    calc ‖B γ s‖ ≤ ‖Ψ s (α s + γ s) - Ψ s (α s)‖ + ‖(Ψ' s (α s)).curryLeft (γ s)‖ :=
          norm_sub_le _ _
      _ ≤ c' * ‖γ s‖ + c' * ‖γ s‖ := add_le_add h1 h2
      _ ≤ 2 * c' * ‖γ‖ := by nlinarith
  have hlim : ∀ s, Tendsto (fun γ : ℝ →ᵇ E => ‖B γ s‖ * ‖γ‖⁻¹) (𝓝 0) (𝓝 0) := by
    intro s
    refine Metric.tendsto_nhds.2 fun η hη => ?_
    have hcont : ContinuousAt (Ψ' s) (α s) := (hΨ'.cont s).continuousAt
    obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.1 hcont (η / 2) (by positivity)
    have hev : ∀ᶠ γ : ℝ →ᵇ E in 𝓝 0, ‖γ‖ < δ := by
      have := Metric.ball_mem_nhds (0 : ℝ →ᵇ E) hδ
      filter_upwards [this] with γ hγ using by simpa using hγ
    filter_upwards [hev] with γ hγ
    rw [Real.dist_eq, sub_zero]
    by_cases hγ0 : γ = 0
    · subst hγ0; simp [B, hη]
    · have hγpos : 0 < ‖γ‖ := norm_pos_iff.2 hγ0
      have hγs : ‖γ s‖ ≤ ‖γ‖ := γ.norm_coe_le_norm s
      set g : E → ML E r := fun z => Ψ s z - (Ψ' s (α s)).curryLeft z with hg
      have hgd : ∀ z, HasFDerivAt g ((Ψ' s z).curryLeft - (Ψ' s (α s)).curryLeft) z := fun z =>
        (hd s z).sub (ContinuousLinearMap.hasFDerivAt _)
      have h1 := mv_bound (f := g) (f' := fun z => (Ψ' s z).curryLeft - (Ψ' s (α s)).curryLeft)
        hgd (convex_ball (α s) δ) (C := η / 2) (fun z hz => by
          have e : (Ψ' s z).curryLeft - (Ψ' s (α s)).curryLeft = (Ψ' s z - Ψ' s (α s)).curryLeft := by
            ext v; simp
          rw [e, norm_curryLeft']
          have := hδ' (by simpa using hz)
          rw [dist_eq_norm] at this
          exact this.le)
          (mem_ball_self hδ) (by
            rw [mem_ball, dist_eq_norm]; simp only [add_sub_cancel_left]; linarith) 
      have hBg : B γ s = g (α s + γ s) - g (α s) := by
        simp only [B, hg]; rw [map_add]; abel
      rw [hBg, abs_of_nonneg (by positivity)]
      calc ‖g (α s + γ s) - g (α s)‖ * ‖γ‖⁻¹ ≤ (η / 2 * ‖γ s‖) * ‖γ‖⁻¹ :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ ≤ (η / 2 * ‖γ‖) * ‖γ‖⁻¹ := by gcongr
        _ = η / 2 := by field_simp
        _ < η := by linarith
  have hG : Tendsto (fun γ : ℝ →ᵇ E => ∫ s in (0 : ℝ)..T, ‖B γ s‖ * ‖γ‖⁻¹) (𝓝 0) (𝓝 0) := by
    have := intervalIntegral.tendsto_integral_filter_of_dominated_convergence (a := 0) (b := T)
      (μ := volume) (l := 𝓝 (0 : ℝ →ᵇ E)) (F := fun γ s => ‖B γ s‖ * ‖γ‖⁻¹)
      (f := fun _ => (0 : ℝ)) (fun _ => 2 * c') ?_ ?_ ?_ ?_
    · simpa using this
    · exact Eventually.of_forall fun γ => ((hBB γ).sm.norm.mul_const _).aestronglyMeasurable
    · have hev : ∀ᶠ γ : ℝ →ᵇ E in 𝓝 0, ‖γ‖ < 1 := by
        have := Metric.ball_mem_nhds (0 : ℝ →ᵇ E) one_pos
        filter_upwards [this] with γ hγ using by simpa using hγ
      filter_upwards [hev] with γ hγ
      refine Eventually.of_forall fun s _ => ?_
      rw [norm_mul, norm_norm, norm_inv, norm_norm]
      by_cases hγ0 : γ = 0
      · subst hγ0; simp; positivity
      · have hγpos : 0 < ‖γ‖ := norm_pos_iff.2 hγ0
        calc ‖B γ s‖ * ‖γ‖⁻¹ ≤ (2 * c' * ‖γ‖) * ‖γ‖⁻¹ :=
              mul_le_mul_of_nonneg_right (hbound γ hγ s) (by positivity)
          _ = 2 * c' := by field_simp
    · exact intervalIntegrable_const
    · exact Eventually.of_forall fun s _ => hlim s
  filter_upwards [hG.eventually (Iio_mem_nhds hε)] with γ hγ
  have hk := norm_Vop_le hT (hBB γ)
  have hγ' : ∫ s in (0 : ℝ)..T, ‖B γ s‖ * ‖γ‖⁻¹ < ε := hγ
  show ‖Vop T r (fun s => Ψ s ((α + γ) s)) - Vop T r (fun s => Ψ s (α s)) -
      (Vop T (r + 1) (fun s => Ψ' s (α s))).curryLeft γ‖ ≤ ε * ‖γ‖
  rw [hRem γ]
  refine hk.trans ?_
  by_cases hγ0 : γ = 0
  · subst hγ0; simp [B]
  · have hγpos : 0 < ‖γ‖ := norm_pos_iff.2 hγ0
    rw [intervalIntegral.integral_mul_const] at hγ'
    have := (mul_lt_mul_of_pos_right hγ' hγpos)
    rw [mul_assoc, inv_mul_cancel₀ hγpos.ne', mul_one] at this
    exact this.le

end HRS.MS.FlowB
