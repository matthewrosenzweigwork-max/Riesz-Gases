import HRS.MC.CepH2Aux2

/-!
# CEPH2, helper 3: integration by parts on the cylinder

For a `C¹`, diagonally periodic `F` vanishing for `‖P⊥ x‖ > R`: `∫_cell ∂_v F = 0`.  Proof: the cell integral of a
periodic function is invariant under translation by `s v`; differentiate in `s`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators Pointwise

noncomputable section

namespace HRS.MC.CepH2

open HRS HRS.MC.Cepa

variable {N : ℕ}

theorem h2_fderiv_periodic {F : Ch N → ℝ} (hper : ∀ x, F (x + cep_diag N) = F x) (x : Ch N) :
    fderiv ℝ F (x + cep_diag N) = fderiv ℝ F x := by
  have : (fun y => F (y + cep_diag N)) = F := funext hper
  rw [← fderiv_comp_add_right, this]

/-- A function vanishing on `{R < ‖P⊥ x‖}` has vanishing derivative there. -/
theorem h2_fderiv_eq_zero_of_far [NeZero N] {F : Ch N → ℝ} {R : ℝ} (hR : ∀ x, R < ‖h2_perp x‖ → F x = 0)
    {x : Ch N} (hx : R < ‖h2_perp x‖) : fderiv ℝ F x = 0 := by
  have hopen : IsOpen {y : Ch N | R < ‖h2_perp y‖} :=
    isOpen_lt continuous_const (h2_continuous_perp.norm)
  have hev : F =ᶠ[𝓝 x] fun _ => (0 : ℝ) :=
    Filter.mem_of_superset (hopen.mem_nhds hx) fun y hy => hR y hy
  rw [hev.fderiv_eq]; simp

theorem h2_measurableSet_tube [NeZero N] (R : ℝ) : MeasurableSet {x : Ch N | ‖h2_perp x‖ ≤ R} :=
  measurableSet_le h2_continuous_perp.norm.measurable measurable_const

theorem h2_integrable_tube_indicator [NeZero N] (R c : ℝ) :
    Integrable (Set.indicator {x : Ch N | ‖h2_perp x‖ ≤ R} fun _ => c) (volume.restrict (cep_cell N)) := by
  rw [integrable_indicator_iff (h2_measurableSet_tube R)]
  refine integrableOn_const ?_
  rw [Measure.restrict_apply (h2_measurableSet_tube R)]
  exact ((measure_mono (by intro x hx; exact ⟨hx.2, hx.1⟩ : {x : Ch N | ‖h2_perp x‖ ≤ R} ∩ cep_cell N ⊆
    cep_cell N ∩ {x | ‖h2_perp x‖ ≤ R})).trans_lt (h2_volume_tube_lt_top R)).ne

theorem h2_integrable_cell_of_far [NeZero N] {F : Ch N → ℝ} (hF : Continuous F)
    (hper : ∀ x, F (x + cep_diag N) = F x) {R : ℝ} (hR : ∀ x, R < ‖h2_perp x‖ → F x = 0) :
    Integrable F (volume.restrict (cep_cell N)) := by
  obtain ⟨C, hC⟩ := h2_bdd_tube hF hper R
  refine Integrable.mono' (h2_integrable_tube_indicator R |C|) hF.aestronglyMeasurable (ae_of_all _ fun x => ?_)
  by_cases hx : ‖h2_perp x‖ ≤ R
  · rw [Set.indicator_of_mem (show x ∈ {x : Ch N | ‖h2_perp x‖ ≤ R} from hx)]
    exact (hC x hx).trans (le_abs_self C)
  · rw [hR x (not_le.1 hx)]
    exact le_of_eq_of_le (by simp) (Set.indicator_nonneg (fun _ _ => abs_nonneg C) x)

theorem h2_norm_perp_smul_le [NeZero N] {s : ℝ} (hs : |s| ≤ 1) (v : Ch N) : ‖h2_perp (s • v)‖ ≤ ‖v‖ := by
  refine (h2_norm_perp_le _).trans ?_
  rw [norm_smul, Real.norm_eq_abs]
  calc |s| * ‖v‖ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right hs (norm_nonneg _)
    _ = ‖v‖ := one_mul _

/-- **Integration by parts on the cylinder**: `∫_cell ∂_v F = 0` for `C¹`, periodic `F` with transversally
bounded support. -/
theorem h2_ibp_per [NeZero N] {F : Ch N → ℝ} (hF : ContDiff ℝ 1 F) (hper : ∀ x, F (x + cep_diag N) = F x)
    {R : ℝ} (hR : ∀ x, R < ‖h2_perp x‖ → F x = 0) (v : Ch N) :
    ∫ x in cep_cell N, fderiv ℝ F x v = 0 := by
  have hFc : Continuous F := hF.continuous
  have hFd : Continuous (fderiv ℝ F) := hF.continuous_fderiv (by simp)
  have hFdv : ∀ s : ℝ, Continuous fun x => fderiv ℝ F (x + s • v) v := fun s =>
    (hFd.comp (continuous_id.add continuous_const)).clm_apply continuous_const
  obtain ⟨C, hC⟩ := h2_bdd_tube hFd (fun x => h2_fderiv_periodic hper x) (R + 2 * ‖v‖)
  have hconst : ∀ s : ℝ, ∫ x in cep_cell N, F (x + s • v) = ∫ x in cep_cell N, F x :=
    fun s => h2_setIntegral_translate hper (s • v)
  set μ := volume.restrict (cep_cell N) with hμ
  have hbound : ∀ᵐ x ∂μ, ∀ s ∈ Metric.ball (0 : ℝ) 1,
      ‖fderiv ℝ F (x + s • v) v‖ ≤ Set.indicator {x : Ch N | ‖h2_perp x‖ ≤ R + ‖v‖} (fun _ => C * ‖v‖) x := by
    refine ae_of_all _ fun x s hs => ?_
    have hs1 : |s| ≤ 1 := by
      have := Metric.mem_ball.1 hs
      rw [Real.dist_eq, sub_zero] at this; exact this.le
    have hpv := h2_norm_perp_smul_le hs1 v
    by_cases hx : ‖h2_perp x‖ ≤ R + ‖v‖
    · rw [Set.indicator_of_mem (show x ∈ {x : Ch N | ‖h2_perp x‖ ≤ R + ‖v‖} from hx)]
      have hxs : ‖h2_perp (x + s • v)‖ ≤ R + 2 * ‖v‖ := by
        rw [h2_perp_add]
        calc ‖h2_perp x + h2_perp (s • v)‖ ≤ ‖h2_perp x‖ + ‖h2_perp (s • v)‖ := norm_add_le _ _
          _ ≤ R + 2 * ‖v‖ := by linarith
      calc ‖fderiv ℝ F (x + s • v) v‖ ≤ ‖fderiv ℝ F (x + s • v)‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ C * ‖v‖ := mul_le_mul_of_nonneg_right (hC _ hxs) (norm_nonneg _)
    · rw [Set.indicator_of_notMem (show x ∉ {x : Ch N | ‖h2_perp x‖ ≤ R + ‖v‖} from hx)]
      have hfar : R < ‖h2_perp (x + s • v)‖ := by
        rw [h2_perp_add]
        have : ‖h2_perp x‖ ≤ ‖h2_perp x + h2_perp (s • v)‖ + ‖h2_perp (s • v)‖ := by
          calc ‖h2_perp x‖ = ‖(h2_perp x + h2_perp (s • v)) - h2_perp (s • v)‖ := by rw [add_sub_cancel_right]
            _ ≤ _ := norm_sub_le _ _
        linarith [not_le.1 hx]
      rw [h2_fderiv_eq_zero_of_far hR hfar]; simp
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (𝕜 := ℝ)
    (F := fun (s : ℝ) (x : Ch N) => F (x + s • v)) (x₀ := 0) (s := Metric.ball (0 : ℝ) 1)
    (bound := Set.indicator {x : Ch N | ‖h2_perp x‖ ≤ R + ‖v‖} (fun _ => C * ‖v‖))
    (F' := fun (s : ℝ) (x : Ch N) => fderiv ℝ F (x + s • v) v) (Metric.ball_mem_nhds 0 one_pos)
    (Eventually.of_forall fun s => (hFc.comp (continuous_id.add continuous_const)).aestronglyMeasurable)
    (by simpa using h2_integrable_cell_of_far hFc hper hR)
    (hFdv 0).aestronglyMeasurable hbound (h2_integrable_tube_indicator _ _)
    (ae_of_all _ fun x s _ => by
      have h1 : HasDerivAt (fun s : ℝ => x + s • v) v s := by
        simpa using ((hasDerivAt_id s).smul_const v).const_add x
      exact (hF.differentiable (by simp) (x + s • v)).hasFDerivAt.comp_hasDerivAt s h1)
  have hcst : (fun s : ℝ => ∫ x, F (x + s • v) ∂μ) = fun _ => ∫ x, F x ∂μ := funext hconst
  rw [hcst] at hderiv
  have := hderiv.2.unique (hasDerivAt_const (0 : ℝ) (∫ x, F x ∂μ))
  simpa using this

end HRS.MC.CepH2
