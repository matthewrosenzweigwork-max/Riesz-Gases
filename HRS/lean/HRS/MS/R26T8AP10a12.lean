import HRS.MS.R26T8AP10a11

/-!
# S8.2 T8A P10a (part 12): `ε → 0` and the core identity
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

theorem r26t8a_p10a_Ecan_tendsto {y : Euc d} {τ : ℝ} {h : Euc d → Euc d} (H : R26P10Hyp d y τ h)
    {s : ℝ} (hs : 0 < s) (hsd : s < d) {x : Euc d} (hxy : x ≠ y) :
    Integrable (r26t8a_Ecan0 s h x) ∧
    Tendsto (fun ε : ℝ => ∫ u, r26t8a_Ecan s ε h x u) (𝓝[>] 0) (𝓝 (∫ u, r26t8a_Ecan0 s h x u)) := by
  have hd := H.hd
  haveI : Nontrivial (Euc d) := by
    apply Module.nontrivial_of_finrank_pos (R := ℝ)
    simp; omega
  obtain ⟨r1, hr1, hr14, L, hL, hlip⟩ := r26t8a_p10a_lip H.C1 hxy
  have hhn := r26t8a_p10a_hnorm_int H
  set Bd : Euc d → ℝ := fun u =>
    (ball x r1).indicator (fun u => d * s * L * ‖u - x‖ ^ (-s)) u +
      d * s * r1 ^ (-s - 1) * ‖h u‖ +
      (ball x (1 / 2)).indicator (fun _ => d * s * r1 ^ (-s - 1) * ‖h x‖) u with hBd
  have hBdi : Integrable Bd := by
    refine Integrable.add (Integrable.add ?_ ?_) ?_
    · rw [integrable_indicator_iff measurableSet_ball]
      exact (r26t8a_p10a_pole_on hd hs hsd x hr1).const_mul _
    · exact hhn.const_mul _
    · rw [integrable_indicator_iff measurableSet_ball]
      exact integrableOn_const (by exact measure_ball_lt_top.ne)
  have hae : ∀ᵐ u : Euc d ∂volume, u ≠ x := compl_mem_ae_iff.mpr (measure_singleton x)
  have hmeasA : ∀ ε : ℝ, 0 < ε → AEStronglyMeasurable (r26t8a_Ecan s ε h x) volume := by
    intro ε hε
    have hdc : ∀ j : Fin d, Continuous fun u : Euc d => r26t8a_dkeps s ε (x - u) j := fun j =>
      (r26t8a_dkeps_continuous s ε hε j).comp (continuous_const.sub continuous_id)
    have hj : ∀ j : Fin d, Continuous fun v : Euc d => v j := fun j => (EuclideanSpace.proj j).continuous
    refine r26t8a_p10a_aesm_ite (x := x) ?_ ?_
    · refine r26t8a_p10a_aesm hd y ?_
      refine continuousOn_finsetSum _ fun j _ => ?_
      exact (((hj j).comp_continuousOn H.C1.continuousOn).sub continuousOn_const).mul (hdc j).continuousOn
    · refine r26t8a_p10a_aesm hd y ?_
      refine continuousOn_finsetSum _ fun j _ => ?_
      exact ((hj j).comp_continuousOn H.C1.continuousOn).mul (hdc j).continuousOn
  have hbound : ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ᵐ u : Euc d ∂volume, ‖r26t8a_Ecan s ε h x u‖ ≤ Bd u := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    filter_upwards [hae] with u hu
    rw [Real.norm_eq_abs]
    exact r26t8a_p10a_Ecan_bound hs hε hr1 hr14 hL hlip hu
  have hlim : ∀ᵐ u : Euc d ∂volume, Tendsto (fun ε : ℝ => r26t8a_Ecan s ε h x u) (𝓝[>] 0)
      (𝓝 (r26t8a_Ecan0 s h x u)) := by
    filter_upwards [hae] with u hu
    have hw : x - u ≠ 0 := sub_ne_zero.2 (Ne.symm hu)
    unfold r26t8a_Ecan r26t8a_Ecan0
    by_cases hc : ‖x - u‖ ≤ 1 / 4
    · simp only [if_pos hc]
      exact tendsto_finset_sum _ fun j _ => (r26t8a_dkeps_tendsto s hw j).const_mul _
    · simp only [if_neg hc]
      exact tendsto_finset_sum _ fun j _ => (r26t8a_dkeps_tendsto s hw j).const_mul _
  have hT := tendsto_integral_filter_of_dominated_convergence (l := 𝓝[>] (0 : ℝ)) Bd
    (by filter_upwards [self_mem_nhdsWithin] with ε hε; exact hmeasA ε hε) hbound hBdi hlim
  refine ⟨?_, hT⟩
  -- integrability of the limit integrand: dominated by `Bd`
  have hhj : ∀ j : Fin d, AEStronglyMeasurable (fun u => h u j) volume := fun j =>
    r26t8a_p10a_aesm hd y (((EuclideanSpace.proj j).continuous).comp_continuousOn H.C1.continuousOn)
  have hkj : ∀ j : Fin d, Measurable (fun u : Euc d => -s * (x - u) j * ‖x - u‖ ^ (-s - 2)) := fun j => by
    have h1 : Measurable fun u : Euc d => (x - u) j :=
      ((EuclideanSpace.proj j).continuous.measurable).comp (measurable_const.sub measurable_id)
    exact (measurable_const.mul h1).mul ((measurable_const.sub measurable_id).norm.pow_const _)
  have hmeas0 : AEStronglyMeasurable (r26t8a_Ecan0 s h x) volume := by
    refine r26t8a_p10a_aesm_ite (x := x) ?_ ?_
    · exact Finset.aestronglyMeasurable_fun_sum _ fun j _ =>
        ((hhj j).sub aestronglyMeasurable_const).mul (hkj j).aestronglyMeasurable
    · exact Finset.aestronglyMeasurable_fun_sum _ fun j _ => (hhj j).mul (hkj j).aestronglyMeasurable
  refine Integrable.mono' hBdi hmeas0 ?_
  filter_upwards [hae, hlim] with u hu hl
  have hb : ∀ᶠ ε : ℝ in 𝓝[>] 0, ‖r26t8a_Ecan s ε h x u‖ ≤ Bd u := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [Real.norm_eq_abs]
    exact r26t8a_p10a_Ecan_bound hs hε hr1 hr14 hL hlip hu
  exact le_of_tendsto hl.norm hb

end HRS.MS.R26T8A
