import HRS.MS.R26T8AP10a12

/-!
# S8.2 T8A P10a (part 13): the core identity (principal-value form)
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

theorem r26t8a_p10a_exists_cutoff (d : ℕ) : ∃ chi : Euc d → ℝ, NewtonCutoff chi := by
  let b : ContDiffBump (0 : Euc d) := ⟨1, 2, one_pos, one_lt_two⟩
  refine ⟨fun z => (b z + b (-z)) / 2, ?_, ?_, ?_, ?_, ?_⟩
  · exact (b.contDiff.add (b.contDiff.comp contDiff_neg)).div_const 2
  · intro z; simp [add_comm]
  · intro z
    have h1 := b.nonneg' z
    have h2 := b.nonneg' (-z)
    have h3 := b.le_one (x := z)
    have h4 := b.le_one (x := -z)
    constructor <;> linarith
  · intro z hz
    have h1 : b z = 1 := b.one_of_mem_closedBall (by simpa using hz)
    have h2 : b (-z) = 1 := b.one_of_mem_closedBall (by simpa using hz)
    simp [h1, h2]
  · intro z hz
    have h1 : b z = 0 := b.zero_of_le_dist (by simpa using hz)
    have h2 : b (-z) = 0 := b.zero_of_le_dist (by simpa using hz)
    simp [h1, h2]

theorem r26t8a_p10a_core {y : Euc d} {τ : ℝ} {h : Euc d → Euc d} (H : R26P10Hyp d y τ h)
    {s : ℝ} (hs : 0 < s) (hsd : s < d) {x : Euc d} (hxy : x ≠ y) :
    Integrable (fun u => ‖x - u‖ ^ (-s) * r26t8a_divh h u) ∧
    ∫ u, ‖x - u‖ ^ (-s) * r26t8a_divh h u = ∫ u, r26t8a_Ecan0 s h x u := by
  have hd := H.hd
  haveI : Nontrivial (Euc d) := by
    apply Module.nontrivial_of_finrank_pos (R := ℝ)
    simp; omega
  obtain ⟨chi, hchi⟩ := r26t8a_p10a_exists_cutoff d
  have hint := r26t8a_p10a_xpole_int H hs hsd hxy
  refine ⟨hint, ?_⟩
  have hae : ∀ᵐ u : Euc d ∂volume, u ≠ x := compl_mem_ae_iff.mpr (measure_singleton x)
  have hL1 : Tendsto (fun ε : ℝ => ∫ u, r26t8a_keps s ε (x - u) * r26t8a_divh h u) (𝓝[>] 0)
      (𝓝 (∫ u, ‖x - u‖ ^ (-s) * r26t8a_divh h u)) := by
    refine tendsto_integral_filter_of_dominated_convergence (l := 𝓝[>] (0 : ℝ))
      (fun u => ‖‖x - u‖ ^ (-s) * r26t8a_divh h u‖) ?_ ?_ hint.norm ?_
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have hGc : Continuous fun u : Euc d => r26t8a_keps s ε (x - u) :=
        (r26t8a_keps_continuous s ε hε).comp (continuous_const.sub continuous_id)
      exact hGc.aestronglyMeasurable.mul
        (r26t8a_p10a_aesm hd y (r26t8a_divh_continuousOn H.C1))
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      filter_upwards [hae] with u hu
      have hw : x - u ≠ 0 := sub_ne_zero.2 (Ne.symm hu)
      rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (r26t8a_keps_nonneg s ε _), Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
      exact mul_le_mul_of_nonneg_right (r26t8a_keps_le hs hε hw) (abs_nonneg _)
    · filter_upwards [hae] with u hu
      have hw : x - u ≠ 0 := sub_ne_zero.2 (Ne.symm hu)
      exact (r26t8a_keps_tendsto s hw).mul_const _
  have hL2 : ∀ ε : ℝ, 0 < ε →
      ∫ u, r26t8a_keps s ε (x - u) * r26t8a_divh h u = ∫ u, r26t8a_Ecan s ε h x u := by
    intro ε hε
    rw [r26t8a_p10a_eps_ibp hchi H hs hε x, (r26t8a_p10a_Ecan_integral H hs hε x).2]
  have hL3 := (r26t8a_p10a_Ecan_tendsto H hs hsd hxy).2
  have hL4 : Tendsto (fun ε : ℝ => ∫ u, r26t8a_keps s ε (x - u) * r26t8a_divh h u) (𝓝[>] 0)
      (𝓝 (∫ u, r26t8a_Ecan0 s h x u)) := by
    refine hL3.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (hL2 ε hε).symm
  exact tendsto_nhds_unique hL1 hL4

end HRS.MS.R26T8A
