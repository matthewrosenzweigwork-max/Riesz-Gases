import HRS.MS.R26T8AA01m

/-!
# S8.2 T8A A01 (part n): exhaustion of the plane by exterior regions
For `ψ` integrable and any `u, v`: `∫_{ε<‖u-z‖, ε<‖v-z‖} ψ → ∫ ψ` as `ε → 0+`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_a01_limint (hd : 2 ≤ d) (u v : Euc d) {ψ : Euc d → ℝ} (hψ : Integrable ψ) :
    Tendsto (fun ε : ℝ => ∫ z, Set.indicator {z : Euc d | ε < ‖u - z‖ ∧ ε < ‖v - z‖} ψ z) (𝓝[>] 0)
      (𝓝 (∫ z, ψ z)) := by
  haveI : Nontrivial (Euc d) := by
    apply Module.nontrivial_of_finrank_pos (R := ℝ)
    simp; omega
  have hae : ∀ᵐ z : Euc d ∂volume, z ≠ u ∧ z ≠ v := by
    have hx : ∀ᵐ t : Euc d ∂volume, t ≠ u := compl_mem_ae_iff.mpr (measure_singleton u)
    have hy : ∀ᵐ t : Euc d ∂volume, t ≠ v := compl_mem_ae_iff.mpr (measure_singleton v)
    filter_upwards [hx, hy] with t h1 h2 using ⟨h1, h2⟩
  refine tendsto_integral_filter_of_dominated_convergence (fun z => ‖ψ z‖) ?_ ?_ hψ.norm ?_
  · refine Filter.Eventually.of_forall fun ε => ?_
    have hs : MeasurableSet {z : Euc d | ε < ‖u - z‖ ∧ ε < ‖v - z‖} :=
      (measurableSet_lt measurable_const (measurable_const.sub measurable_id).norm).inter
        (measurableSet_lt measurable_const (measurable_const.sub measurable_id).norm)
    exact hψ.aestronglyMeasurable.indicator hs
  · refine Filter.Eventually.of_forall fun ε => Filter.Eventually.of_forall fun z => ?_
    by_cases h : z ∈ {z : Euc d | ε < ‖u - z‖ ∧ ε < ‖v - z‖}
    · rw [Set.indicator_of_mem h]
    · rw [Set.indicator_of_notMem h]; simp
  · filter_upwards [hae] with z ⟨hzu, hzv⟩
    have h1 : 0 < ‖u - z‖ := norm_pos_iff.2 (sub_ne_zero.2 hzu.symm)
    have h2 : 0 < ‖v - z‖ := norm_pos_iff.2 (sub_ne_zero.2 hzv.symm)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (lt_min h1 h2)] with ε hε
    rw [Set.indicator_of_mem (show z ∈ {z : Euc d | ε < ‖u - z‖ ∧ ε < ‖v - z‖} from
      ⟨lt_of_lt_of_le hε.2 (min_le_left _ _), lt_of_lt_of_le hε.2 (min_le_right _ _)⟩)]

end HRS.MS.R26T8A
