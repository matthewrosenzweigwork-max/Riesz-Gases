import HRS.MS.R26T8AP10a8

/-!
# S8.2 T8A P10a (part 9): Lipschitz radius at `x` and oddness of the regularised force on balls
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

theorem r26t8a_p10a_lip {y : Euc d} {h : Euc d → Euc d} (hC : ContDiffOn ℝ 1 h {y}ᶜ) {x : Euc d}
    (hxy : x ≠ y) : ∃ r1 : ℝ, 0 < r1 ∧ r1 ≤ 1 / 4 ∧ ∃ L : ℝ, 0 ≤ L ∧ ∀ u : Euc d, ‖u - x‖ < r1 →
      ‖h u - h x‖ ≤ L * ‖u - x‖ := by
  have hopen : IsOpen ({y}ᶜ : Set (Euc d)) := isClosed_singleton.isOpen_compl
  have hca : ContDiffAt ℝ 1 h x := hC.contDiffAt (hopen.mem_nhds (by simpa using hxy))
  obtain ⟨K, t, ht, hK⟩ := hca.exists_lipschitzOnWith
  obtain ⟨r, hr, hrt⟩ := Metric.mem_nhds_iff.1 ht
  refine ⟨min r (1 / 4), lt_min hr (by norm_num), min_le_right _ _, K, K.2, fun u hu => ?_⟩
  have hu1 : u ∈ t := hrt (by simpa [mem_ball_iff_norm, dist_eq_norm] using lt_of_lt_of_le hu (min_le_left _ _))
  have hx1 : x ∈ t := hrt (Metric.mem_ball_self hr)
  have := hK.dist_le_mul u hu1 x hx1
  simpa [dist_eq_norm] using this

/-- the odd truncated regularised force integrates to zero over the ball around `x`. -/
theorem r26t8a_p10a_odd (s : ℝ) {ε : ℝ} (hε : 0 < ε) (hs : 0 < s) (x : Euc d) (j : Fin d) :
    Integrable (fun u : Euc d => (closedBall (0 : Euc d) (1 / 4)).indicator
        (fun w => r26t8a_dkeps s ε w j) (x - u)) ∧
      ∫ u : Euc d, (closedBall (0 : Euc d) (1 / 4)).indicator
        (fun w => r26t8a_dkeps s ε w j) (x - u) = 0 := by
  set g : Euc d → ℝ := (closedBall (0 : Euc d) (1 / 4)).indicator (fun w => r26t8a_dkeps s ε w j) with hg
  have hgi : Integrable g := by
    rw [hg, integrable_indicator_iff measurableSet_closedBall]
    exact (r26t8a_dkeps_continuous s ε hε j).continuousOn.integrableOn_compact (isCompact_closedBall _ _)
  refine ⟨hgi.comp_sub_left x, ?_⟩
  rw [integral_sub_left_eq_self g volume x]
  have hodd : ∀ w : Euc d, g (-w) = - g w := by
    intro w
    by_cases hw : w ∈ closedBall (0 : Euc d) (1 / 4)
    · have hw' : -w ∈ closedBall (0 : Euc d) (1 / 4) := by simpa using hw
      rw [hg]; rw [Set.indicator_of_mem hw', Set.indicator_of_mem hw, r26t8a_dkeps_neg]
    · have hw' : -w ∉ closedBall (0 : Euc d) (1 / 4) := by simpa using hw
      rw [hg]; rw [Set.indicator_of_notMem hw', Set.indicator_of_notMem hw, neg_zero]
  have h1 := integral_neg_eq_self g (volume : Measure (Euc d))
  simp only [hodd, integral_neg] at h1
  linarith

end HRS.MS.R26T8A
