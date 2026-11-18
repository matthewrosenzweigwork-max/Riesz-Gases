import HRS.MS.R26T8AP14b
import HRS.MS.R26T8AP05a

/-!
# S8.2 T8A Z0: elementary facts on the Newton kernel for the derivative induction
* `r26t8a_Z0_K_contOn`: the Newton kernel is continuous off the origin;
* `r26t8a_Z0_K_bdd`: it is bounded on compact annuli;
* `r26t8a_Z0_tail`: tails of ball integrals of an integrable function tend to zero.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

theorem r26t8a_Z0_K_contOn (nu : ℝ) : ContinuousOn (newtonKernel d nu) {0}ᶜ := by
  intro z hz
  have hz0 : z ≠ 0 := hz
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.2 hz0
  have hnc : ContinuousAt (fun z : Euc d => ‖z‖) z := continuous_norm.continuousAt
  unfold newtonKernel
  by_cases h : d = 2
  · simp only [h, ↓reduceIte]
    exact ((hnc.log hn).neg.div_const _).continuousWithinAt
  · simp only [h, ite_false]
    exact (((Real.continuousAt_rpow_const _ _ (Or.inl hn)).comp hnc).div_const _).continuousWithinAt

theorem r26t8a_Z0_K_bdd (nu : ℝ) {ρ R : ℝ} (hρ : 0 < ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : Euc d, ρ ≤ ‖t‖ → ‖t‖ ≤ R → |newtonKernel d nu t| ≤ C := by
  set S : Set (Euc d) := {t | ρ ≤ ‖t‖ ∧ ‖t‖ ≤ R} with hS
  have hcl : IsClosed S := (isClosed_le continuous_const continuous_norm).inter
    (isClosed_le continuous_norm continuous_const)
  have hsub : S ⊆ closedBall (0 : Euc d) R := fun t ht => by
    rw [mem_closedBall_zero_iff]; exact ht.2
  have hc : IsCompact S := (isCompact_closedBall (0 : Euc d) R).of_isClosed_subset hcl hsub
  have hcont : ContinuousOn (newtonKernel d nu) S := (r26t8a_Z0_K_contOn nu).mono fun t ht => by
    have : 0 < ‖t‖ := lt_of_lt_of_le hρ ht.1
    simpa using (norm_pos_iff.1 this)
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuousOn hcont
  refine ⟨max C 0, le_max_right _ _, fun t h1 h2 => ?_⟩
  have := hC t ⟨h1, h2⟩
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

theorem r26t8a_Z0_tail (hd : 1 ≤ d) {h : Euc d → ℝ} (hh : Integrable h) :
    Tendsto (fun N : ℕ => ∫ w in ball (0 : Euc d) (3 * (1 / 2 : ℝ) ^ N), ‖h w‖) atTop (𝓝 0) := by
  haveI : Nontrivial (Euc d) := by
    apply Module.nontrivial_of_finrank_pos (R := ℝ)
    simp; omega
  have hanti : Antitone (fun N : ℕ => ball (0 : Euc d) (3 * (1 / 2 : ℝ) ^ N)) := by
    intro m n hmn
    refine ball_subset_ball ?_
    have : (1 / 2 : ℝ) ^ n ≤ (1 / 2) ^ m := pow_le_pow_of_le_one (by norm_num) (by norm_num) hmn
    linarith
  have := tendsto_setIntegral_of_antitone (μ := volume) (f := fun w => ‖h w‖)
    (s := fun N : ℕ => ball (0 : Euc d) (3 * (1 / 2 : ℝ) ^ N)) (fun N => measurableSet_ball) hanti
    ⟨0, hh.norm.integrableOn⟩
  have hI : (⋂ N : ℕ, ball (0 : Euc d) (3 * (1 / 2 : ℝ) ^ N)) ⊆ {0} := by
    intro w hw
    rw [Set.mem_iInter] at hw
    by_contra hne
    have hpos : 0 < ‖w‖ := norm_pos_iff.2 hne
    have hev : ∀ᶠ N : ℕ in atTop, 3 * (1 / 2 : ℝ) ^ N < ‖w‖ := by
      have h1 : Tendsto (fun N : ℕ => 3 * (1 / 2 : ℝ) ^ N) atTop (𝓝 (3 * 0)) :=
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).const_mul 3
      rw [mul_zero] at h1
      exact h1.eventually (gt_mem_nhds hpos)
    obtain ⟨N, hN⟩ := hev.exists
    have := hw N
    rw [mem_ball_zero_iff] at this
    linarith
  have h0 : ∫ x in ⋂ N : ℕ, ball (0 : Euc d) (3 * (1 / 2 : ℝ) ^ N), ‖h x‖ = 0 := by
    refine setIntegral_measure_zero _ ?_
    exact measure_mono_null hI (measure_singleton 0)
  rwa [h0] at this

end HRS.MS.R26T8A
