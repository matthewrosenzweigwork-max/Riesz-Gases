import HRS.MS.R26T8AZ3m
import HRS.MS.R26T8AP05a

/-!
# S8.2 T8A Y0: the Riesz kernel `‖w‖^{α-d}` has the properties used for the derivative induction
measurability, local integrability, continuity off `0`, boundedness on annuli, and the integrable majorant (copies of the Newton-kernel facts).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

/-- The Riesz kernel `‖w‖^{α-d}`. -/
def r26t8a_Y0_rK (d : ℕ) (α : ℝ) (w : Euc d) : ℝ := ‖w‖ ^ (α - (d : ℝ))

theorem r26t8a_Y0_measurable (α : ℝ) : Measurable (r26t8a_Y0_rK d α) :=
  measurable_norm.pow_const _

theorem r26t8a_Y0_integrableOn (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) (r : ℝ) :
    IntegrableOn (r26t8a_Y0_rK d α) (ball (0 : Euc d) r) := by
  have h := r26t8a_integrableOn_ball_rpow (d := d) hd (α := (d : ℝ) - α) (by linarith) r
  refine h.congr_fun (fun z _ => ?_) measurableSet_ball
  simp only [r26t8a_Y0_rK]
  congr 1; ring

theorem r26t8a_Y0_contOn (α : ℝ) : ContinuousOn (r26t8a_Y0_rK d α) {0}ᶜ := by
  intro z hz
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.2 hz
  exact ((Real.continuousAt_rpow_const _ _ (Or.inl hn)).comp continuous_norm.continuousAt).continuousWithinAt

theorem r26t8a_Y0_K_bdd (α : ℝ) {ρ R : ℝ} (hρ : 0 < ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : Euc d, ρ ≤ ‖t‖ → ‖t‖ ≤ R → |r26t8a_Y0_rK d α t| ≤ C := by
  set S : Set (Euc d) := {t | ρ ≤ ‖t‖ ∧ ‖t‖ ≤ R} with hS
  have hcl : IsClosed S := (isClosed_le continuous_const continuous_norm).inter
    (isClosed_le continuous_norm continuous_const)
  have hsub : S ⊆ closedBall (0 : Euc d) R := fun t ht => by
    rw [mem_closedBall_zero_iff]; exact ht.2
  have hc : IsCompact S := (isCompact_closedBall (0 : Euc d) R).of_isClosed_subset hcl hsub
  have hcont : ContinuousOn (r26t8a_Y0_rK d α) S := (r26t8a_Y0_contOn α).mono fun t ht => by
    have : 0 < ‖t‖ := lt_of_lt_of_le hρ ht.1
    simpa using (norm_pos_iff.1 this)
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuousOn hcont
  refine ⟨max C 0, le_max_right _ _, fun t h1 h2 => ?_⟩
  have := hC t ⟨h1, h2⟩
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

theorem r26t8a_Y0_major (hd : 2 ≤ d) {α : ℝ} (hα : 0 < α) {s : ℝ} (hs0 : 0 < s) (hsd : s < d) {w : Euc d} (hw : w ≠ 0) :
    Integrable (fun z : Euc d => |r26t8a_Y0_rK d α (w - z)| *
      (closedBall (0 : Euc d) 2).indicator (fun z => ‖z‖ ^ (-s)) z) := by
  have hwn : 0 < ‖w‖ := norm_pos_iff.2 hw
  set ρ : ℝ := ‖w‖ / 2 with hρ
  have hρ0 : 0 < ρ := by positivity
  -- bound of K on the annulus
  have hcomp : IsCompact ({u : Euc d | ρ ≤ ‖u‖} ∩ closedBall (0 : Euc d) (3 * ρ)) :=
    (isCompact_closedBall _ _).inter_left (isClosed_le continuous_const continuous_norm)
  obtain ⟨Km, hKm⟩ := hcomp.exists_bound_of_continuousOn ((r26t8a_Y0_contOn (d := d) α).mono
    (fun u hu => norm_pos_iff.1 (lt_of_lt_of_le hρ0 hu.1)))
  have hun : ‖(ρ / ‖w‖) • w‖ = ρ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]; field_simp
  have hKm0 : 0 ≤ Km := le_trans (norm_nonneg _) (hKm ((ρ / ‖w‖) • w) ⟨by simp only [Set.mem_setOf_eq]; rw [hun],
    by simp only [mem_closedBall, dist_zero_right]; rw [hun]; linarith⟩)
  -- two dominating integrable functions
  have hI1 : Integrable ((ball (0 : Euc d) ρ).indicator (fun z : Euc d => Km * ‖z‖ ^ (-s))) :=
    (integrable_indicator_iff measurableSet_ball).2
      ((r26t8a_integrableOn_ball_rpow (by omega) hsd ρ).const_mul Km)
  have hKint : Integrable ((ball (0 : Euc d) (‖w‖ + 3)).indicator (r26t8a_Y0_rK d α)) :=
    (integrable_indicator_iff measurableSet_ball).2 (r26t8a_Y0_integrableOn (by omega) hα _)
  have hI2 : Integrable (fun z : Euc d => ρ ^ (-s) * ((ball (0 : Euc d) (‖w‖ + 3)).indicator
      (fun u => |r26t8a_Y0_rK d α u|) (w - z))) := by
    have : Integrable (fun u : Euc d => (ball (0 : Euc d) (‖w‖ + 3)).indicator
        (fun u => |r26t8a_Y0_rK d α u|) u) := by
      have := hKint.norm
      refine this.congr (Eventually.of_forall fun u => ?_)
      by_cases hu : u ∈ ball (0 : Euc d) (‖w‖ + 3)
      · simp [Set.indicator_of_mem hu]
      · simp [Set.indicator_of_notMem hu]
    exact (this.comp_sub_left w).const_mul _
  refine Integrable.mono' (hI1.add hI2) ?_ (Eventually.of_forall fun z => ?_)
  · have hm1 : Measurable (fun z : Euc d => |r26t8a_Y0_rK d α (w - z)|) :=
      continuous_abs.measurable.comp ((r26t8a_Y0_measurable α).comp (measurable_const.sub measurable_id))
    have hm2 : Measurable ((closedBall (0 : Euc d) 2).indicator (fun z : Euc d => ‖z‖ ^ (-s))) :=
      Measurable.indicator (measurable_norm.pow_const _) measurableSet_closedBall
    exact (hm1.mul hm2).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (Set.indicator_nonneg
      (fun u _ => Real.rpow_nonneg (norm_nonneg u) _) z))]
    by_cases hz : z ∈ closedBall (0 : Euc d) 2
    · rw [Set.indicator_of_mem hz]
      have hz2 : ‖z‖ ≤ 2 := by simpa using hz
      by_cases hzr : ‖z‖ < ρ
      · have hzb : z ∈ ball (0 : Euc d) ρ := by simpa using hzr
        have hKb : |r26t8a_Y0_rK d α (w - z)| ≤ Km := by
          have := hKm (w - z) ⟨?_, ?_⟩
          · simpa using this
          · simp only [Set.mem_setOf_eq]
            have := norm_sub_norm_le w z
            rw [hρ]; linarith
          · simp only [mem_closedBall, dist_zero_right]
            have := norm_sub_le w z
            rw [hρ]; linarith
        simp only [Pi.add_apply, Set.indicator_of_mem hzb]
        have h2 : 0 ≤ (ball (0 : Euc d) (‖w‖ + 3)).indicator (fun u => |r26t8a_Y0_rK d α u|) (w - z) :=
          Set.indicator_nonneg (fun u _ => abs_nonneg _) _
        have h3 : 0 ≤ ρ ^ (-s) * (ball (0 : Euc d) (‖w‖ + 3)).indicator (fun u => |r26t8a_Y0_rK d α u|) (w - z) :=
          mul_nonneg (Real.rpow_nonneg hρ0.le _) h2
        nlinarith [mul_le_mul_of_nonneg_right hKb (Real.rpow_nonneg (norm_nonneg z) (-s))]
      · push Not at hzr
        have hzb : z ∉ ball (0 : Euc d) ρ := by simpa using hzr
        have hwz : w - z ∈ ball (0 : Euc d) (‖w‖ + 3) := by
          simp only [mem_ball, dist_zero_right]
          have := norm_sub_le w z
          linarith
        simp only [Pi.add_apply, Set.indicator_of_notMem hzb, Set.indicator_of_mem hwz, zero_add]
        have hpow : ‖z‖ ^ (-s) ≤ ρ ^ (-s) := Real.rpow_le_rpow_of_nonpos hρ0 hzr (by linarith)
        calc |r26t8a_Y0_rK d α (w - z)| * ‖z‖ ^ (-s) ≤ |r26t8a_Y0_rK d α (w - z)| * ρ ^ (-s) :=
              mul_le_mul_of_nonneg_left hpow (abs_nonneg _)
          _ = _ := mul_comm _ _
    · rw [Set.indicator_of_notMem hz, mul_zero]
      simp only [Pi.add_apply]
      have h1 : 0 ≤ (ball (0 : Euc d) ρ).indicator (fun z : Euc d => Km * ‖z‖ ^ (-s)) z :=
        Set.indicator_nonneg (fun u _ => mul_nonneg hKm0 (Real.rpow_nonneg (norm_nonneg u) _)) z
      have h2 : 0 ≤ ρ ^ (-s) * (ball (0 : Euc d) (‖w‖ + 3)).indicator (fun u => |r26t8a_Y0_rK d α u|) (w - z) :=
        mul_nonneg (Real.rpow_nonneg hρ0.le _) (Set.indicator_nonneg (fun u _ => abs_nonneg _) _)
      linarith

end HRS.MS.R26T8A
