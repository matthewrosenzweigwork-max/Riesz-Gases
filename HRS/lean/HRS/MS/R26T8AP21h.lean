import HRS.MS.R26T8AP21g

/-!
# S8.2 local Newton layer, packet T8A.P21 (part h): nested jets commute with a `t`-integral
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

theorem r26t8a_nest_integral {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {p q : ℕ} {Θ : ℝ → Euc d × Euc d → ℝ}
    (hΘ : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) (fun tYw : ℝ × (Euc d × Euc d) => Θ tYw.1 tYw.2)) (X z : Euc d) :
    r26t8a_nest p q (fun Yw => ∫ t in (0 : ℝ)..1, Θ t Yw) X z =
      ∫ t in (0 : ℝ)..1, r26t8a_nest p q (Θ t) X z := by
  have hΘ3 : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞)
      (fun tYw : (ℝ × Euc d) × Euc d => Θ tYw.1.1 (tYw.1.2, tYw.2)) :=
    hΘ.comp ((contDiff_fst.fst).prodMk ((contDiff_fst.snd).prodMk contDiff_snd))
  have hchic : ∀ (c : Euc d), ContDiff ℝ ∞ (fun u : Euc d => chi (u - c)) := fun c =>
    hchi.1.comp (contDiff_id.sub contDiff_const)
  have hchi1 : ∀ (c u : Euc d), ‖u - c‖ ≤ 1 → chi (u - c) = 1 := fun c u h => hchi.2.2.2.1 _ h
  have hchi0 : ∀ (c u : Euc d), 2 ≤ ‖u - c‖ → chi (u - c) = 0 := fun c u h => hchi.2.2.2.2 _ h
  -- stage in w
  have hstageW : ∀ Y : Euc d, iteratedFDeriv ℝ q (fun w => ∫ t in (0 : ℝ)..1, Θ t (Y, w)) z =
      ∫ t in (0 : ℝ)..1, iteratedFDeriv ℝ q (fun w => Θ t (Y, w)) z := by
    intro Y
    set Θt : ℝ → Euc d → ℝ := fun t w => chi (w - z) * Θ t (Y, w) with hΘt
    have hj : ContDiff ℝ (q : WithTop ℕ∞) (fun tw : ℝ × Euc d => Θt tw.1 tw.2) :=
      (((hchic z).of_le (by exact_mod_cast le_top)).comp contDiff_snd).mul
        ((hΘ.of_le (by exact_mod_cast Nat.le_add_left q p)).comp
          (contDiff_fst.prodMk (contDiff_const.prodMk contDiff_snd)))
    have hK : ∀ t w, w ∉ Metric.closedBall z 2 → Θt t w = 0 := fun t w hw => by
      have : 2 ≤ ‖w - z‖ := by
        rw [Metric.mem_closedBall, dist_eq_norm, not_le] at hw; exact hw.le
      simp [hΘt, hchi0 z w this]
    have hev : (fun w => ∫ t in (0 : ℝ)..1, Θ t (Y, w)) =ᶠ[𝓝 z] fun w => ∫ t in (0 : ℝ)..1, Θt t w := by
      filter_upwards [Metric.ball_mem_nhds z one_pos] with w hw
      have : ‖w - z‖ ≤ 1 := by rw [Metric.mem_ball, dist_eq_norm] at hw; exact hw.le
      refine intervalIntegral.integral_congr (fun t _ => ?_)
      simp [hΘt, hchi1 z w this]
    rw [(hev.iteratedFDeriv ℝ q).eq_of_nhds, r26t8a_stageT Θt hj (isCompact_closedBall z 2) hK z]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    have : (Θt t) =ᶠ[𝓝 z] fun w => Θ t (Y, w) := by
      filter_upwards [Metric.ball_mem_nhds z one_pos] with w hw
      have : ‖w - z‖ ≤ 1 := by rw [Metric.mem_ball, dist_eq_norm] at hw; exact hw.le
      simp [hΘt, hchi1 z w this]
    exact (this.iteratedFDeriv ℝ q).eq_of_nhds
  -- stage in Y
  unfold r26t8a_nest
  have hrew : (fun Y => iteratedFDeriv ℝ q (fun w => (fun Yw => ∫ t in (0 : ℝ)..1, Θ t Yw) (Y, w)) z) =
      fun Y => ∫ t in (0 : ℝ)..1, iteratedFDeriv ℝ q (fun w => Θ t (Y, w)) z := funext hstageW
  rw [hrew]
  set Mt : ℝ → Euc d → ContinuousMultilinearMap ℝ (fun _ : Fin q => Euc d) ℝ :=
    fun t Y => iteratedFDeriv ℝ q (fun w => Θ t (Y, w)) z with hMt
  set Θh : ℝ → Euc d → ContinuousMultilinearMap ℝ (fun _ : Fin q => Euc d) ℝ :=
    fun t Y => chi (Y - X) • Mt t Y with hΘh
  have hMj : ContDiff ℝ (p : WithTop ℕ∞) (fun tY : ℝ × Euc d => Mt tY.1 tY.2) := by
    have e : (fun tY : ℝ × Euc d => Mt tY.1 tY.2) = fun tY =>
        (iteratedFDeriv ℝ q (fun tYw : (ℝ × Euc d) × Euc d => Θ tYw.1.1 (tYw.1.2, tYw.2)) (tY, z)).compContinuousLinearMap
          (fun _ => ContinuousLinearMap.inr ℝ (ℝ × Euc d) (Euc d)) := by
      funext tY
      exact r26t8a_slice_jet_inr' (i := q) (hΘ3.of_le (by exact_mod_cast Nat.le_add_left q p)) tY z
    rw [e]
    exact (ContinuousMultilinearMap.compContinuousLinearMapL
      (fun _ : Fin q => ContinuousLinearMap.inr ℝ (ℝ × Euc d) (Euc d))).contDiff.comp
      ((hΘ3.iteratedFDeriv_right (m := (p : WithTop ℕ∞)) (by exact_mod_cast le_refl (p + q))).comp
        (contDiff_id.prodMk contDiff_const))
  have hj : ContDiff ℝ (p : WithTop ℕ∞) (fun tY : ℝ × Euc d => Θh tY.1 tY.2) :=
    (((hchic X).of_le (by exact_mod_cast le_top)).comp contDiff_snd).smul hMj
  have hK : ∀ t Y, Y ∉ Metric.closedBall X 2 → Θh t Y = 0 := fun t Y hY => by
    have : 2 ≤ ‖Y - X‖ := by
      rw [Metric.mem_closedBall, dist_eq_norm, not_le] at hY; exact hY.le
    simp [hΘh, hchi0 X Y this]
  have hev : (fun Y => ∫ t in (0 : ℝ)..1, Mt t Y) =ᶠ[𝓝 X] fun Y => ∫ t in (0 : ℝ)..1, Θh t Y := by
    filter_upwards [Metric.ball_mem_nhds X one_pos] with Y hY
    have : ‖Y - X‖ ≤ 1 := by rw [Metric.mem_ball, dist_eq_norm] at hY; exact hY.le
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    simp [hΘh, hchi1 X Y this]
  rw [(hev.iteratedFDeriv ℝ p).eq_of_nhds, r26t8a_stageT Θh hj (isCompact_closedBall X 2) hK X]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  have : (Θh t) =ᶠ[𝓝 X] Mt t := by
    filter_upwards [Metric.ball_mem_nhds X one_pos] with Y hY
    have : ‖Y - X‖ ≤ 1 := by rw [Metric.mem_ball, dist_eq_norm] at hY; exact hY.le
    simp [hΘh, hchi1 X Y this]
  exact (this.iteratedFDeriv ℝ p).eq_of_nhds

end HRS.MS.R26T8A
