import HRS.MS.R2InterpAux87

/-!
# S10.2 (worker S10R), part 88 (packet M3a): continuity of paths in `B_m` with bounded, coordinatewise continuous Hermite coefficients
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole

variable {d : ℕ}

theorem s102_ofSeq_mem {m : ℝ} (hm : (d : ℝ) < m) {C0 : ℝ} (c : MultiIndex d → ℝ) (hb : ∀ α, |c α| ≤ C0) :
    Memℓp (fun α : MultiIndex d => oscEigenvalue d α ^ (-(m / 2)) * c α) 2 :=
  OscDual.memℓp_of_bounded hm c ⟨C0, hb⟩

theorem s102_ofSeq_continuousOn {m : ℝ} (hm : (d : ℝ) < m) {S : Set ℝ} (c : ℝ → MultiIndex d → ℝ) {C0 : ℝ}
    (hb : ∀ u ∈ S, ∀ α, |c u α| ≤ C0) (hc : ∀ α, ContinuousOn (fun u => c u α) S) :
    ContinuousOn (fun u => (OscDual.ofSeq m (c u) : OscDual d m)) S := by
  intro u0 hu0
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  have hnorm : ∀ u ∈ S, ‖(OscDual.ofSeq m (c u) : OscDual d m) - OscDual.ofSeq m (c u0)‖ =
      Real.sqrt (∑' α : MultiIndex d, (oscEigenvalue d α ^ (-(m / 2)) * (c u α - c u0 α)) ^ 2) := by
    intro u hu
    rw [OscDual.norm_eq_coord]
    congr 1
    refine tsum_congr fun α => ?_
    rw [s102_coord_sub, OscDual.coord_ofSeq_of_mem _ (s102_ofSeq_mem hm _ (hb u hu)),
      OscDual.coord_ofSeq_of_mem _ (s102_ofSeq_mem hm _ (hb u0 hu0))]
    ring
  have hlim : Tendsto (fun u => ∑' α : MultiIndex d, (oscEigenvalue d α ^ (-(m / 2)) * (c u α - c u0 α)) ^ 2)
      (𝓝[S] u0) (𝓝 0) := by
    have hsum : Summable fun α : MultiIndex d => (2 * C0) ^ 2 * oscEigenvalue d α ^ (-m) :=
      (OscDual.summable_oscEv_neg_rpow hm).mul_left _
    have := tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝[S] u0)
      (f := fun u α => (oscEigenvalue d α ^ (-(m / 2)) * (c u α - c u0 α)) ^ 2) (g := fun _ => 0)
      (bound := fun α => (2 * C0) ^ 2 * oscEigenvalue d α ^ (-m)) hsum
      (fun α => by
        have h1 : Tendsto (fun u => c u α) (𝓝[S] u0) (𝓝 (c u0 α)) := hc α u0 hu0
        have h2 := ((h1.sub_const (c u0 α)).const_mul (oscEigenvalue d α ^ (-(m / 2)))).pow 2
        simpa using h2)
      (by
        filter_upwards [self_mem_nhdsWithin] with u hu α
        have h := oscEv_pos α
        have hq : (oscEigenvalue d α ^ (-(m / 2))) ^ 2 = oscEigenvalue d α ^ (-m) := by
          rw [← rpow_half_sq (-m) _ h, neg_div]
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), mul_pow, hq]
        have hdiff : (c u α - c u0 α) ^ 2 ≤ (2 * C0) ^ 2 := by
          have h1 := hb u hu α
          have h2 := hb u0 hu0 α
          have : |c u α - c u0 α| ≤ 2 * C0 := by
            calc |c u α - c u0 α| ≤ |c u α| + |c u0 α| := abs_sub _ _
              _ ≤ 2 * C0 := by linarith
          have h0 : 0 ≤ 2 * C0 := (abs_nonneg _).trans this
          nlinarith [sq_abs (c u α - c u0 α), abs_nonneg (c u α - c u0 α)]
        have hpos : 0 ≤ oscEigenvalue d α ^ (-m) := (Real.rpow_pos_of_pos h _).le
        nlinarith)
    simpa using this
  have hsq : Tendsto (fun u => Real.sqrt (∑' α : MultiIndex d,
      (oscEigenvalue d α ^ (-(m / 2)) * (c u α - c u0 α)) ^ 2)) (𝓝[S] u0) (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hlim
    rw [Real.sqrt_zero] at this
    exact this
  refine hsq.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with u hu
  exact (hnorm u hu).symm

end HRS.MS.R2Interp

end
