import HRS.MS.SA16Y4Tc3
import HRS.MS.SA16Y4Wk2

/-!
# S.A.16 (SA16Y4) Tl1: uniform convergence with a common support ball gives `L^q` convergence
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R

section Tl1
variable {d : ℕ}

theorem sa16y4_Lq_of_unif {q : ℝ≥0∞} (hq : q ≠ ⊤) (hq0 : q ≠ 0) (R0 : ℝ) (Nn : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (N : EuclideanSpace ℝ (Fin d) → ℝ) (hc : ∀ j, Continuous (Nn j)) (hc' : Continuous N)
    (h0 : ∀ j x, R0 < ‖x‖ → Nn j x = 0) (h0' : ∀ x, R0 < ‖x‖ → N x = 0)
    (huni : ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ∀ x, |Nn j x - N x| ≤ ε) :
    Tendsto (fun j => (eLpNorm (fun x => Nn j x - N x) q volume).toReal) atTop (𝓝 0) := by
  set V : ℝ := (volume (closedBall (0 : EuclideanSpace ℝ (Fin d)) R0)).toReal ^ (q.toReal)⁻¹ with hV
  have hV0 : 0 ≤ V := Real.rpow_nonneg ENNReal.toReal_nonneg _
  have hBfin : volume (closedBall (0 : EuclideanSpace ℝ (Fin d)) R0) ≠ ⊤ := measure_closedBall_lt_top.ne
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε' : 0 < ε / (V + 1) / 2 := by positivity
  filter_upwards [huni _ hε'] with j hj
  have hsupp : (fun x => Nn j x - N x).support ⊆ closedBall (0 : EuclideanSpace ℝ (Fin d)) R0 := by
    intro x hx
    by_contra hxc
    rw [mem_closedBall_zero_iff, not_le] at hxc
    exact hx (by simp [h0 j x hxc, h0' x hxc])
  have hmeas : AEStronglyMeasurable (fun x => Nn j x - N x) volume := ((hc j).sub hc').aestronglyMeasurable
  rw [← eLpNorm_restrict_eq_of_support_subset (p := q) hmeas hsupp]
  have hle := eLpNorm_le_of_ae_bound (p := q) (μ := volume.restrict (closedBall (0 : EuclideanSpace ℝ (Fin d)) R0))
    (f := fun x => Nn j x - N x) (C := ε / (V + 1) / 2) hmeas.restrict
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hj x)
  rw [Measure.restrict_apply_univ] at hle
  have hfin : (volume (closedBall (0 : EuclideanSpace ℝ (Fin d)) R0)) ^ (q.toReal)⁻¹ *
      ENNReal.ofReal (ε / (V + 1) / 2) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity) hBfin) ENNReal.ofReal_ne_top
  have h2 := ENNReal.toReal_mono hfin hle
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hε'.le] at h2
  rw [Real.dist_eq, sub_zero, abs_of_nonneg ENNReal.toReal_nonneg]
  refine lt_of_le_of_lt h2 ?_
  rw [← hV]
  calc V * (ε / (V + 1) / 2) < ε := by
        have h1 : V * (ε / (V + 1) / 2) = (V / (V + 1)) * ε / 2 := by field_simp
        have h2 : V / (V + 1) < 1 := by rw [div_lt_one (by positivity)]; linarith
        rw [h1]
        nlinarith

end Tl1

end HRS.Whole.AppendixA.Phase2SA16R
