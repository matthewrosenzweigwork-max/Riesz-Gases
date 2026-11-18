import HRS.MS.Fp81S21RespRecon10
import HRS.MS.S111X2Aux28

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.S111X2

/-- The weighted shifted oscillator orbit is jointly measurable on the
window and initial-reference product measure. -/
theorem fp81s21_respRecon_orbit_joint_measurable (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∀ a : ℝ, 0 ≤ a → ∀ α : MultiIndex p.d,
          ∀ w : ℝ → ℝ, Continuous w →
            AEStronglyMeasurable (Function.uncurry (fun t x => w t *
              r26t3_U R 0 (a + t) (oscTestFun (wholeSpaceIndex p.d : ℝ) α) x))
              ((volume.restrict (Icc (0 : ℝ) p.T)).prod (r26t3_mu R 0)) := by
  obtain ⟨δ0, hδ0, hhalf, horbit⟩ := fp81s21_respRecon_orbit_bounds p
  refine ⟨δ0, hδ0, hhalf, fun δ hδ hδle R a ha α w hw => ?_⟩
  obtain ⟨-, -, -, href⟩ := r26t3_reference_data p δ hδ (hδle.trans hhalf) R
  obtain ⟨M, c, S, hc, hTc⟩ := href 0
  haveI : IsProbabilityMeasure (r26t3_mu R 0) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hTc.prob
  obtain ⟨B, hB, hreg, hcont⟩ := horbit δ hδ hδle R a ha α
  let q : ℝ → ℝ := s111x2_clamp p.T
  have hq : Continuous q := s111x2_clamp_cont p.T
  have hqI : ∀ t, q t ∈ Icc (0 : ℝ) p.T := s111x2_clamp_mem p.hT.le
  let f : ℝ → Euc p.d → ℝ := fun t x => w t *
    r26t3_U R 0 (a + q t) (oscTestFun (wholeSpaceIndex p.d : ℝ) α) x
  have hfc : ∀ x, Continuous (fun t => f t x) := by
    intro x
    have hc := continuousOn_iff_continuous_restrict.mp (hcont x)
    have hqc : Continuous (fun t : ℝ => (⟨q t, hqI t⟩ : Icc (0 : ℝ) p.T)) :=
      hq.subtype_mk _
    exact hw.mul (hc.comp hqc)
  have hfm : ∀ t, Measurable (f t) := by
    intro t
    exact (continuous_const.mul (hreg (q t) (hqI t)).1.1.continuous).measurable
  have hfm' : Measurable (Function.uncurry f) :=
    measurable_uncurry_of_continuous_of_measurable hfc hfm
  apply hfm'.aestronglyMeasurable.congr
  have hset : ∀ᵐ z ∂((volume.restrict (Icc (0 : ℝ) p.T)).prod (r26t3_mu R 0)),
      z.1 ∈ Icc (0 : ℝ) p.T := by
    apply (Measure.ae_prod_iff_ae_ae (measurable_fst measurableSet_Icc)).2
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact Filter.Eventually.of_forall fun _ => ht
  filter_upwards [hset] with z hz
  change w z.1 * r26t3_U R 0 (a + q z.1) _ z.2 =
    w z.1 * r26t3_U R 0 (a + z.1) _ z.2
  dsimp [q]
  rw [s111x2_clamp_id hz]

#print axioms fp81s21_respRecon_orbit_joint_measurable

end HRS.Fp81.S21
end
