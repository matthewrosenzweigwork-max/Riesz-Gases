import HRS.MS.Fp81S21RespRecon11
import HRS.MS.Fp81S21ResponseWindow3
import HRS.MS.R2InterpAux3

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.S111X2

/-- The response of a weighted shifted orbit has a jointly measurable
representative on the window and initial-reference product measure. -/
theorem fp81s21_respRecon_response_joint_measurable (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ, 0 < p.γ →
        ∀ a : ℝ, 0 ≤ a → ∀ α : MultiIndex p.d,
          ∀ w : ℝ → ℝ, Continuous w →
            AEStronglyMeasurable (Function.uncurry (fun t => r26t3_a R
              (fun x => w t * r26t3_U R 0 (a + t)
                (oscTestFun (wholeSpaceIndex p.d : ℝ) α) x)))
              ((volume.restrict (Icc (0 : ℝ) p.T)).prod (r26t3_mu R 0)) := by
  obtain ⟨δo, ho, hohalf, horbit⟩ := fp81s21_respRecon_orbit_bounds p
  obtain ⟨δg, hg, hghalf, hgen⟩ := fp81s21_responseWindow_genuine p
  refine ⟨min δo δg, lt_min ho hg, (min_le_left _ _).trans hohalf,
    fun δ hδ hδle R hγ a ha α w hw => ?_⟩
  have hδo := hδle.trans (min_le_left δo δg)
  have hδg := hδle.trans (min_le_right δo δg)
  have hδh := hδo.trans hohalf
  obtain ⟨-, -, -, href⟩ := r26t3_reference_data p δ hδ hδh R
  obtain ⟨M, c, S, hc, hTc⟩ := href 0
  haveI : IsProbabilityMeasure (r26t3_mu R 0) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hTc.prob
  obtain ⟨B, hB, hreg, hcont⟩ := horbit δ hδ hδo R a ha α
  obtain ⟨C, hC, hsmooth⟩ := r26t3_response_smooth hδ hδh R hγ
  let q : ℝ → ℝ := s111x2_clamp p.T
  have hq : Continuous q := s111x2_clamp_cont p.T
  have hqI : ∀ t, q t ∈ Icc (0 : ℝ) p.T := s111x2_clamp_mem p.hT.le
  let v : ℝ → Euc p.d → ℝ := fun t => r26t3_U R 0 (a + q t)
    (oscTestFun (wholeSpaceIndex p.d : ℝ) α)
  let f : ℝ → Euc p.d → ℝ := fun t => r26t3_a R (fun x => w t * v t x)
  have hmem (t : ℝ) : MemCb (r26t3_J p.d) (v t) := (hreg (q t) (hqI t)).1
  have hsmul (t : ℝ) (x : Euc p.d) : f t x = w t * r26t3_a R (v t) x := by
    have h := fp81s21_response_smul hδ hδh R hγ (v t) (hmem t) (w t) x
    have he : (w t • v t) = (fun y => w t * v t y) := by
      funext y
      simp [Pi.smul_apply, smul_eq_mul]
    rw [he] at h
    exact h
  have hfc : ∀ x, Continuous (fun t => f t x) := by
    intro x
    obtain ⟨-, -, hcoord⟩ := hgen δ hδ hδg R hγ a ha x
    have hpath : Continuous (fun s : Icc (0 : ℝ) p.T =>
        OscDual.coord (OscPath.at' (responseWindow R a x) s) α) :=
      (HRS.MS.R2Interp.s102_coordCLM (m := (wholeSpaceIndex p.d : ℝ)) α).continuous.comp
        (responseWindow R a x).continuous
    have hqc : Continuous (fun t : ℝ => (⟨q t, hqI t⟩ : Icc (0 : ℝ) p.T)) :=
      hq.subtype_mk _
    have hh := hw.mul (hpath.comp hqc)
    apply hh.congr
    intro t
    change w t * OscDual.coord (OscPath.at' (responseWindow R a x) ⟨q t, hqI t⟩) α = f t x
    rw [hsmul]
    congr 1
    simpa [v, r26t3_U] using hcoord ⟨q t, hqI t⟩ α
  have hfm : ∀ t, Measurable (f t) := by
    intro t
    have hm : MemCb (r26t3_J p.d) (fun x => w t * v t x) := by
      simpa [Pi.smul_apply, smul_eq_mul] using (HRS.MS.Tc5.tc5_cb_smul (w t) (hmem t)).1
    exact (hsmooth _ hm).1.1.continuous.measurable
  have hfm' : Measurable (Function.uncurry f) :=
    measurable_uncurry_of_continuous_of_measurable hfc hfm
  apply hfm'.aestronglyMeasurable.congr
  have hset : ∀ᵐ z ∂((volume.restrict (Icc (0 : ℝ) p.T)).prod (r26t3_mu R 0)),
      z.1 ∈ Icc (0 : ℝ) p.T := by
    apply (Measure.ae_prod_iff_ae_ae (measurable_fst measurableSet_Icc)).2
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact Filter.Eventually.of_forall fun _ => ht
  filter_upwards [hset] with z hz
  change r26t3_a R (fun x => w z.1 * r26t3_U R 0 (a + q z.1)
    (oscTestFun (wholeSpaceIndex p.d : ℝ) α) x) z.2 = _
  dsimp [q]
  rw [s111x2_clamp_id hz]
  rfl

#print axioms fp81s21_respRecon_response_joint_measurable

end HRS.Fp81.S21
end
