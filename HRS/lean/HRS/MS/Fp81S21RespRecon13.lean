import HRS.MS.Fp81S21RespRecon12

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.S111X2

/-- The response commutes almost everywhere with a weighted shifted orbit
integral, provided the pointwise integral is in the initial L² space. -/
theorem fp81s21_respRecon_orbit_interchange_ae (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ, 0 < p.γ →
        ∀ a : ℝ, 0 ≤ a → ∀ α : MultiIndex p.d,
          ∀ w : ℝ → ℝ, Continuous w → ∀ C : ℝ, 0 ≤ C →
            (∀ t ∈ Icc (0 : ℝ) p.T, |w t| ≤ C) →
            MemLp (fun x => ∫ t in Icc (0 : ℝ) p.T, w t *
              r26t3_U R 0 (a + t) (oscTestFun (wholeSpaceIndex p.d : ℝ) α) x)
              2 (r26t3_mu R 0) →
            r26t3_a R (fun x => ∫ t in Icc (0 : ℝ) p.T, w t *
              r26t3_U R 0 (a + t) (oscTestFun (wholeSpaceIndex p.d : ℝ) α) x)
              =ᵐ[r26t3_mu R 0] fun x => ∫ t in Icc (0 : ℝ) p.T,
                r26t3_a R (fun y => w t * r26t3_U R 0 (a + t)
                  (oscTestFun (wholeSpaceIndex p.d : ℝ) α) y) x := by
  obtain ⟨δo, ho, hohalf, horbit⟩ := fp81s21_respRecon_orbit_bounds p
  obtain ⟨δl, hl, hlhalf, hlp⟩ := fp81s21_respRecon_orbit_L2_integrable p
  obtain ⟨δm, hm, hmhalf, hmeas⟩ := fp81s21_respRecon_orbit_joint_measurable p
  obtain ⟨δr, hr, hrhalf, hresp⟩ := fp81s21_respRecon_response_joint_measurable p
  let D := min δo (min δl (min δm δr))
  have hDo : D ≤ δo := min_le_left _ _
  have hDl : D ≤ δl := (min_le_right _ _).trans (min_le_left _ _)
  have hDm : D ≤ δm := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hDr : D ≤ δr := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨D, lt_min ho (lt_min hl (lt_min hm hr)), hDo.trans hohalf,
    fun δ hδ hδle R hγ a ha α w hw C hC hbound hq => ?_⟩
  have hδh := hδle.trans (hDo.trans hohalf)
  obtain ⟨-, -, -, href⟩ := r26t3_reference_data p δ hδ hδh R
  obtain ⟨M, c, S, hc, hTc⟩ := href 0
  haveI : IsProbabilityMeasure (r26t3_mu R 0) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hTc.prob
  obtain ⟨B, hB, hreg, hcont⟩ := horbit δ hδ (hδle.trans hDo) R a ha α
  let g : ℝ → Euc p.d → ℝ := fun t x => w t * r26t3_U R 0 (a + t)
    (oscTestFun (wholeSpaceIndex p.d : ℝ) α) x
  have hmem : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) p.T)),
      MemLp (g t) 2 (r26t3_mu R 0) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact (HRS.MS.Tc5.tc5_memLp_of_cb (ν := r26t3_mu R 0) (hreg t ht).1).const_mul (w t)
  exact fp81s21_respRecon_response_interchange_ae hδ hδh R _ g
    (hmeas δ hδ (hδle.trans hDm) R a ha α w hw)
    (hresp δ hδ (hδle.trans hDr) R hγ a ha α w hw)
    hmem (hlp δ hδ (hδle.trans hDl) R a ha α w hw.continuousOn C hC hbound) hq

#print axioms fp81s21_respRecon_orbit_interchange_ae

end HRS.Fp81.S21
end
