import HRS.MS.R26T6CI11Sections

/-! I11: a joint L³ field has genuine samplewise L³ time sections. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T6C
open HRS HRS.Whole

theorem r26t6c_samplewise_memLp_three
    {Time Omega B : Type*}
    [MeasurableSpace Time] [MeasurableSpace Omega]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    (dt : Measure Time) [SFinite dt]
    (P : Measure Omega) [SFinite P]
    (G : Time × Omega → B)
    (hG : MemLp G 3 (dt.prod P)) :
    ∀ᵐ w ∂P, MemLp (fun t => G (t,w)) 3 dt := by
  have hInt := r26t6c_samplewise_integrable_cube dt P G hG
  have hMeas := hG.aestronglyMeasurable.prodMk_right
  filter_upwards [hInt, hMeas] with w hi hm
  apply (memLp_iff).2
  apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (by norm_num : (3 : ℝ≥0∞) ≠ 0)
    (by norm_num : (3 : ℝ≥0∞) ≠ ⊤) hm).2
  have heq : (∫⁻ t, ‖G (t,w)‖ₑ ^ (3 : ℝ) ∂dt) =
      ENNReal.ofReal (∫ t, ‖G (t,w)‖ ^ 3 ∂dt) := by
    calc
      _ = ∫⁻ t, ENNReal.ofReal (‖G (t,w)‖ ^ 3) ∂dt := by
        refine lintegral_congr (fun t => ?_)
        rw [← ofReal_norm_eq_enorm]
        calc
          (ENNReal.ofReal ‖G (t,w)‖) ^ (3 : ℝ) =
              (ENNReal.ofReal ‖G (t,w)‖) ^ (3 : ℕ) :=
                ENNReal.rpow_natCast _ 3
          _ = _ := (ENNReal.ofReal_pow (norm_nonneg (G (t,w))) 3).symm
      _ = _ := (ofReal_integral_eq_lintegral_ofReal hi
        (ae_of_all _ fun t => pow_nonneg (norm_nonneg _) 3)).symm
  simpa only [ENNReal.toReal_ofNat] using (heq.trans_lt ENNReal.ofReal_lt_top)

end HRS.MS.R26T6C
