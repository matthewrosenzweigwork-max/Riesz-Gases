import HRS.MS.R26T6CI11PathCube

/-! I11: Banach-valued L³ criterion from integrability of norm cubed. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T6C

theorem r26t6c_memLp_three_of_integrable_norm_cube
    {Omega B : Type*} [MeasurableSpace Omega]
    [NormedAddCommGroup B]
    (P : Measure Omega) (F : Omega → B)
    (hFm : AEStronglyMeasurable F P)
    (hI : Integrable (fun w => ‖F w‖ ^ 3) P) :
    MemLp F 3 P := by
  apply (memLp_iff).2
  apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (by norm_num : (3 : ℝ≥0∞) ≠ 0)
    (by norm_num : (3 : ℝ≥0∞) ≠ ⊤) hFm).2
  have heq : (∫⁻ w, ‖F w‖ₑ ^ (3 : ℝ) ∂P) =
      ENNReal.ofReal (∫ w, ‖F w‖ ^ 3 ∂P) := by
    calc
      _ = ∫⁻ w, ENNReal.ofReal (‖F w‖ ^ 3) ∂P := by
        refine lintegral_congr (fun w => ?_)
        rw [← ofReal_norm_eq_enorm]
        calc
          (ENNReal.ofReal ‖F w‖) ^ (3 : ℝ) =
              (ENNReal.ofReal ‖F w‖) ^ (3 : ℕ) :=
                ENNReal.rpow_natCast _ 3
          _ = _ := (ENNReal.ofReal_pow (norm_nonneg (F w)) 3).symm
      _ = _ := (ofReal_integral_eq_lintegral_ofReal hI
        (ae_of_all _ fun w => pow_nonneg (norm_nonneg _) 3)).symm
  simpa only [ENNReal.toReal_ofNat] using heq.trans_lt ENNReal.ofReal_lt_top

end HRS.MS.R26T6C
