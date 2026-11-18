import HRS.MS.R26T6CI11Joint

/-!
# I11: samplewise integrability of the oscillator derivative's
# cubic norm from its genuine joint L³ estimate.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T6C
open HRS HRS.Whole

theorem r26t6c_samplewise_integrable_cube
    {Time Omega B : Type*}
    [MeasurableSpace Time] [MeasurableSpace Omega]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    (dt : Measure Time) [SFinite dt]
    (P : Measure Omega) [SFinite P]
    (G : Time × Omega → B)
    (hG : MemLp G 3 (dt.prod P)) :
    ∀ᵐ w ∂P, Integrable (fun t => ‖G (t,w)‖ ^ 3) dt := by
  have hI : Integrable (fun z : Time × Omega => ‖G z‖ ^ 3) (dt.prod P) :=
    hG.integrable_norm_pow (by norm_num : (3 : ℕ) ≠ 0)
  exact hI.prod_left_ae

end HRS.MS.R26T6C
