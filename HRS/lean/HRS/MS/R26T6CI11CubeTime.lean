import HRS.MS.R26T6CI11Cube

/-!
# I11: integrated cubic norm bound from the time-section estimates.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T6C

theorem r26t6c_spacetime_cube_le
    {Time Omega B : Type*} [MeasurableSpace Time] [MeasurableSpace Omega]
    [NormedAddCommGroup B]
    (dt : Measure Time) [IsFiniteMeasure dt]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (G : Time × Omega → B)
    (hG : MemLp G 3 (dt.prod P))
    (A : ℝ) (hA : 0 ≤ A)
    (hsec : ∀ᵐ t ∂dt,
      MemLp (fun w => G (t,w)) 3 P ∧
      eLpNorm (fun w => G (t,w)) 3 P ≤ ENNReal.ofReal A) :
    (∫ z, ‖G z‖ ^ 3 ∂(dt.prod P)) ≤ (dt Set.univ).toReal * A ^ 3 := by
  have hi : Integrable (fun z => ‖G z‖ ^ 3) (dt.prod P) :=
    hG.integrable_norm_pow (by norm_num : (3 : ℕ) ≠ 0)
  have hinner : Integrable (fun t => ∫ w, ‖G (t,w)‖ ^ 3 ∂P) dt :=
    hi.integral_prod_left
  have hpoint : ∀ᵐ t ∂dt, (∫ w, ‖G (t,w)‖ ^ 3 ∂P) ≤ A ^ 3 := by
    filter_upwards [hsec] with t ht
    exact r26t6c_vector_cube_le P (fun w => G (t,w))
      ht.1 A hA ht.2
  calc
    _ = ∫ t, ∫ w, ‖G (t,w)‖ ^ 3 ∂P ∂dt := integral_prod _ hi
    _ ≤ ∫ t, A ^ 3 ∂dt :=
      integral_mono_ae hinner (integrable_const _) hpoint
    _ = (dt Set.univ).toReal * A ^ 3 := by
      rw [integral_const]
      simp [Measure.real, mul_comm]

end HRS.MS.R26T6C
