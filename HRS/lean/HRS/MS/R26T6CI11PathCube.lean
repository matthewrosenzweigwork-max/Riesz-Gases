import HRS.MS.R26T6CI11CubeAlgebra
import HRS.MS.R26T6CI10Bound
import HRS.MS.R26T6CI11MeasPath

/-!
# I11: samplewise cubed norm of a continuous primitive.

The deterministic constant follows from L³-to-L¹ Holder and the
elementary two-term cubic inequality.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T6C
open HRS HRS.Whole
variable {d : ℕ} {m : ℝ}

local instance : Fact ((1 : ℝ≥0∞) ≤ 3) := ⟨by norm_num⟩

theorem r26t6c_primitive_path_cube_le
    (T : ℝ) (hT : 0 < T)
    (I : OscDual d m)
    (G : ℝ → OscDual d m)
    (hG : MemLp G 3 (volume.restrict (Set.Icc (0 : ℝ) T)))
    (L : OscPath d m T)
    (hEq : ∀ t : Set.Icc (0 : ℝ) T,
      OscPath.at' L t = I +
        ∫ v in Set.Icc (0 : ℝ) (t : ℝ), G v) :
    ‖L‖ ^ 3 ≤ 4 * ‖I‖ ^ 3 +
      4 * T ^ 2 * ∫ v in Set.Icc (0 : ℝ) T, ‖G v‖ ^ 3 := by
  let dt : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) T)
  let q : Lp (OscDual d m) 3 dt := hG.toLp G
  have hfull : IntegrableOn G (Set.Icc (0 : ℝ) T) :=
    hG.integrable (by norm_num)
  have hq : ∫ v in Set.Icc (0 : ℝ) T, ‖G v‖ =
      ∫ v in Set.Icc (0 : ℝ) T, ‖(q : ℝ → OscDual d m) v‖ := by
    apply integral_congr_ae
    filter_upwards [hG.coeFn_toLp] with v hv
    rw [hv]
  have hq3 : ‖q‖ ^ 3 =
      ∫ v in Set.Icc (0 : ℝ) T, ‖G v‖ ^ 3 := by
    rw [Lp.norm_toLp G hG]
    exact r26t6c_vector_lpNorm_cube dt G hG
  have hbound : ‖L‖ ≤ ‖I‖ + T ^ (2 / 3 : ℝ) * ‖q‖ := by
    have hC0 : 0 ≤ ‖I‖ + T ^ (2 / 3 : ℝ) * ‖q‖ := by positivity
    refine (ContinuousMap.norm_le L hC0).2 fun t => ?_
    change ‖OscPath.at' L t‖ ≤ _
    rw [hEq t]
    calc
      _ ≤ ‖I‖ + ‖∫ v in Set.Icc (0 : ℝ) (t : ℝ), G v‖ :=
        norm_add_le _ _
      _ ≤ ‖I‖ + ∫ v in Set.Icc (0 : ℝ) (t : ℝ), ‖G v‖ :=
        add_le_add_right (norm_integral_le_integral_norm _) _
      _ ≤ ‖I‖ + ∫ v in Set.Icc (0 : ℝ) T, ‖G v‖ := by
        apply add_le_add_right
        exact setIntegral_mono_set hfull.norm
          (Filter.Eventually.of_forall fun _ => norm_nonneg _)
          (Filter.Eventually.of_forall (Set.Icc_subset_Icc_right t.2.2))
      _ = ‖I‖ + ∫ v in Set.Icc (0 : ℝ) T, ‖(q : ℝ → OscDual d m) v‖ := by rw [hq]
      _ ≤ ‖I‖ + T ^ (2 / 3 : ℝ) * ‖q‖ :=
        add_le_add_right (r26t6c_L3_l1_le T hT.le q) _
  have hpow := pow_le_pow_left₀ (norm_nonneg L) hbound 3
  have hsum := r26t6c_sum_cube_le ‖I‖ (T ^ (2 / 3 : ℝ) * ‖q‖)
    (norm_nonneg I) (mul_nonneg (Real.rpow_nonneg hT.le _) (norm_nonneg q))
  calc
    ‖L‖ ^ 3 ≤ (‖I‖ + T ^ (2 / 3 : ℝ) * ‖q‖) ^ 3 := hpow
    _ ≤ 4 * (‖I‖ ^ 3 + (T ^ (2 / 3 : ℝ) * ‖q‖) ^ 3) := hsum
    _ = 4 * ‖I‖ ^ 3 + 4 * T ^ 2 *
        ∫ v in Set.Icc (0 : ℝ) T, ‖G v‖ ^ 3 := by
      rw [mul_pow, r26t6c_time_power_cube T hT.le, hq3]
      ring

end HRS.MS.R26T6C
