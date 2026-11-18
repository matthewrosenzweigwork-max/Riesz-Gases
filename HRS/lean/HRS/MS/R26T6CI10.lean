import HRS.MS.R26T6CI10Primitive

/-!
# R26-T6C.I10 — continuous primitive of a genuine L³ time class.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T6C
open HRS HRS.Whole

local instance : Fact ((1 : ℝ≥0∞) ≤ 3) := ⟨by norm_num⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem r26t6c_primitiveFun_norm_le (T : ℝ) (hT : 0 < T)
    (q : Lp E 3 (volume.restrict (Set.Icc (0 : ℝ) T))) :
    ‖r26t6c_primitiveFun T hT q‖ ≤ max 1 T * ‖q‖ := by
  have hqi : IntegrableOn (q : ℝ → E) (Set.Icc (0 : ℝ) T) :=
    (Lp.memLp q).integrable (by norm_num)
  have hC0 : 0 ≤ max (1 : ℝ) T * ‖q‖ :=
    mul_nonneg ((by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _)) (norm_nonneg q)
  refine (ContinuousMap.norm_le (r26t6c_primitiveFun T hT q) hC0).2 fun t => ?_
  change ‖∫ v in Set.Icc (0 : ℝ) (t : ℝ), (q : ℝ → E) v‖ ≤
    max 1 T * ‖q‖
  calc
    _ ≤ ∫ v in Set.Icc (0 : ℝ) (t : ℝ), ‖(q : ℝ → E) v‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ v in Set.Icc (0 : ℝ) T, ‖(q : ℝ → E) v‖ :=
      setIntegral_mono_set hqi.norm
        (Filter.Eventually.of_forall fun _ => norm_nonneg _)
        (Filter.Eventually.of_forall <| Set.Icc_subset_Icc_right t.2.2)
    _ ≤ T ^ (2 / 3 : ℝ) * ‖q‖ := r26t6c_L3_l1_le T hT.le q
    _ ≤ max 1 T * ‖q‖ :=
      mul_le_mul_of_nonneg_right (r26t6c_time_power_le_max T hT) (norm_nonneg q)

theorem r26t6c_L3_primitive (T : ℝ) (hT : 0 < T) :
    ∃ V : Lp E 3 (volume.restrict (Set.Icc (0 : ℝ) T)) →L[ℝ]
        C(Set.Icc (0 : ℝ) T, E),
      ‖V‖ ≤ max 1 T ∧ ∀ q, ∀ t : Set.Icc (0 : ℝ) T,
        V q t = ∫ v in Set.Icc 0 (t : ℝ), q v := by
  let V := (r26t6c_primitiveLin (E := E) T hT).mkContinuous (max 1 T)
      (r26t6c_primitiveFun_norm_le T hT)
  refine ⟨V, ?_, ?_⟩
  · exact LinearMap.mkContinuous_norm_le _
      (show 0 ≤ max (1 : ℝ) T from (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _)) _
  · intro q t
    rfl

end HRS.MS.R26T6C
