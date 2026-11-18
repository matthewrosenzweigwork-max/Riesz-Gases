import HRS.MS.R26T6CI11Sample
import HRS.MS.R26T6CI10Primitive

/-!
# I11: samplewise continuity of the genuine Bochner time primitive,
# obtained without selecting a time-dependent Lp representative.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T6C
open HRS HRS.Whole

theorem r26t6c_samplewise_continuous_primitive
    {Omega B : Type*} [MeasurableSpace Omega]
    [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
    (T : ℝ) (hT : 0 < T)
    (P : Measure Omega) [SFinite P]
    (G : ℝ × Omega → B)
    (hG : MemLp G 3 ((volume.restrict (Set.Icc 0 T)).prod P)) :
    ∀ᵐ w ∂P,
      ContinuousOn (fun t : ℝ => ∫ v in Set.Icc 0 t, G (v,w))
        (Set.Icc 0 T) := by
  have hsections := r26t6c_samplewise_memLp_three
    (volume.restrict (Set.Icc 0 T)) P G hG
  filter_upwards [hsections] with w hw
  have hint : IntegrableOn (fun v => G (v,w)) (Set.uIcc 0 T) := by
    rw [Set.uIcc_of_le hT.le]
    exact hw.integrable (by norm_num)
  have hc := intervalIntegral.continuousOn_primitive_interval (a := 0) hint
  rw [Set.uIcc_of_le hT.le] at hc
  refine hc.congr ?_
  intro t ht
  change (∫ v in Set.Icc (0 : ℝ) t, G (v,w)) =
    ∫ v in (0 : ℝ)..t, G (v,w)
  rw [intervalIntegral.integral_of_le ht.1, integral_Icc_eq_integral_Ioc]

end HRS.MS.R26T6C
