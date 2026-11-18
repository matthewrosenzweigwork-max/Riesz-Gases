import HRS.MS.R26T6CI11Joint
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

/-!
# I11: a.e. measurability of every fixed-time Bochner primitive evaluation.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T6C

theorem r26t6c_primitive_eval_aesm
    {Omega B : Type*} [MeasurableSpace Omega]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    (T : ℝ) (P : Measure Omega) [SFinite P]
    (G : ℝ × Omega → B)
    (hG : AEStronglyMeasurable G
      ((volume.restrict (Set.Icc (0 : ℝ) T)).prod P))
    (t : Set.Icc (0 : ℝ) T) :
    AEStronglyMeasurable
      (fun w => ∫ v in Set.Icc (0 : ℝ) (t : ℝ), G (v,w)) P := by
  let dt : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) T)
  let dt' : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) (t : ℝ))
  have hsub : dt' ≤ dt :=
    Measure.restrict_mono (Set.Icc_subset_Icc_right t.2.2) le_rfl
  have hswap : AEStronglyMeasurable
      (fun z : Omega × ℝ => G (z.2,z.1)) (P.prod dt) :=
    hG.prod_swap
  have hswap' : AEStronglyMeasurable
      (fun z : Omega × ℝ => G (z.2,z.1)) (P.prod dt') :=
    hswap.mono_measure (Measure.prod_mono le_rfl hsub)
  exact hswap'.integral_prod_right'

end HRS.MS.R26T6C
