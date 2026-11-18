import HRS.MS.S111K4J01I
import HRS.MS.S111TermAux8

/-!
# S11.1 / J01 piece: the B03 interval tensor depends on the forcing only through its a.e. class (S11K4)

Two forcing fields with the K3 coordinate formula for `J z a b`, equal for a.e. time, have equal interval tensors: by T08
(`s111t_tensor_ext`) it suffices to compare the coordinate products `w ↦ ∏ coord`, which are `eval`-functionals of oscillator
tests, and the K3 formula gives integrals of `z v (…)`, which only see `z v` for a.e. `v`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111K4J01

open HRS HRS.Whole

theorem J_congr {d : ℕ} {C : WholeCoeff d} {m T u : ℝ} (hT : 0 < T) {z1 z2 : ℝ → (Euc d → ℝ) → ℝ}
    {a b : ℝ} {J1 J2 : projTensor (OscPath d m T) 2}
    (h1 : HRS.MS.S111K3.K3ShiftedJValue C m T u z1 a b J1)
    (h2 : HRS.MS.S111K3.K3ShiftedJValue C m T u z2 a b J2)
    (hab : Set.Ioc a b ⊆ Set.Icc (0 : ℝ) (u + T))
    (hae : ∀ᵐ v ∂(volume : Measure ℝ), v ∈ Set.Icc (0 : ℝ) (u + T) → z1 v = z2 v) :
    J1 = J2 := by
  refine HRS.MS.S111T.s111t_tensor_ext 2 hT J1 J2 fun tau alpha M hM => ?_
  have hcombo : ∀ β : MultiIndex d, IsR2DualCombo m (oscTestFun m β) := fun β =>
    ⟨{β}, fun _ => 1, by funext x; simp⟩
  have hMeq : M = (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 2) ℝ).compContinuousLinearMap
      ![HRS.MS.R2Interp.s102_ell (T := T) (m := m) (tau 0) (alpha 0), HRS.MS.R2Interp.s102_ell (T := T) (m := m) (tau 1) (alpha 1)] := by
    refine ContinuousMultilinearMap.ext fun w => ?_
    rw [hM w]
    simp [ContinuousMultilinearMap.compContinuousLinearMap_apply, ContinuousMultilinearMap.mkPiAlgebra_apply,
      HRS.MS.R2Interp.s102_ell_apply, Fin.prod_univ_two]
  have hl : ∀ (t : Set.Icc (0 : ℝ) T) (β : MultiIndex d) (w : OscPath d m T),
      HRS.MS.R2Interp.s102_ell (T := T) (m := m) t β w = OscDual.eval (OscPath.at' w t) (oscTestFun m β) := fun t β w => by
    rw [OscDual.eval_oscTestFun]; rfl
  have e1 := h1 (tau 0) (tau 1) (oscTestFun m (alpha 0)) (oscTestFun m (alpha 1))
    (HRS.MS.R2Interp.s102_ell (tau 0) (alpha 0)) (HRS.MS.R2Interp.s102_ell (tau 1) (alpha 1)) (hcombo _) (hcombo _)
    (hl _ _) (hl _ _)
  have e2 := h2 (tau 0) (tau 1) (oscTestFun m (alpha 0)) (oscTestFun m (alpha 1))
    (HRS.MS.R2Interp.s102_ell (tau 0) (alpha 0)) (HRS.MS.R2Interp.s102_ell (tau 1) (alpha 1)) (hcombo _) (hcombo _)
    (hl _ _) (hl _ _)
  rw [hMeq, e1, e2]
  congr 1
  have hset : Set.Ioc a b ∩ Set.Icc 0 (min (u + (tau 0 : ℝ)) (u + (tau 1 : ℝ))) ⊆ Set.Icc (0 : ℝ) (u + T) :=
    Set.inter_subset_left.trans hab
  refine setIntegral_congr_ae (measurableSet_Ioc.inter measurableSet_Icc) ?_
  filter_upwards [hae] with v hv hvS
  rw [hv (hset hvS)]

end HRS.MS.S111K4J01
