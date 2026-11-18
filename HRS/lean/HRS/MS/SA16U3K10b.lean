import HRS.MS.SA16U3K10a

/-!
# S.A.16 K10, part (b): `T` commutes with the first derivative of a Schwartz function (worker SA16U3)
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16Cutoff
open HRS HRS.Whole HRS.Whole.AppendixA HRS.CZ.Pv HRS.CZ.ElemA Phase2SA16

section K10b
variable {d : ℕ}

lemma sa16u3_schwartz_fderiv_bdd (W : SchwartzMap (Euc d) ℝ) :
    ∃ Bd : ℝ, ∀ y, ‖fderiv ℝ W y‖ ≤ Bd :=
  ⟨SchwartzMap.seminorm ℝ 0 1 W, fun y => by simpa using W.le_seminorm ℝ 0 1 y⟩

lemma sa16u3_fderiv_cont (W : SchwartzMap (Euc d) ℝ) : Continuous (fun y => fderiv ℝ W y) :=
  (W.smooth 1).continuous_fderiv (by simp)

lemma sa16u3_dK_int (hd : 1 ≤ d) {θ δ : ℝ} (hθ1 : 1 < θ) (hδ : 0 < δ) (i : Fin d)
    (W : SchwartzMap (Euc d) ℝ) (x : Euc d) :
    Integrable (fun z => spliceKernel d θ δ i z • fderiv ℝ W (x - z)) := by
  obtain ⟨Bd, hBd⟩ := sa16u3_schwartz_fderiv_bdd W
  refine Integrable.mono' ((sa16u3_K_int hd hθ1 hδ i).norm.mul_const Bd)
    ((sa16k5_ks_meas θ δ i).aestronglyMeasurable.smul
      ((sa16u3_fderiv_cont W).comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
    (Eventually.of_forall fun z => ?_)
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (hBd _) (norm_nonneg _)

lemma sa16u3_T_hasFDerivAt (hd : 1 ≤ d) {θ δ : ℝ} (hθ1 : 1 < θ) (hδ : 0 < δ) (i : Fin d)
    (W : SchwartzMap (Euc d) ℝ) (x : Euc d) :
    HasFDerivAt (fun y => spliceOdd d θ δ i W y)
      (∫ z, spliceKernel d θ δ i z • fderiv ℝ W (x - z)) x := by
  obtain ⟨Bd, hBd⟩ := sa16u3_schwartz_fderiv_bdd W
  obtain ⟨B0, hB0⟩ := sa16j_schwartz_bdd W
  have hKm : Measurable (spliceKernel d θ δ i) := sa16k5_ks_meas θ δ i
  have key := hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ)
    (F := fun (y z : Euc d) => spliceKernel d θ δ i z * W (y - z))
    (F' := fun (y z : Euc d) => spliceKernel d θ δ i z • fderiv ℝ W (y - z))
    (x₀ := x) (s := Set.univ) (bound := fun z => ‖spliceKernel d θ δ i z‖ * Bd) (μ := volume)
    Filter.univ_mem
    (Eventually.of_forall fun y => hKm.aestronglyMeasurable.mul
      (W.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
    (sa16u3_T_int hd hθ1 hδ i W.continuous (B := B0) (fun y => by
      simpa [Real.norm_eq_abs] using hB0 y) x)
    (hKm.aestronglyMeasurable.smul
      ((sa16u3_fderiv_cont W).comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
    (Eventually.of_forall fun z y _ => by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hBd _) (norm_nonneg _))
    ((sa16u3_K_int hd hθ1 hδ i).norm.mul_const Bd)
    (Eventually.of_forall fun z y _ => by
      have h1 : HasFDerivAt (fun y : Euc d => W (y - z)) (fderiv ℝ W (y - z)) y := by
        have := ((W.differentiableAt (x := y - z)).hasFDerivAt).comp y
          ((hasFDerivAt_id y).sub_const z)
        convert this using 1 <;> first | rfl | simp
      exact h1.const_mul (spliceKernel d θ δ i z))
  exact key

lemma sa16u3_T_fderiv_apply (hd : 1 ≤ d) {θ δ : ℝ} (hθ1 : 1 < θ) (hδ : 0 < δ) (i : Fin d)
    (W : SchwartzMap (Euc d) ℝ) (x v : Euc d) :
    fderiv ℝ (fun y => spliceOdd d θ δ i W y) x v =
      spliceOdd d θ δ i (fun y => fderiv ℝ W y v) x := by
  rw [(sa16u3_T_hasFDerivAt hd hθ1 hδ i W x).fderiv,
    ContinuousLinearMap.integral_apply (sa16u3_dK_int hd hθ1 hδ i W x) v]
  unfold spliceOdd
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp [smul_eq_mul]

lemma sa16u3_T_differentiable (hd : 1 ≤ d) {θ δ : ℝ} (hθ1 : 1 < θ) (hδ : 0 < δ) (i : Fin d)
    (W : SchwartzMap (Euc d) ℝ) : Differentiable ℝ (fun y => spliceOdd d θ δ i W y) :=
  fun x => (sa16u3_T_hasFDerivAt hd hθ1 hδ i W x).differentiableAt

end K10b
end HRS.Whole.AppendixA.Phase2SA16Cutoff
