import HRS.MS.S82VG3
import HRS.MS.CritForceNF3

/-!
# S8.2 A02 (S82V), part 7: second derivative of a row of a pair kernel
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82V
open HRS HRS.Whole HRS.MS.Phase2S82

/-- The Hessian of a row `x ↦ F (x, y)` is bounded by the Hessian of `F`. -/
lemma s82v_hess_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : E × E → ℝ)
    {U : Set (E × E)} (hU : IsOpen U) (hF : ContDiffOn ℝ 2 F U) (x y : E) (hxy : (x, y) ∈ U) :
    ‖fderiv ℝ (fderiv ℝ (fun z => F (z, y))) x‖ ≤ ‖iteratedFDeriv ℝ 2 F (x, y)‖ := by
  have hι : ∀ z : E, HasFDerivAt (fun z : E => (z, y)) (ContinuousLinearMap.inl ℝ E E) z := fun z =>
    (hasFDerivAt_id z).prodMk (hasFDerivAt_const y z)
  have hUo : IsOpen ((fun z : E => (z, y)) ⁻¹' U) :=
    hU.preimage (continuous_id.prodMk continuous_const)
  have hFat : ∀ p ∈ U, ContDiffAt ℝ 2 F p := fun p hp => hF.contDiffAt (hU.mem_nhds hp)
  -- the first derivative of the row near `x`
  set R : ((E × E) →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ E (E × E) ℝ).flip (ContinuousLinearMap.inl ℝ E E) with hR
  have hRapp : ∀ L : (E × E) →L[ℝ] ℝ, R L = L.comp (ContinuousLinearMap.inl ℝ E E) := fun L => rfl
  have hev : fderiv ℝ (fun z => F (z, y)) =ᶠ[𝓝 x] fun z => R (fderiv ℝ F (z, y)) := by
    filter_upwards [hUo.mem_nhds hxy] with z hz
    have hd : DifferentiableAt ℝ F (z, y) := (hFat _ hz).differentiableAt (by norm_num)
    have := hd.hasFDerivAt.comp z (hι z)
    rw [hRapp]
    exact this.fderiv
  have hg : ContDiffAt ℝ 1 (fderiv ℝ F) (x, y) := (hFat _ hxy).fderiv_right (by norm_num)
  have hgd : DifferentiableAt ℝ (fderiv ℝ F) (x, y) := hg.differentiableAt (by norm_num)
  have h1 : HasFDerivAt (fun z : E => fderiv ℝ F (z, y))
      ((fderiv ℝ (fderiv ℝ F) (x, y)).comp (ContinuousLinearMap.inl ℝ E E)) x :=
    hgd.hasFDerivAt.comp x (hι x)
  have h2 : HasFDerivAt (fun z : E => R (fderiv ℝ F (z, y)))
      (R.comp ((fderiv ℝ (fderiv ℝ F) (x, y)).comp (ContinuousLinearMap.inl ℝ E E))) x :=
    R.hasFDerivAt.comp x h1
  rw [hev.fderiv_eq, h2.fderiv]
  have hRn : ‖R‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun L => ?_
    rw [hRapp, one_mul]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (by simpa using mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_inl_le_one ℝ E E) (norm_nonneg L))
  calc ‖R.comp ((fderiv ℝ (fderiv ℝ F) (x, y)).comp (ContinuousLinearMap.inl ℝ E E))‖
      ≤ ‖R‖ * ‖(fderiv ℝ (fderiv ℝ F) (x, y)).comp (ContinuousLinearMap.inl ℝ E E)‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * (‖fderiv ℝ (fderiv ℝ F) (x, y)‖ * ‖ContinuousLinearMap.inl ℝ E E‖) := by
        gcongr
        · exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * (‖fderiv ℝ (fderiv ℝ F) (x, y)‖ * 1) := by
        gcongr
        exact ContinuousLinearMap.norm_inl_le_one ℝ E E
    _ = ‖iteratedFDeriv ℝ 2 F (x, y)‖ := by
        rw [one_mul, mul_one, ← norm_iteratedFDeriv_one (𝕜 := ℝ), norm_iteratedFDeriv_fderiv]

end HRS.MS.S82V

end
