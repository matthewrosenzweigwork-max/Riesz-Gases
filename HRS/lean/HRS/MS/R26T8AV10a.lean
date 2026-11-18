import HRS.MS.R26T8AO05a1

/-!
# S8.2 T8A.V10a: regularity of the configuration gradient of a smooth compactly supported function

For `F : EucConfig d N → ℝ` of class `C¹`, `HRS.MS.Phase2S82.configGrad F X i = (toDual)⁻¹ (DF X ∘ ι_i)` where `ι_i` is the
inclusion of the `i`-th factor; hence `X ↦ HRS.MS.Phase2S82.configGrad F X i` is continuous, bounded by `‖DF X‖`, and bounded
uniformly if `F` has compact support.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.PDE.ToolboxRd

theorem r26t8a_v10a_eq {d N : ℕ} (F : EucConfig d N → ℝ) (hF : ContDiff ℝ 1 F)
    (X : EucConfig d N) (i : Fin N) :
    HRS.MS.Phase2S82.configGrad F X i = (InnerProductSpace.toDual ℝ (Euc d)).symm
      ((fderiv ℝ F X).comp (ContinuousLinearMap.pi (Pi.single i (ContinuousLinearMap.id ℝ (Euc d))))) := by
  have hF' : ∀ y, HasFDerivAt F (fderiv ℝ F y) y := fun y =>
    (hF.differentiable one_ne_zero y).hasFDerivAt
  unfold HRS.MS.Phase2S82.configGrad gradient
  rw [r26t8a_o05a1_fderiv_update F hF' X i (X i), Function.update_eq_self]

theorem r26t8a_v10a_norm {d N : ℕ} (F : EucConfig d N → ℝ) (hF : ContDiff ℝ 1 F)
    (X : EucConfig d N) (i : Fin N) : ‖HRS.MS.Phase2S82.configGrad F X i‖ ≤ ‖fderiv ℝ F X‖ := by
  rw [r26t8a_v10a_eq F hF X i, LinearIsometryEquiv.norm_map]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  have h1 : ‖(ContinuousLinearMap.pi (Pi.single i (ContinuousLinearMap.id ℝ (Euc d))) :
      Euc d →L[ℝ] EucConfig d N)‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    rw [one_mul]
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg x)).2 fun j => ?_
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  calc _ ≤ ‖fderiv ℝ F X‖ * 1 := by gcongr
    _ = _ := mul_one _

theorem r26t8a_v10a_cont {d N : ℕ} (F : EucConfig d N → ℝ) (hF : ContDiff ℝ 1 F) (i : Fin N) :
    Continuous fun X => HRS.MS.Phase2S82.configGrad F X i := by
  have : (fun X => HRS.MS.Phase2S82.configGrad F X i) = fun X => (InnerProductSpace.toDual ℝ (Euc d)).symm
      ((fderiv ℝ F X).comp (ContinuousLinearMap.pi (Pi.single i (ContinuousLinearMap.id ℝ (Euc d))))) :=
    funext fun X => r26t8a_v10a_eq F hF X i
  rw [this]
  refine (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp ?_
  exact ((ContinuousLinearMap.compL ℝ (Euc d) (EucConfig d N) ℝ).flip
    (ContinuousLinearMap.pi (Pi.single i (ContinuousLinearMap.id ℝ (Euc d))))).continuous.comp
    (hF.continuous_fderiv one_ne_zero)

theorem r26t8a_v10a_bdd {d N : ℕ} (F : EucConfig d N → ℝ) (hF : ContDiff ℝ ∞ F)
    (hFc : HasCompactSupport F) : ∃ C : ℝ, 0 ≤ C ∧ ∀ X i, ‖HRS.MS.Phase2S82.configGrad F X i‖ ≤ C := by
  have h1 : ContDiff ℝ 1 F := hF.of_le (by exact_mod_cast le_top)
  have hc : HasCompactSupport (fderiv ℝ F) := hFc.fderiv (𝕜 := ℝ)
  obtain ⟨C, hC⟩ := (hF.continuous_fderiv (by simp)).bounded_above_of_compact_support hc
  exact ⟨max C 0, le_max_right _ _, fun X i =>
    (r26t8a_v10a_norm F h1 X i).trans ((hC X).trans (le_max_left _ _))⟩

end HRS.MS.R26T8A

end
