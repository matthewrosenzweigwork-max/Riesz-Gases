import HRS.MS.SA16Y3Yg2
import HRS.MS.SA16Y3Mo1
import HRS.MS.SA16Y4Fam1

/-!
# S.A.16 (SA16Y4) Ct1: the derivative gain of mollification, `‖f - ρ_n ⋆ f‖_p ≤ (n+1)^{-1} ∑_i ‖∂_i f‖_p` for `f ∈ C_c^∞`

Two applications of the weighted Minkowski inequality `sa16j_mink` (over the segment variable `s ∈ [0,1]` and over `y`, weight
`ρ_n(y)‖y‖`), after `f(x) - f(x-y) = ∫_0^1 ∇f(x - s y)·y ds`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Q

section Ct1
variable {d : ℕ}

/-- the inner Minkowski step: averaging a translate over the segment does not increase the `L^p` norm -/
lemma sa16y4_seg_mink {p : ℝ} (hp : 1 ≤ p) {g : EuclideanSpace ℝ (Fin d) → ℝ≥0∞} (hg : Measurable g)
    (y : EuclideanSpace ℝ (Fin d)) :
    ∫⁻ x, (∫⁻ s in Ioc (0 : ℝ) 1, g (x - s • y)) ^ p ≤ ∫⁻ x, g x ^ p := by
  have hF : Measurable (Function.uncurry fun (x : EuclideanSpace ℝ (Fin d)) (s : ℝ) => g (x - s • y)) :=
    hg.comp (measurable_fst.sub (measurable_snd.smul_const y))
  have h := sa16j_mink (μ := (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (ν := (volume.restrict (Ioc (0 : ℝ) 1))) hp (a := fun _ => 1) measurable_const hF
  have hinner : ∀ s : ℝ, ∫⁻ x, g (x - s • y) ^ p = ∫⁻ x, g x ^ p := fun s =>
    lintegral_sub_right_eq_self (fun x => g x ^ p) (s • y)
  simp only [one_mul, hinner, lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    Real.volume_Ioc, sub_zero, ENNReal.ofReal_one, mul_one, ENNReal.one_rpow] at h
  simpa using h

/-- `G z = ∑_i |∂_i f (z)|` -/
def sa16y4_G1 (f : EuclideanSpace ℝ (Fin d) → ℝ) (z : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ i : Fin d, |fderiv ℝ f z (EuclideanSpace.single i 1)|

lemma sa16y4_fderiv_le {f : EuclideanSpace ℝ (Fin d) → ℝ} (z y : EuclideanSpace ℝ (Fin d)) :
    |fderiv ℝ f z y| ≤ ‖y‖ * sa16y4_G1 f z := by
  have hy : y = ∑ i : Fin d, y i • EuclideanSpace.single i (1 : ℝ) := by
    have := (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr y
    simpa [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using this.symm
  conv_lhs => rw [hy]
  rw [map_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  unfold sa16y4_G1
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [map_smul, smul_eq_mul, abs_mul]
  exact mul_le_mul_of_nonneg_right (by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le y i) (abs_nonneg _)

lemma sa16y4_seg_ftc {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : IsCcInfty f) (x y : EuclideanSpace ℝ (Fin d)) :
    f x - f (x - y) = ∫ s in (0 : ℝ)..1, fderiv ℝ f (x - s • y) y := by
  have hd : Differentiable ℝ f := hf.1.differentiable (by simp)
  have hder : ∀ s : ℝ, HasDerivAt (fun s : ℝ => f (x - s • y)) (-(fderiv ℝ f (x - s • y) y)) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => x - s • y) (-y) s := by
      simpa using ((hasDerivAt_id s).smul_const y).const_sub x
    have h2 := (hd (x - s • y)).hasFDerivAt.comp_hasDerivAt s h1
    rw [map_neg] at h2
    exact h2
  have hcont : Continuous (fun s : ℝ => fderiv ℝ f (x - s • y) y) :=
    ((hf.1.continuous_fderiv (by simp)).comp (continuous_const.sub (continuous_id.smul continuous_const))).clm_apply
      continuous_const
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hder s) (hcont.neg.intervalIntegrable 0 1)
  simp only [one_smul, zero_smul, sub_zero, intervalIntegral.integral_neg] at this
  linarith

end Ct1

end HRS.Whole.AppendixA.Phase2SA16R
