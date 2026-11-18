import HRS.MS.SA16RHeat16

/-!
# S.A.16 (SA16R) Heat17: the heat equation for the kernel, general integration by parts

* `sa16r_g_hasDerivAt_a`: `∂_a g_a(z) = (‖z‖²/(4a²) - d/(2a)) g_a(z)`.
* `sa16r_ddg`: `∂_i (∂_i g_a)(z) = (z_i²/(4a²) - 1/(2a)) g_a(z)`; hence `∑_i ∂_i ∂_i g_a = ∂_a g_a` (`sa16r_g_heat`).
* `sa16r_ibp_gen`: `∫ (∂_i h)(z) ψ(x-z) dz = ∫ h(z) (∂_i ψ)(x-z) dz` for smooth `h` and `ψ ∈ C_c^∞`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16

section Heat17
variable {d : ℕ}

lemma sa16r_g_hasDerivAt_a {a : ℝ} (ha : 0 < a) (z : Euc d) :
    HasDerivAt (fun a : ℝ => sa16r_g d a z)
      ((‖z‖ ^ 2 / (4 * a ^ 2) - (d : ℝ) / (2 * a)) * sa16r_g d a z) a := by
  have h4 : 0 < 4 * Real.pi * a := by positivity
  have h1 : HasDerivAt (fun a : ℝ => (4 * Real.pi * a) ^ (-((d : ℝ) / 2)))
      ((-((d : ℝ) / 2)) * (4 * Real.pi * a) ^ (-((d : ℝ) / 2) - 1) * (4 * Real.pi)) a := by
    have := ((hasDerivAt_id' a).const_mul (4 * Real.pi)).rpow_const (p := -((d : ℝ) / 2)) (Or.inl h4.ne')
    convert this using 1
    ring
  have h2 : HasDerivAt (fun a : ℝ => Real.exp (-(1 / (4 * a)) * ‖z‖ ^ 2))
      (Real.exp (-(1 / (4 * a)) * ‖z‖ ^ 2) * (‖z‖ ^ 2 / (4 * a ^ 2))) a := by
    have hinv : HasDerivAt (fun a : ℝ => (4 * a)⁻¹) (-(4 : ℝ) / (4 * a) ^ 2) a := by
      have := ((hasDerivAt_id' a).const_mul (4 : ℝ)).inv (by positivity : (4 : ℝ) * a ≠ 0)
      convert this using 1
      ring
    have h3 : HasDerivAt (fun a : ℝ => -(1 / (4 * a)) * ‖z‖ ^ 2) (‖z‖ ^ 2 / (4 * a ^ 2)) a := by
      have := (hinv.neg.mul_const (‖z‖ ^ 2))
      refine (this.congr_deriv ?_).congr_of_eventuallyEq ?_
      · field_simp
      · exact Eventually.of_forall fun a => by simp [one_div]
    exact h3.exp
  have := h1.mul h2
  unfold sa16r_g
  convert this using 1
  have hN : (4 * Real.pi * a) ^ (-((d : ℝ) / 2) - 1) = (4 * Real.pi * a) ^ (-((d : ℝ) / 2)) / (4 * Real.pi * a) := by
    rw [Real.rpow_sub h4, Real.rpow_one]
  rw [hN]
  field_simp
  ring

lemma sa16r_ddg {a : ℝ} (ha : 0 < a) (z : Euc d) (i : Fin d) :
    fderiv ℝ (sa16r_dg d a i) z (EuclideanSpace.single i 1) =
      (((z i) ^ 2 / (4 * a ^ 2)) - 1 / (2 * a)) * sa16r_g d a z := by
  have h1 : HasFDerivAt (fun z : Euc d => -(z i) / (2 * a))
      ((-(1 / (2 * a))) • (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ)) z := by
    have := ((-(1 / (2 * a))) • (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ)).hasFDerivAt (x := z)
    convert this using 1
    funext v; simp; ring
  have h2 : HasFDerivAt (sa16r_g d a) (fderiv ℝ (sa16r_g d a) z) z :=
    ((sa16r_g_contDiff (a := a)).differentiable (by simp) z).hasFDerivAt
  have h3 := h1.mul h2
  have hfun : sa16r_dg d a i = fun z => (-(z i) / (2 * a)) * sa16r_g d a z := rfl
  have h3' : HasFDerivAt (fun z : Euc d => (-(z i) / (2 * a)) * sa16r_g d a z) _ z := h3
  rw [hfun, h3'.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hg := sa16r_g_fderiv ha z i
  rw [hg]
  simp [sa16r_dg]
  field_simp
  ring

lemma sa16r_g_heat {a : ℝ} (ha : 0 < a) (z : Euc d) :
    ∑ i : Fin d, fderiv ℝ (sa16r_dg d a i) z (EuclideanSpace.single i 1) =
      (‖z‖ ^ 2 / (4 * a ^ 2) - (d : ℝ) / (2 * a)) * sa16r_g d a z := by
  simp_rw [sa16r_ddg ha z]
  rw [← Finset.sum_mul]
  congr 1
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)]
  simp only [Real.norm_eq_abs, sq_abs, nsmul_eq_mul]
  field_simp

end Heat17

end HRS.Whole.AppendixA.Phase2SA16R
