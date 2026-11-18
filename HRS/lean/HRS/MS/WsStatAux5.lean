import HRS.MS.WsStatAux4
import HRS.MS.UlWitTie
import HRS.MS.FeatDecAux3
import HRS.MS.LogReg
import HRS.MS.MovThermAux2
import HRS.MH.DualityRdC1b

/-!
# S21 packet D1: the thermal reference as a stationary mean-field solution

Facts about the thermal equilibrium `rho_beta` of `V = a|x|^2/2` used to build the stationary `WholeSetup` of S2.1 (i):

* `s21_schwartz_thermal`: `IsSchwartzDensity (thermalDensity d s a beta)` for all `0 <= s < d` (S3.4 regularity for `s > 0`,
  S4.1 for `s = 0`);
* `s21_confinement_eq`: `confinement a = quadV (a . 1) 0`, hence `quadraticGradientDyn d s a beta = <s, -1, quadV (a.1) 0, beta^{-1}>`;
* `s21_gradU_eq`: for a thermal `rho`, the cancellation force `convGradConvW (rieszKernelGrad d s) rho` is the gradient of the
  potential `g * mu` (Euler equation `mv0_thermal_force` against `mv0_sqrt_gauss_thermal`);
* `s21_lap_bound`: `|Delta psi| <= d * cbNorm 2 psi` for `psi in C_b^2`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.S21

open HRS.Whole
open HRS (Euc)

variable {d : ℕ}

theorem s21_schwartz_thermal (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a)
    (hβ : 0 < β) : IsSchwartzDensity (thermalDensity d s a β) := by
  rcases hs0.eq_or_lt with h0 | h0
  · subst h0
    obtain ⟨C, c, BU, hT⟩ := S45.s45_thermal_data hd le_rfl hsd ha hβ
    obtain ⟨⟨f, hf⟩, -⟩ := HRS.MS.LogReg.logThermal_regularity_proof hd a β ha hβ
    exact ⟨hT.prob, f, funext hf⟩
  · exact HRS.MS.S85.s85_thermal_schwartz hd h0 hsd ha hβ

theorem s21_matVec_smul_one (a : ℝ) (x : Euc d) :
    Torus.matVec (a • (1 : Matrix (Fin d) (Fin d) ℝ)) x = a • x := by
  unfold Torus.matVec
  simp

theorem s21_matVec_neg_one (x : Euc d) :
    Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ) x = -x := by
  unfold Torus.matVec
  simp

theorem s21_confinement_eq (a : ℝ) :
    (confinement a : Euc d → ℝ) = quadV (a • (1 : Matrix (Fin d) (Fin d) ℝ)) 0 := by
  funext x
  unfold confinement quadV
  rw [s21_matVec_smul_one]
  simp [real_inner_self_eq_norm_sq, inner_smul_right]
  ring

theorem s21_dyn_eq (s a β : ℝ) :
    quadraticGradientDyn d s a β =
      (⟨s, -1, quadV (a • (1 : Matrix (Fin d) (Fin d) ℝ)) 0, β⁻¹⟩ : WholeDyn d) := by
  unfold quadraticGradientDyn
  rw [s21_confinement_eq]

theorem s21_gradU_eq (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a)
    (hβ : 0 < β) {ρ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s a β ρ) (x : Euc d) :
    convGradConvW (rieszKernelGrad d s) ρ x =
      gradient (HRS.Whole.convMeasure (rieszKernel d s) (thermalMeasure d s a β)) x := by
  have h1 := HRS.MS.Mov0.mv0_thermal_force hd hs0 hsd ha hβ hρ x
  obtain ⟨-, h2, -⟩ := HRS.MS.Mov0.mv0_sqrt_gauss_thermal hd hs0 hsd ha hβ hρ
  rw [h2 x] at h1
  set G := gradient (HRS.Whole.convMeasure (rieszKernel d s) (thermalMeasure d s a β)) x with hG
  have hβ' : β⁻¹ * β = 1 := inv_mul_cancel₀ hβ.ne'
  have : convGradConvW (rieszKernelGrad d s) ρ x - G = 0 := by
    rw [← h1]
    match_scalars <;> field_simp <;> ring
  exact sub_eq_zero.1 this

/-! ### Bounds for `C_b^2` test functions -/

theorem s21_iter_le_cb {ψ : Euc d → ℝ} (hψ : MemCb 2 ψ) {j : ℕ} (hj : j ≤ 2) (z : Euc d) :
    ‖iteratedFDeriv ℝ j ψ z‖ ≤ HRS.cbNorm 2 ψ := by
  have h0 : ‖iteratedFDeriv ℝ j ψ z‖ ≤ ⨆ w : Euc d, ‖iteratedFDeriv ℝ j ψ w‖ :=
    le_ciSup (hψ.2 j hj) z
  refine h0.trans ?_
  unfold HRS.cbNorm
  exact Finset.single_le_sum (f := fun j => ⨆ w : Euc d, ‖iteratedFDeriv ℝ j ψ w‖)
    (fun j _ => Real.iSup_nonneg fun w => norm_nonneg _) (Finset.mem_range.2 (by omega))

theorem s21_grad_bound {ψ : Euc d → ℝ} (hψ : MemCb 2 ψ) (z : Euc d) :
    ‖gradient ψ z‖ ≤ HRS.cbNorm 2 ψ := by
  have h1 : ‖gradient ψ z‖ = ‖fderiv ℝ ψ z‖ := by
    unfold gradient
    exact (InnerProductSpace.toDual ℝ (Euc d)).symm.norm_map _
  rw [h1, ← norm_iteratedFDeriv_one (𝕜 := ℝ) (x := z) (f := ψ)]
  exact s21_iter_le_cb hψ (by norm_num) z

theorem s21_hess_bound {ψ : Euc d → ℝ} (hψ : MemCb 2 ψ) (z : Euc d) :
    ‖fderiv ℝ (gradient ψ) z‖ ≤ HRS.cbNorm 2 ψ := by
  refine (HRS.MH.DualityRd.db1_fderiv_gradient_le hψ.1 z).trans ?_
  have h1 := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := ψ) (x := z) (n := 1)
  have h2 := norm_iteratedFDeriv_one (𝕜 := ℝ) (x := z) (fderiv ℝ ψ)
  rw [← h2, h1]
  exact s21_iter_le_cb hψ le_rfl z

theorem s21_lap_bound {ψ : Euc d → ℝ} (hψ : MemCb 2 ψ) (x : Euc d) :
    |Laplacian.laplacian ψ x| ≤ d * HRS.cbNorm 2 ψ := by
  rw [← S45.s45_div_gradient hψ.1 x]
  unfold S45.s45_div
  have hnb : ∀ a : Fin d, ‖(EuclideanSpace.single a (1 : ℝ) : Euc d)‖ ≤ 1 := fun a => by simp
  calc |∑ a : Fin d, (fderiv ℝ (gradient ψ) x (EuclideanSpace.single a (1 : ℝ))) a|
      ≤ ∑ a : Fin d, |(fderiv ℝ (gradient ψ) x (EuclideanSpace.single a (1 : ℝ))) a| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a : Fin d, HRS.cbNorm 2 ψ := by
        refine Finset.sum_le_sum fun a _ => ?_
        refine (S45.s45_abs_coord_le _ a).trans ?_
        calc ‖fderiv ℝ (gradient ψ) x (EuclideanSpace.single a (1 : ℝ))‖
            ≤ ‖fderiv ℝ (gradient ψ) x‖ * ‖(EuclideanSpace.single a (1 : ℝ) : Euc d)‖ :=
              ContinuousLinearMap.le_opNorm _ _
          _ ≤ HRS.cbNorm 2 ψ * 1 := by
              gcongr
              · exact (norm_nonneg _).trans (s21_hess_bound hψ x)
              · exact s21_hess_bound hψ x
              · exact hnb a
          _ = _ := mul_one _
    _ = d * HRS.cbNorm 2 ψ := by simp

theorem s21_lap_continuous {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 2 ψ) :
    Continuous (Laplacian.laplacian ψ) := by
  have h : Laplacian.laplacian ψ = fun x => S45.s45_div (gradient ψ) x := by
    funext x; exact (S45.s45_div_gradient hψ x).symm
  rw [h]
  unfold S45.s45_div
  refine continuous_finset_sum _ fun a _ => ?_
  have hc : Continuous (fderiv ℝ (gradient ψ)) :=
    (S45.s45_contDiff_gradient hψ).continuous_fderiv one_ne_zero
  exact (EuclideanSpace.proj a : Euc d →L[ℝ] ℝ).continuous.comp (hc.clm_apply continuous_const)

/-! ### Gaussian domination -/

theorem s21_gauss_dom {s a β C c BU : ℝ} (hT : S45.ThermalData d s a β C c BU) {f : Euc d → ℝ}
    (hf : AEStronglyMeasurable f volume) {K : ℝ} (hK : ∀ x, |f x| ≤ K * (1 + ‖x‖)) :
    Integrable (fun x => thermalDensity d s a β x * f x) := by
  have hc := hT.hc
  have hK0 : 0 ≤ K := by
    have := hK 0
    simp only [norm_zero, add_zero, mul_one] at this
    exact (abs_nonneg _).trans this
  obtain ⟨Cp, hCp0, hCp⟩ := S45.s45_poly_le (c := c / 4) (by positivity)
  have hg := HRS.MP.SelfSimP4Impl.p4g_integrable_gauss d (b := 3 * c / 4) (by positivity)
  refine Integrable.mono' (hg.const_mul (C * K * Cp)) (hT.prob.measurable.aestronglyMeasurable.mul hf)
    (Filter.Eventually.of_forall fun x => ?_)
  have hn := norm_nonneg x
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hT.prob.nonneg x)]
  have h1 : thermalDensity d s a β x ≤ C * Real.exp (-c * ‖x‖ ^ 2) := (le_abs_self _).trans (hT.h0 x)
  have h2 : |f x| ≤ K * (Cp * Real.exp (c / 4 * ‖x‖ ^ 2)) :=
    (hK x).trans (mul_le_mul_of_nonneg_left (hCp ‖x‖ hn) hK0)
  have e : Real.exp (-c * ‖x‖ ^ 2) * Real.exp (c / 4 * ‖x‖ ^ 2) = Real.exp (-(3 * c / 4 * ‖x‖ ^ 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  calc thermalDensity d s a β x * |f x|
      ≤ (C * Real.exp (-c * ‖x‖ ^ 2)) * (K * (Cp * Real.exp (c / 4 * ‖x‖ ^ 2))) :=
        mul_le_mul h1 h2 (abs_nonneg _) (by have := hT.C0; positivity)
    _ = (C * K * Cp) * (Real.exp (-c * ‖x‖ ^ 2) * Real.exp (c / 4 * ‖x‖ ^ 2)) := by ring
    _ = _ := by rw [e]

end HRS.MS.S21
