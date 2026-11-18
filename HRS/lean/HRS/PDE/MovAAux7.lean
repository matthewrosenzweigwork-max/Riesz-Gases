import HRS.PDE.MovAAux6

/-!
# MOVA Aux7: transport of one-body sums to the big torus `𝕋^{N d}` and the tilted invariance on `Config d N`.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

/-- The one-body sum `∑_i φ(x_i)` on the big torus. -/
def mova_bigPsi (φ : Torus d → ℝ) : Torus (N * d) → ℝ :=
  fun z => ∑ i, φ ((d1_configEquiv d N).symm z i)

theorem mova_bigPsi_comp (φ : Torus d → ℝ) (X : Config d N) :
    mova_bigPsi φ (d1_configEquiv d N X) = ∑ i, φ (X i) := by
  simp [mova_bigPsi]

theorem mova_bigPsi_cl (φ : Torus d → ℝ) :
    d1_cl (mova_bigPsi (N := N) φ) = fun Y : Fin N → Euc d => ∑ i, Torus.lift φ (Y i) := by
  funext Y
  unfold d1_cl
  rw [mova_bigPsi_comp]
  rfl

theorem mova_bigPsi_isCk {φ : Torus d → ℝ} (hφ : Torus.IsCk 2 φ) :
    Torus.IsCk 2 (mova_bigPsi (N := N) φ) := by
  rw [d1_isCk_iff, mova_bigPsi_cl]
  have hc : ContDiff ℝ 2 (Torus.lift φ) := hφ
  refine ContDiff.sum fun i _ => ?_
  exact hc.comp (contDiff_apply ℝ (Euc d) i)

theorem mova_bigPsi_grad_apply {φ : Torus d → ℝ} (hφ : Torus.IsCk 1 φ) (X : Config d N)
    (i : Fin N) (j : Fin d) :
    (Torus.grad (mova_bigPsi (N := N) φ) (d1_configEquiv d N X)).ofLp (d1_idx d N (i, j)) =
      (Torus.grad φ (X i)).ofLp j := by
  rw [d1_grad_apply, mova_bigPsi_cl, mova_psiL_fderiv hφ, mova_grad_apply]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply]
  rw [Finset.sum_eq_single i]
  · simp [configBasis, Torus.partialDeriv]
  · intro a _ ha
    simp [configBasis, Pi.single_apply, Ne.symm ha]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem mova_bigPsi_grad_sq {φ : Torus d → ℝ} (hφ : Torus.IsCk 1 φ) (X : Config d N) :
    ‖Torus.grad (mova_bigPsi (N := N) φ) (d1_configEquiv d N X)‖ ^ 2 =
      ∑ i, ‖Torus.grad φ (X i)‖ ^ 2 := by
  rw [mova_norm_sq_eq_sum, ← (d1_idx d N).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mova_norm_sq_eq_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mova_bigPsi_grad_apply hφ]

theorem mova_bigU_isCk_one (D : DynData d) (hV : Torus.IsCk 2 D.V) (M : ℝ) :
    Torus.IsCk 1 (b15d_U (N := N) D M) := by
  rw [d1_isCk_iff, b15d_cl_U]
  exact b15c_potentialReg_contDiff D (n := 1) (by exact_mod_cast le_top) (mova_isCk_one_of_two hV) M

/-- Tilted invariance on `Config d N`:
`∫ (L ψ + κ‖∇ψ‖²) e^{-κ⁻¹U^M + ψ} dX = 0` for the one-body sum `ψ = ∑_i φ(x_i)`. -/
theorem mova_ibp_config {κ : ℝ} (hκ : 0 < κ) (D : DynData d)
    (hM : D.M = -(1 : Matrix (Fin d) (Fin d) ℝ)) (hV : Torus.IsCk 2 D.V) (M : ℝ)
    {φ : Torus d → ℝ} (hφ : Torus.IsCk 2 φ) :
    ∫ X : Config d N, (d1_configGen κ (b15d_configDriftReg D M) (fun X => ∑ i, φ (X i)) X +
        κ * ∑ i, ‖Torus.grad φ (X i)‖ ^ 2) *
      Real.exp (-(κ⁻¹ * b15c_potentialReg D M X) + ∑ i, φ (X i)) = 0 := by
  have h := mova_ibp_tilt hκ (mova_bigU_isCk_one (N := N) D hV M) (mova_bigPsi_isCk (N := N) hφ)
  set F : Torus (N * d) → ℝ := fun z =>
    (d1_gen κ (d1_gradDrift (b15d_U (N := N) D M)) (mova_bigPsi (N := N) φ) z +
      κ * ‖Torus.grad (mova_bigPsi (N := N) φ) z‖ ^ 2) *
      Real.exp (-(κ⁻¹ * b15d_U (N := N) D M z) + mova_bigPsi (N := N) φ z) with hF
  have key : ∫ X : Config d N, F (d1_configEquiv d N X) = ∫ z, F z :=
    (d1_configEquiv_measurePreserving d N).integral_comp' F
  refine Eq.trans (integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)) (key.trans h)
  simp only [hF]
  have hdrift : d1_gradDrift (b15d_U (N := N) D M) = d1_pushField (b15d_configDriftReg D M) :=
    funext fun x => (b15d_pushField_eq_gradDrift D hM hV M x).symm
  have hgen : d1_gen κ (d1_gradDrift (b15d_U (N := N) D M)) (mova_bigPsi (N := N) φ)
      (d1_configEquiv d N X) = d1_configGen κ (b15d_configDriftReg D M) (fun X => ∑ i, φ (X i)) X := by
    rw [hdrift, d1_gen_config]
    congr 1
    funext Y
    exact mova_bigPsi_comp φ Y
  rw [hgen, mova_bigPsi_grad_sq (mova_isCk_one_of_two hφ), mova_bigPsi_comp]
  have hU : b15d_U (N := N) D M (d1_configEquiv d N X) = b15c_potentialReg D M X := by
    simp [b15d_U]
  rw [hU]

end HRS
