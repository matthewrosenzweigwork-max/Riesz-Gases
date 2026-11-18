import HRS.MC.CepH2Fish1
import HRS.MC.CepH2Sde3

/-!
# CEPH2, the `ζ`-functional of a mollified density is bounded by its dissipation
-/

open MeasureTheory Filter Topology ProbabilityTheory Set InformationTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepH2

open HRS HRS.MC.Cepa

variable {N : ℕ} [NeZero N]

theorem h2_ofReal_integral_le {s : Set (Ch N)} {G : Ch N → ℝ} (hG : IntegrableOn G s) :
    ENNReal.ofReal (∫ x in s, G x) ≤ ∫⁻ x in s, ENNReal.ofReal (G x) := by
  have hp : IntegrableOn (fun x => max (G x) 0) s := hG.pos_part
  have h1 : ∫ x in s, G x ≤ ∫ x in s, max (G x) 0 := integral_mono hG hp (fun x => le_max_left _ _)
  refine (ENNReal.ofReal_le_ofReal h1).trans ?_
  rw [ofReal_integral_eq_lintegral_ofReal hp (ae_of_all _ fun x => le_max_right _ _)]
  refine le_of_eq (lintegral_congr fun x => ?_)
  simp [ENNReal.ofReal_max]

theorem h2_sum_coord_apply (f : Ch N →L[ℝ] ℝ) (z : Ch N) :
    f z = ∑ k : Fin N, z k * f (EuclideanSpace.single k 1) := by
  have h : z = ∑ k : Fin N, z k • (EuclideanSpace.single k (1 : ℝ) : Ch N) := by
    rw [h2_sum_single]
  conv_lhs => rw [h]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, smul_eq_mul]


theorem h2_fint_le_D1 {θ v : ℝ} (hθ : 0 < θ) (hv : 0 < v) {U : Ch N → ℝ} (hU : ContDiff ℝ 1 U)
    (hUper : ∀ z, U (z + cep_diag N) = U z) {ζ : Ch N → Ch N}
    (hζ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ζ) (hper : ∀ z, ζ (z + cep_diag N) = ζ z) {R : ℝ}
    (hfar : ∀ z, R < ‖h2_perp z‖ → ζ z = 0) (μ : Measure (Ch N)) [IsProbabilityMeasure μ] :
    ENNReal.ofReal (∫ z, h2_fint θ U ζ z ∂(h2_dMeas (h2_mu v μ))) ≤
      ∫⁻ x in cep_cell N, ENNReal.ofReal (h2_dens θ v U μ x) := by
  set u := h2_mu v μ with hu
  have hu1 : ContDiff ℝ 1 u := h2_contDiff_mu hv μ
  have huper : ∀ x, u (x + cep_diag N) = u x := h2_mu_periodic v μ
  have hu0 : ∀ x, 0 < u x := h2_mu_pos hv μ
  have hdu : ∀ x, fderiv ℝ u x = h2_mu1 v μ x := fun x => (h2_hasFDerivAt_mu hv μ x).fderiv
  have hduc : Continuous (fderiv ℝ u) := hu1.continuous_fderiv (by simp)
  have hdUc : Continuous (fderiv ℝ U) := hU.continuous_fderiv (by simp)
  have hζc : Continuous ζ := hζ.continuous
  have hdUper : ∀ x, fderiv ℝ U (x + cep_diag N) = fderiv ℝ U x := h2_fderiv_periodic hUper
  have hduper : ∀ x, fderiv ℝ u (x + cep_diag N) = fderiv ℝ u x := h2_fderiv_periodic huper
  have hz1 : ∀ k : Fin N, ContDiff ℝ 1 (fun w => ζ w k) := h2_zk_contDiff hζ
  set dz : Fin N → Ch N → ℝ := fun k x => fderiv ℝ (fun w => ζ w k) x (EuclideanSpace.single k 1) with hdz
  have hdzc : ∀ k, Continuous (dz k) := fun k =>
    ((hz1 k).continuous_fderiv (by simp)).clm_apply continuous_const
  have hdzper : ∀ k x, dz k (x + cep_diag N) = dz k x := fun k x => by
    simp only [hdz]; rw [h2_fderiv_periodic (h2_zk_periodic hper k) x]
  have hdzfar : ∀ k x, R < ‖h2_perp x‖ → dz k x = 0 := fun k x hx => by
    simp only [hdz]; rw [h2_fderiv_eq_zero_of_far (h2_zk_far hfar k) hx]; rfl
  have hfint := fun P (hc : Continuous P) (hp : ∀ x, P (x + cep_diag N) = P x)
      (hf : ∀ x, R < ‖h2_perp x‖ → P x = 0) => h2_integrable_cell_of_far hc hp hf
  -- the integrated-by-parts identities
  set A : Fin N → Ch N → ℝ := fun k x => u x * dz k x with hA
  set B : Fin N → Ch N → ℝ := fun k x => ζ x k * fderiv ℝ u x (EuclideanSpace.single k 1) with hB
  have hAc : ∀ k, Continuous (A k) := fun k => hu1.continuous.mul (hdzc k)
  have hBc : ∀ k, Continuous (B k) := fun k =>
    ((EuclideanSpace.proj (𝕜 := ℝ) k).continuous.comp hζc).mul (hduc.clm_apply continuous_const)
  have hAi : ∀ k, IntegrableOn (A k) (cep_cell N) := fun k =>
    hfint _ (hAc k) (fun x => by simp only [hA, huper, hdzper]) (fun x hx => by simp only [hA, hdzfar k x hx, mul_zero])
  have hBi : ∀ k, IntegrableOn (B k) (cep_cell N) := fun k =>
    hfint _ (hBc k) (fun x => by simp only [hB, hper, hduper]) (fun x hx => by
      simp only [hB, hfar x hx]; simp)
  have hibp : ∀ k, ∫ x in cep_cell N, (A k x + B k x) = 0 := by
    intro k
    have hF : ContDiff ℝ 1 (fun x => u x * ζ x k) := hu1.mul (hz1 k)
    have hFper : ∀ x, (fun x => u x * ζ x k) (x + cep_diag N) = (fun x => u x * ζ x k) x := fun x => by
      simp only [huper, hper]
    have hFfar : ∀ x, R < ‖h2_perp x‖ → (fun x => u x * ζ x k) x = 0 := fun x hx => by
      simp only [hfar x hx]; simp
    have := h2_ibp_per hF hFper hFfar (EuclideanSpace.single k 1)
    rw [← this]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    have hd : fderiv ℝ (fun x => u x * ζ x k) x = u x • fderiv ℝ (fun w => ζ w k) x + (ζ x k) • fderiv ℝ u x :=
      fderiv_mul (hu1.differentiable (by simp) x) ((hz1 k).differentiable (by simp) x)
    simp only [hA, hB, hd, hdz, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  -- the pointwise identity
  set H : Ch N → ℝ := fun x => 2 * fderiv ℝ u x (ζ x) + 2 * θ⁻¹ * u x * fderiv ℝ U x (ζ x) - u x * ‖ζ x‖ ^ 2 with hH
  have hHc : Continuous H := by
    simp only [hH]
    refine ((continuous_const.mul (hduc.clm_apply hζc)).add ((continuous_const.mul hu1.continuous).mul
      (hdUc.clm_apply hζc))).sub (hu1.continuous.mul (hζc.norm.pow 2))
  have hHi : IntegrableOn H (cep_cell N) :=
    hfint _ hHc (fun x => by simp only [hH, huper, hduper, hdUper, hper]) (fun x hx => by
      simp only [hH, hfar x hx]; simp)
  have hgi : IntegrableOn (fun x => u x * h2_fint θ U ζ x) (cep_cell N) :=
    hfint _ (hu1.continuous.mul (h2_fint_continuous hU θ hζ)) (fun x => by
      simp only [huper, h2_fint_periodic hUper θ hper]) (fun x hx => by
      simp only [h2_fint_far θ hfar hx, mul_zero])
  have hpt : ∀ x, u x * h2_fint θ U ζ x = H x - 2 * ∑ k, (A k x + B k x) := by
    intro x
    have h1 : ∑ k, B k x = fderiv ℝ u x (ζ x) := by
      rw [h2_sum_coord_apply (fderiv ℝ u x) (ζ x)]
    have h2 : inner ℝ (gradient U x) (ζ x) = fderiv ℝ U x (ζ x) := (h2_fderiv_eq_inner x (ζ x)).symm
    simp only [h2_fint, hH, Finset.sum_add_distrib, h1, h2, hA]
    simp only [hdz, ← Finset.mul_sum]
    ring
  have hcell : ∫ x in cep_cell N, u x * h2_fint θ U ζ x = ∫ x in cep_cell N, H x := by
    have e1 : ∫ x in cep_cell N, u x * h2_fint θ U ζ x =
        ∫ x in cep_cell N, (H x - 2 * ∑ k, (A k x + B k x)) :=
      integral_congr_ae (ae_of_all _ hpt)
    have hSi : IntegrableOn (fun x => ∑ k, (A k x + B k x)) (cep_cell N) :=
      integrable_finset_sum _ fun k _ => (hAi k).add (hBi k)
    have hS : ∫ x in cep_cell N, ∑ k, (A k x + B k x) = ∑ k, ∫ x in cep_cell N, (A k x + B k x) :=
      integral_finset_sum _ fun k _ => (hAi k).add (hBi k)
    rw [e1, integral_sub hHi (hSi.const_mul 2), integral_const_mul, hS]
    simp [hibp]
  -- the density inequality
  have hle : ∀ x, H x ≤ h2_dens θ v U μ x := by
    intro x
    have hd : fderiv ℝ (h2_ell θ v U μ) x = (u x)⁻¹ • fderiv ℝ u x + (1 / θ) • fderiv ℝ U x := by
      rw [h2_fderiv_ell hv hU μ x, hdu x]
    have hHx : H x = u x * (2 * fderiv ℝ (h2_ell θ v U μ) x (ζ x) - ‖ζ x‖ ^ 2) := by
      rw [hd]
      simp only [hH, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      have := (hu0 x).ne'
      field_simp
    rw [hHx]
    unfold h2_dens
    refine mul_le_mul_of_nonneg_left ?_ (hu0 x).le
    have h1 : fderiv ℝ (h2_ell θ v U μ) x (ζ x) ≤ ‖fderiv ℝ (h2_ell θ v U μ) x‖ * ‖ζ x‖ :=
      (le_abs_self _).trans ((Real.norm_eq_abs _).symm ▸ ContinuousLinearMap.le_opNorm _ _)
    nlinarith [sq_nonneg (‖fderiv ℝ (h2_ell θ v U μ) x‖ - ‖ζ x‖)]
  -- conclusion
  have hν : ∫ z, h2_fint θ U ζ z ∂(h2_dMeas u) = ∫ x in cep_cell N, u x * h2_fint θ U ζ x := by
    unfold h2_dMeas
    rw [integral_withDensity_eq_integral_toReal_smul (f := fun x => ENNReal.ofReal (u x))
      (ENNReal.measurable_ofReal.comp hu1.continuous.measurable)
      (Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp [ENNReal.toReal_ofReal (hu0 x).le]
  rw [hν, hcell]
  refine (h2_ofReal_integral_le hHi).trans (lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hle x))

end HRS.MC.CepH2
