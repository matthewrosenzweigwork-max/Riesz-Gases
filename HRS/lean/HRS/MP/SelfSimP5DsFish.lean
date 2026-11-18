import HRS.MP.SelfSimP5DsEnt

/-!
# P5 dissipation on `Fin N`: transport of the Fisher information
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set InformationTheory
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.SelfSimP4 HRS.MP.SelfSimP5
  HRS.MP.SelfSimP5Core
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MP.SelfSimP5Ds

/-- Transport of a vector field. -/
def p5d_tf {N : ℕ} (ζ : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)) :
    EucConfig 1 N → EucConfig 1 N :=
  fun x => p5d_e N (ζ ((p5d_e N).symm x))

theorem p5d_tf_apply {N : ℕ} (ζ : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (z : EuclideanSpace ℝ (Fin N)) : p5d_tf ζ (p5d_e N z) = p5d_e N (ζ z) := by
  simp [p5d_tf]

theorem p5d_tf_contDiff {N : ℕ} {ζ : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)}
    (h : ContDiff ℝ ∞ ζ) : ContDiff ℝ ∞ (p5d_tf ζ) :=
  (p5d_e N).contDiff.comp (h.comp (p5d_e N).symm.contDiff)

theorem p5d_tf_compact {N : ℕ} {ζ : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)}
    (h : HasCompactSupport ζ) : HasCompactSupport (p5d_tf ζ) := by
  have h1 : HasCompactSupport (ζ ∘ (p5d_e N).symm) :=
    h.comp_homeomorph (p5d_e N).symm.toHomeomorph
  exact h1.comp_left (g := p5d_e N) (map_zero _)

/-- Inverse transport of a vector field. -/
def p5d_tfi {N : ℕ} (ζ : EucConfig 1 N → EucConfig 1 N) :
    EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N) :=
  fun z => (p5d_e N).symm (ζ (p5d_e N z))

theorem p5d_tfi_contDiff {N : ℕ} {ζ : EucConfig 1 N → EucConfig 1 N}
    (h : ContDiff ℝ ∞ ζ) : ContDiff ℝ ∞ (p5d_tfi ζ) :=
  (p5d_e N).symm.contDiff.comp (h.comp (p5d_e N).contDiff)

theorem p5d_tfi_compact {N : ℕ} {ζ : EucConfig 1 N → EucConfig 1 N}
    (h : HasCompactSupport ζ) : HasCompactSupport (p5d_tfi ζ) := by
  have h1 : HasCompactSupport (ζ ∘ (p5d_e N)) :=
    h.comp_homeomorph (p5d_e N).toHomeomorph
  exact h1.comp_left (g := (p5d_e N).symm) (map_zero _)

theorem p5d_tf_tfi {N : ℕ} (ζ : EucConfig 1 N → EucConfig 1 N) : p5d_tf (p5d_tfi ζ) = ζ := by
  funext x
  simp [p5d_tf, p5d_tfi]

theorem p5d_tfi_tf {N : ℕ} (ζ : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)) :
    p5d_tfi (p5d_tf ζ) = ζ := by
  funext x
  simp [p5d_tf, p5d_tfi]

theorem p5d_symm_basis {N : ℕ} (i : Fin N) (j : Fin 1) :
    (p5d_e N).symm (configBasis 1 N (i, j)) = EuclideanSpace.single i (1 : ℝ) := by
  have hj : j = 0 := Subsingleton.elim _ _
  subst hj
  ext k
  rw [p5d_e_symm_apply]
  by_cases hk : k = i
  · subst hk
    simp [configBasis]
  · simp [configBasis, Pi.single_apply, hk, PiLp.single_apply]

theorem p5d_div {N : ℕ} {ζ : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)}
    (z : EuclideanSpace ℝ (Fin N)) :
    configDivW (p5d_tf ζ) (p5d_e N z) = ss5_div ζ z := by
  unfold configDivW ss5_div
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fin.sum_univ_one]
  have hfun : (fun Z : EucConfig 1 N => p5d_tf ζ Z i 0) =
      (fun w : EuclideanSpace ℝ (Fin N) => ζ w i) ∘ (p5d_e N).symm := by
    funext Z
    simp only [p5d_tf, Function.comp]
    rw [p5d_e_apply]
  rw [hfun, ContinuousLinearEquiv.comp_right_fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]
  rw [p5d_symm_basis]

theorem p5d_logG {N : ℕ} {θ : ℝ} {U : EuclideanSpace ℝ (Fin N) → ℝ} (hU : Differentiable ℝ U)
    {ζ : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)} (z : EuclideanSpace ℝ (Fin N)) :
    fderiv ℝ (fun Z : EucConfig 1 N => Real.log (p4GibbsOf θ (p5d_V U) Z)) (p5d_e N z)
        (p5d_tf ζ (p5d_e N z)) = -(θ⁻¹) * inner ℝ (gradient U z) (ζ z) := by
  have hfun : (fun Z : EucConfig 1 N => Real.log (p4GibbsOf θ (p5d_V U) Z)) =
      fun Z => -(θ⁻¹) * (U ∘ (p5d_e N).symm) Z := by
    funext Z
    simp [p4GibbsOf, p5d_V, Real.log_exp]
  have hd : Differentiable ℝ (U ∘ (p5d_e N).symm) := hU.comp (p5d_e N).symm.differentiable
  rw [hfun, fderiv_const_mul (hd _), ContinuousLinearEquiv.comp_right_fderiv]
  have hg : inner ℝ (gradient U z) (ζ z) = fderiv ℝ U z (ζ z) := by
    unfold gradient
    rw [InnerProductSpace.toDual_symm_apply]
  rw [hg, p5d_tf_apply]
  simp

theorem p5d_sumsq {N : ℕ} (w : EuclideanSpace ℝ (Fin N)) :
    ∑ i, ‖p5d_e N w i‖ ^ 2 = ‖w‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [p5d_norm_e_comp, sq_abs]

/-- The integrand of `ss5_fish` is the integrand of `fisherCptW` along the transport. -/
theorem p5d_integrand {N : ℕ} {θ : ℝ} {U : EuclideanSpace ℝ (Fin N) → ℝ} (hU : Differentiable ℝ U)
    (ζ : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)) (z : EuclideanSpace ℝ (Fin N)) :
    (-2 * configDivW (p5d_tf ζ) (p5d_e N z) -
        2 * fderiv ℝ (fun Z : EucConfig 1 N => Real.log (p4GibbsOf θ (p5d_V U) Z)) (p5d_e N z)
          (p5d_tf ζ (p5d_e N z)) - ∑ i, ‖p5d_tf ζ (p5d_e N z) i‖ ^ 2) =
      -2 * ss5_div ζ z + 2 * θ⁻¹ * inner ℝ (gradient U z) (ζ z) - ‖ζ z‖ ^ 2 := by
  rw [p5d_div, p5d_logG hU, p5d_tf_apply, p5d_sumsq]
  ring

theorem p5d_integral {N : ℕ} {θ : ℝ} {U : EuclideanSpace ℝ (Fin N) → ℝ} (hU : Differentiable ℝ U)
    (ζ : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (μ : Measure (EuclideanSpace ℝ (Fin N))) :
    ∫ X : EucConfig 1 N,
      (-2 * configDivW (p5d_tf ζ) X -
        2 * fderiv ℝ (fun Z : EucConfig 1 N => Real.log (p4GibbsOf θ (p5d_V U) Z)) X (p5d_tf ζ X) -
          ∑ i, ‖p5d_tf ζ X i‖ ^ 2) ∂(μ.map (p5d_e N)) =
    ∫ z, (-2 * ss5_div ζ z + 2 * θ⁻¹ * inner ℝ (gradient U z) (ζ z) - ‖ζ z‖ ^ 2) ∂μ := by
  rw [(p5d_measurableEmbedding N).integral_map]
  exact integral_congr_ae (Eventually.of_forall fun z => p5d_integrand hU ζ z)

theorem p5d_fish {N : ℕ} {θ : ℝ} {U : EuclideanSpace ℝ (Fin N) → ℝ} (hU : Differentiable ℝ U)
    (μ : Measure (EuclideanSpace ℝ (Fin N))) :
    ss5_fish θ U μ = fisherCptW (p4GibbsOf θ (p5d_V U)) (μ.map (p5d_e N)) := by
  unfold ss5_fish fisherCptW
  apply le_antisymm
  · refine iSup₂_le fun ζ hζ => ?_
    refine le_iSup₂_of_le (p5d_tf ζ) ⟨p5d_tf_contDiff hζ.smooth, p5d_tf_compact hζ.compact⟩ ?_
    rw [p5d_integral hU]
  · refine iSup₂_le fun ζ' hζ' => ?_
    refine le_iSup₂_of_le (p5d_tfi ζ') ⟨p5d_tfi_contDiff hζ'.1, p5d_tfi_compact hζ'.2⟩ ?_
    rw [← p5d_integral hU, p5d_tf_tfi]

end HRS.MP.SelfSimP5Ds
