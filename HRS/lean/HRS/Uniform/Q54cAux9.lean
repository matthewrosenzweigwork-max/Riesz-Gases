import HRS.Uniform.Q54cAux8

/-!
# Q54c, part 9: the joint Gaussian law of the pathwise noise functionals

`noise_gaussian`: for a continuous Hilbert martingale `G` with deterministic covariation density `C` and
`C¹` test paths `y_a : [0,t_a] → H`, the random vector
`(⟨G_{t_a}, y_a(t_a)⟩ - ∫_0^{t_a} ⟨G_σ, y_a'(σ)⟩ dσ)_a` has the law `multivariateGaussian 0 Σ`,
`Σ_{ab} = ∫_0^{t_a ∧ t_b} C_σ(y_a(σ), y_b(σ)) dσ`.
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory Complex
open scoped ENNReal NNReal BigOperators Matrix RealInnerProductSpace

namespace HRS.Uniform.Q54c

open HRS HRS.Uniform.Q07c

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

/-- `|C(x,y)| ≤ ‖C‖_{𝔖₁} ‖x‖ ‖y‖`. -/
theorem abs_apply_le_tn {D : H →L[ℝ] H →L[ℝ] ℝ} (hD : IsTraceClassCov D) (x y : H) :
    |D x y| ≤ traceNormForm D * (‖x‖ * ‖y‖) := by
  have hb := bddAbove_pairSum hD
  by_cases hx : x = 0
  · subst hx; simp
  by_cases hy : y = 0
  · subst hy; simp
  have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hyn : 0 < ‖y‖ := norm_pos_iff.2 hy
  set e : H := (‖x‖⁻¹) • x with he
  set f : H := (‖y‖⁻¹) • y with hf
  have hen : ‖e‖ = 1 := by rw [he, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hxn.ne']
  have hfn : ‖f‖ = 1 := by rw [hf, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hyn.ne']
  have hone : ∀ g : H, ‖g‖ = 1 → Orthonormal ℝ (fun _ : Fin 1 => g) := fun g hg =>
    orthonormal_iff_ite.2 (fun i j => by
      have : i = j := Subsingleton.elim i j
      subst this
      simp [real_inner_self_eq_norm_sq, hg])
  let p : OrthonormalPairs H := ⟨⟨1, fun _ => e, fun _ => f⟩, hone e hen, hone f hfn⟩
  have h1 := pairSum_le_traceNormForm hb p
  simp only [Finset.univ_unique, Finset.sum_singleton, p] at h1
  have h2 : D e f = (‖x‖⁻¹) * (‖y‖⁻¹) * D x y := by
    rw [he, hf]
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  rw [h2, abs_mul, abs_mul, abs_of_pos (inv_pos.2 hxn), abs_of_pos (inv_pos.2 hyn)] at h1
  have := mul_le_mul_of_nonneg_left h1 (mul_pos hxn hyn).le
  calc |D x y| = ‖x‖ * ‖y‖ * (‖x‖⁻¹ * ‖y‖⁻¹ * |D x y|) := by field_simp
    _ ≤ ‖x‖ * ‖y‖ * traceNormForm D := this
    _ = _ := by ring


section NoiseGauss

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ}
variable {G : ℝ → Ω → H} {C : ℝ → H →L[ℝ] H →L[ℝ] ℝ} {T : ℝ}

/-- clamping a path into `[0,t]` -/
def clampPath (y : ℝ → H) (t : ℝ) : ℝ → H := fun σ => y (max 0 (min σ t))

theorem continuous_clampPath {y : ℝ → H} {t : ℝ} (ht : 0 ≤ t) (hy : ContinuousOn y (Set.Icc 0 t)) :
    Continuous (clampPath y t) := by
  have hc : Continuous fun σ : ℝ => max 0 (min σ t) :=
    continuous_const.max (continuous_id.min continuous_const)
  refine hy.comp_continuous hc fun σ => ?_
  exact ⟨le_max_left _ _, max_le ht (min_le_right _ _)⟩

theorem isum_clamp (G : ℝ → H) (y : ℝ → H) {T t : ℝ} (hT : 0 ≤ T) (ht : 0 ≤ t) (N : ℕ) :
    isum G (clampPath y t) T t N = isum G y T t N := by
  unfold isum clampPath
  refine Finset.sum_congr rfl fun i _ => ?_
  have h0 : 0 ≤ min (gridPt T N i) t := le_min (gridPt_nonneg hT N i) ht
  have : max 0 (min (min (gridPt T N i) t) t) = min (gridPt T N i) t := by
    rw [min_eq_left (min_le_right _ _)]; exact max_eq_right h0
  rw [this]

end NoiseGauss

end HRS.Uniform.Q54c
