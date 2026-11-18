import HRS.Uniform.Q12P12

/-!
# Q12, Peyre part 13: the integration by parts identity and the weak continuity equation
-/

noncomputable section

open HRS MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators Real

namespace HRS.Uniform.Q12

variable {d : ℕ}

lemma q12_clm_apply_eq_sum (L : Euc d →L[ℝ] ℝ) (w : Euc d) :
    L w = ∑ j : Fin d, w j * L (EuclideanSpace.single j 1) := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr w]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul]
  simp [EuclideanSpace.basisFun_apply]

lemma q12_gradient_coord (F : Euc d → ℝ) (y : Euc d) (j : Fin d) :
    gradient F y j = fderiv ℝ F y (EuclideanSpace.single j 1) := by
  have h := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := Euc d)
    (x := EuclideanSpace.single j 1) (y := fderiv ℝ F y)
  have h2 : inner ℝ (EuclideanSpace.single j (1 : ℝ)) (gradient F y) = gradient F y j := by
    rw [EuclideanSpace.inner_single_left]; simp
  rw [← h, ← h2, real_inner_comm]
  rfl

/-- `DΦ(y)[∇u(y)] = ∑_j ∂_jΦ(y) ∂_j u(y)`. -/
lemma q12_clm_gradient_eq (L : Euc d →L[ℝ] ℝ) (F : Euc d → ℝ) (y : Euc d) :
    L (gradient F y) = ∑ j : Fin d, L (EuclideanSpace.single j 1) *
      fderiv ℝ F y (EuclideanSpace.single j 1) := by
  rw [q12_clm_apply_eq_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [q12_gradient_coord]; ring


namespace PeyreData

lemma hasDerivAt_theta (t : ℝ) : HasDerivAt theta (theta' t) t := by
  have h1 : HasDerivAt (fun t : ℝ => π * t / 2) (π / 2) t := by
    simpa using ((hasDerivAt_id t).const_mul π).div_const 2
  have h2 := (Real.hasDerivAt_sin (π * t / 2)).comp t h1
  have h3 := h2.pow 2
  have e : theta' t = (2 : ℕ) * Real.sin (π * t / 2) ^ (2 - 1) * (Real.cos (π * t / 2) * (π / 2)) := by
    unfold theta'
    have : Real.sin (π * t) = 2 * Real.sin (π * t / 2) * Real.cos (π * t / 2) := by
      rw [← Real.sin_two_mul]; congr 1; ring
    rw [this]; push_cast; ring
  rw [e]
  exact h3

lemma hasDerivAt_theta' (t : ℝ) : HasDerivAt theta' (π ^ 2 / 2 * Real.cos (π * t)) t := by
  have h1 : HasDerivAt (fun t : ℝ => π * t) π t := by
    simpa using (hasDerivAt_id t).const_mul π
  have h2 := (Real.hasDerivAt_sin (π * t)).comp t h1
  have h3 := h2.const_mul (π / 2)
  have e : π ^ 2 / 2 * Real.cos (π * t) = π / 2 * (Real.cos (π * t) * π) := by ring
  rw [e]
  exact h3

lemma theta'_lip (a b : ℝ) : |theta' a - theta' b| ≤ π ^ 2 / 2 * |a - b| := by
  have := (convex_univ (𝕜 := ℝ) (E := ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := theta') (f' := fun x => π ^ 2 / 2 * Real.cos (π * x)) (C := π ^ 2 / 2)
    (fun x _ => (hasDerivAt_theta' x).hasDerivWithinAt)
    (fun x _ => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ π ^ 2 / 2)]
      calc π ^ 2 / 2 * |Real.cos (π * x)| ≤ π ^ 2 / 2 * 1 :=
            mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (by positivity)
        _ = π ^ 2 / 2 := mul_one _)
    (mem_univ b) (mem_univ a)
  simpa [Real.norm_eq_abs] using this

/-- Second-order Taylor bound for `θ`. -/
lemma theta_taylor (t : ℝ) {τ : ℝ} (hτ : 0 ≤ τ) :
    |theta (t + τ) - theta t - τ * theta' t| ≤ π ^ 2 / 2 * τ ^ 2 := by
  have hG : ∀ s ∈ Icc (0 : ℝ) τ, HasDerivWithinAt (fun s => theta (t + s) - theta t - s * theta' t)
      (theta' (t + s) - theta' t) (Icc (0 : ℝ) τ) s := by
    intro s _
    have h1 : HasDerivAt (fun s : ℝ => t + s) 1 s := by simpa using (hasDerivAt_id s).const_add t
    have h2 := (hasDerivAt_theta (t + s)).comp s h1
    have h3 : HasDerivAt (fun s : ℝ => s * theta' t) (theta' t) s := by
      simpa using (hasDerivAt_id s).mul_const (theta' t)
    have h4 := (h2.sub_const (theta t)).sub h3
    exact (h4.congr_deriv (by ring)).hasDerivWithinAt
  have := (convex_Icc (0 : ℝ) τ).norm_image_sub_le_of_norm_hasDerivWithin_le hG
    (C := π ^ 2 / 2 * τ) (fun s hs => by
      rw [Real.norm_eq_abs]
      have := theta'_lip (t + s) t
      simp only [add_sub_cancel_left] at this
      rw [abs_of_nonneg hs.1] at this
      refine this.trans ?_
      exact mul_le_mul_of_nonneg_left hs.2 (by positivity))
    (left_mem_Icc.2 hτ) (right_mem_Icc.2 hτ)
  simp only [add_zero, zero_mul, sub_zero, sub_self, Real.norm_eq_abs] at this
  calc _ ≤ π ^ 2 / 2 * τ * |τ| := by simpa using this
    _ = _ := by rw [abs_of_nonneg hτ]; ring

variable (D : PeyreData d)

lemma isCk_u : Torus.IsCk 2 D.u := D.contDiff_lift_u

/-- Integration by parts: `∫ DΦ[∇u] = ∫ Φ (f - g)` (since `Δu = g - f`). -/
lemma ibp {Φ : Euc d → ℝ} (hp : Torus.Per Φ) (hΦ : ContDiff ℝ 2 Φ) :
    ∫ x : Torus d, fderiv ℝ Φ (Torus.rep x) (D.gradU (Torus.rep x)) =
      ∫ x : Torus d, Φ (Torus.rep x) * (D.f x - D.g x) := by
  set φ : Torus d → ℝ := Torus.descend Φ with hφdef
  have hlift : Torus.lift φ = Φ := Torus.lift_descend' hp
  have hφ : Torus.IsCk 1 φ := by
    unfold Torus.IsCk; rw [hlift]; exact hΦ.of_le (by norm_num)
  have hu2 := D.isCk_u
  have hcont : ∀ j : Fin d, Continuous fun x : Torus d =>
      Torus.partialDeriv j φ x * Torus.partialDeriv j D.u x := fun j =>
    (PDE.continuous_partialDeriv j φ hφ).mul
      (PDE.continuous_partialDeriv j D.u (hu2.of_le (by norm_num)))
  have hpt : ∀ x : Torus d, fderiv ℝ Φ (Torus.rep x) (D.gradU (Torus.rep x)) =
      ∑ j : Fin d, Torus.partialDeriv j φ x * Torus.partialDeriv j D.u x := by
    intro x
    unfold PeyreData.gradU
    rw [q12_clm_gradient_eq]
    refine Finset.sum_congr rfl fun j _ => ?_
    have e1 : Torus.partialDeriv j φ x = fderiv ℝ Φ (Torus.rep x) (EuclideanSpace.single j 1) := by
      unfold Torus.partialDeriv; rw [hlift]
    rw [e1]; rfl
  simp_rw [hpt]
  rw [integral_finset_sum _ fun j _ =>
    (hcont j).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)]
  have hibp : ∀ j : Fin d, ∫ x : Torus d, Torus.partialDeriv j φ x * Torus.partialDeriv j D.u x =
      -∫ x : Torus d, φ x * Torus.partialDeriv j (Torus.partialDeriv j D.u) x := fun j =>
    PDE.integral_partialDeriv_mul j φ (Torus.partialDeriv j D.u) hφ
      (PDE.isCk_one_partialDeriv j D.u hu2)
  simp_rw [hibp]
  rw [Finset.sum_neg_distrib]
  have hφc : Continuous φ := Torus.continuous_descend hp hΦ.continuous
  have hc2 : ∀ j : Fin d, Continuous fun x : Torus d =>
      φ x * Torus.partialDeriv j (Torus.partialDeriv j D.u) x := fun j =>
    hφc.mul (PDE.continuous_partialDeriv j _ (PDE.isCk_one_partialDeriv j D.u hu2))
  rw [← integral_finset_sum _ fun j _ =>
    (hc2 j).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)]
  rw [← integral_neg]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show -∑ j : Fin d, φ x * Torus.partialDeriv j (Torus.partialDeriv j D.u) x = φ x * (D.f x - D.g x)
  rw [← Finset.mul_sum, ← PDE.laplacian_eq_sum D.u hu2 x, D.hΔ x]
  ring

end PeyreData

end HRS.Uniform.Q12
