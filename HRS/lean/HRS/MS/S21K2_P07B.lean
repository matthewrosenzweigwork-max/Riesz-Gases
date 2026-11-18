import HRS.MS.S21G2_M16

/-!
# S21K2 P07B -- third-order Taylor estimate, coordinate expansions, convolution integral (R26-T3.P07)

`|Phi(z+w) - Phi z - D Phi(z) w - 1/2 D^2 Phi(z)[w,w]| <= C |w|^3` for `Phi in C^3` with `|D^3 Phi| <= C` (iterated mean value
inequality along the segment), the Lipschitz bound of `D^2 Phi`, and `int f d(nu * kappa) = int int f(g+w) dkappa dnu`.
Helper prefix `s21k2_p07_`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open scoped ENNReal NNReal BigOperators
noncomputable section
namespace HRS.MS.R26T3

section Taylor
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem s21k2_p07_lip2 {Φ : E → ℝ} (hΦ : ContDiff ℝ 3 Φ) {C : ℝ}
    (hC : ∀ z, ‖iteratedFDeriv ℝ 3 Φ z‖ ≤ C) (z w : E) :
    ‖iteratedFDeriv ℝ 2 Φ (z + w) - iteratedFDeriv ℝ 2 Φ z‖ ≤ C * ‖w‖ := by
  have hd : Differentiable ℝ (iteratedFDeriv ℝ 2 Φ) :=
    hΦ.differentiable_iteratedFDeriv (m := 2) (by exact_mod_cast (by norm_num : (2 : ℕ) < 3))
  have := (convex_univ : Convex ℝ (Set.univ : Set E)).norm_image_sub_le_of_norm_fderiv_le
    (f := iteratedFDeriv ℝ 2 Φ) (C := C) (fun x _ => hd x)
    (fun x _ => by rw [norm_fderiv_iteratedFDeriv]; exact hC x) (Set.mem_univ z) (Set.mem_univ (z + w))
  simpa using this

theorem s21k2_p07_eval2 {M : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ} (w : E) :
    |M ![w, w]| ≤ ‖M‖ * ‖w‖ ^ 2 := by
  have := M.le_opNorm ![w, w]
  simpa [Fin.prod_univ_two, sq] using this

theorem s21k2_p07_taylor {Φ : E → ℝ} (hΦ : ContDiff ℝ 3 Φ) {C : ℝ}
    (hC : ∀ z, ‖iteratedFDeriv ℝ 3 Φ z‖ ≤ C) (z w : E) :
    |Φ (z + w) - Φ z - fderiv ℝ Φ z w - (1 / 2) * iteratedFDeriv ℝ 2 Φ z ![w, w]| ≤ C * ‖w‖ ^ 3 := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC z)
  have hd1 : Differentiable ℝ Φ := hΦ.differentiable (by norm_num)
  have hd2 : Differentiable ℝ (fderiv ℝ Φ) := by
    have h := hΦ.fderiv_right (m := 2) (by norm_num)
    exact h.differentiable (by norm_num)
  set a2 : ℝ → ℝ := fun θ => iteratedFDeriv ℝ 2 Φ (z + θ • w) ![w, w] with ha2
  set a1 : ℝ → ℝ := fun θ => fderiv ℝ Φ (z + θ • w) w with ha1
  set φ : ℝ → ℝ := fun θ => Φ (z + θ • w) with hφ
  have hline : ∀ θ : ℝ, HasDerivAt (fun θ : ℝ => z + θ • w) w θ := fun θ => by
    simpa using ((hasDerivAt_id θ).smul_const w).const_add z
  have hφd : ∀ θ, HasDerivAt φ (a1 θ) θ := fun θ =>
    (hd1 (z + θ • w)).hasFDerivAt.comp_hasDerivAt θ (hline θ)
  have ha1d : ∀ θ, HasDerivAt a1 (a2 θ) θ := fun θ => by
    have h1 : HasDerivAt (fun θ : ℝ => fderiv ℝ Φ (z + θ • w)) (fderiv ℝ (fderiv ℝ Φ) (z + θ • w) w) θ :=
      (hd2 (z + θ • w)).hasFDerivAt.comp_hasDerivAt θ (hline θ)
    have := h1.clm_apply (hasDerivAt_const θ w)
    simpa [ha2, iteratedFDeriv_two_apply] using this
  have ha2b : ∀ θ ∈ Set.Icc (0 : ℝ) 1, |a2 θ - a2 0| ≤ C * ‖w‖ ^ 3 * θ := fun θ hθ => by
    have h := s21k2_p07_lip2 hΦ hC z (θ • w)
    have h2 := s21k2_p07_eval2 (M := iteratedFDeriv ℝ 2 Φ (z + θ • w) - iteratedFDeriv ℝ 2 Φ z) w
    have e : a2 θ - a2 0 = (iteratedFDeriv ℝ 2 Φ (z + θ • w) - iteratedFDeriv ℝ 2 Φ z) ![w, w] := by
      simp [ha2]
    rw [e]
    refine h2.trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ.1] at h
    calc _ ≤ (C * (θ * ‖w‖)) * ‖w‖ ^ 2 := mul_le_mul_of_nonneg_right h (by positivity)
      _ = _ := by ring
  set ψ1 : ℝ → ℝ := fun θ => a1 θ - a1 0 - θ * a2 0 with hψ1
  have hψ1d : ∀ θ, HasDerivAt ψ1 (a2 θ - a2 0) θ := fun θ => by
    have h := ((ha1d θ).sub_const (a1 0)).sub ((hasDerivAt_id θ).mul_const (a2 0))
    exact h.congr_deriv (by simp)
  have hstep1 : ∀ θ ∈ Set.Icc (0 : ℝ) 1, |ψ1 θ| ≤ C * ‖w‖ ^ 3 * θ ^ 2 := fun θ hθ => by
    have := (convex_Icc (0 : ℝ) θ).norm_image_sub_le_of_norm_deriv_le (f := ψ1)
      (C := C * ‖w‖ ^ 3 * θ) (x := 0) (y := θ) (fun t _ => (hψ1d t).differentiableAt)
      (fun t ht => by
        rw [(hψ1d t).deriv, Real.norm_eq_abs]
        refine (ha2b t ⟨ht.1, ht.2.trans hθ.2⟩).trans ?_
        exact mul_le_mul_of_nonneg_left ht.2 (by positivity))
      (Set.left_mem_Icc.2 hθ.1) (Set.right_mem_Icc.2 hθ.1)
    simp only [hψ1, zero_mul, sub_self, sub_zero, Real.norm_eq_abs, abs_of_nonneg hθ.1] at this
    calc |ψ1 θ| ≤ _ := by simpa [hψ1] using this
      _ = _ := by ring
  set ψ : ℝ → ℝ := fun θ => φ θ - φ 0 - θ * a1 0 - θ ^ 2 / 2 * a2 0 with hψ
  have hψd : ∀ θ, HasDerivAt ψ (ψ1 θ) θ := fun θ => by
    have h1 := (((hφd θ).sub_const (φ 0)).sub ((hasDerivAt_id θ).mul_const (a1 0))).sub
      (((hasDerivAt_pow 2 θ).div_const 2).mul_const (a2 0))
    exact h1.congr_deriv (by simp [hψ1])
  have := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le (f := ψ) (C := C * ‖w‖ ^ 3)
    (x := 0) (y := 1) (fun t _ => (hψd t).differentiableAt)
    (fun t ht => by
      rw [(hψd t).deriv, Real.norm_eq_abs]
      refine (hstep1 t ht).trans ?_
      have : t ^ 2 ≤ 1 := pow_le_one₀ ht.1 ht.2
      exact (mul_le_mul_of_nonneg_left this (by positivity)).trans (le_of_eq (mul_one _)))
    (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one)
  simp only [hψ, hφ, ha1, ha2] at this
  simpa [Real.norm_eq_abs] using this

end Taylor

theorem s21k2_p07_conv_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] (ν κ : Measure E)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure κ] {f : E → ℝ} (hf : Continuous f) {B : ℝ}
    (hB : ∀ x, ‖f x‖ ≤ B) :
    ∫ x, f x ∂(ν ∗ κ) = ∫ g, ∫ w, f (g + w) ∂κ ∂ν := by
  have hm : Measurable (fun p : E × E => p.1 + p.2) := measurable_add
  unfold Measure.conv
  rw [integral_map hm.aemeasurable hf.aestronglyMeasurable, integral_prod]
  refine Integrable.of_bound (C := B) ((hf.comp continuous_add).aestronglyMeasurable) ?_
  exact Eventually.of_forall fun p => hB _

theorem s21k2_p07_expand1 {n : ℕ} (L : HRS.Euc n →L[ℝ] ℝ) (w : HRS.Euc n) :
    L w = ∑ i, w.ofLp i * L (EuclideanSpace.single i 1) := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr w]
  simp [map_sum, EuclideanSpace.basisFun_apply]

theorem s21k2_p07_expand2 {n : ℕ} (B : HRS.Euc n →L[ℝ] HRS.Euc n →L[ℝ] ℝ) (w : HRS.Euc n) :
    B w w = ∑ i, ∑ j, w.ofLp i * w.ofLp j * B (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
  rw [s21k2_p07_expand1 (B w) w]
  have h : ∀ j, B w (EuclideanSpace.single j 1) =
      ∑ i, w.ofLp i * B (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := fun j => by
    have := s21k2_p07_expand1 (B.flip (EuclideanSpace.single j 1)) w
    simpa using this
  simp_rw [h, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring


end HRS.MS.R26T3
