import HRS.MS.QsfAsm2

/-!
# S4.5 packet B5 (assembly), part 3: the vector Stein identity (statement and proof)
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace ContDiff

noncomputable section

namespace S45

open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d N : ℕ}

theorem s45_gradient_continuous {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 1 ψ) : Continuous (gradient ψ) := by
  unfold gradient
  exact (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp (hψ.continuous_fderiv one_ne_zero)

theorem s45_fderiv_F_eq (hN : 1 ≤ N) {n : ℕ} {φ : ℕ → Euc d → ℝ} (hφ : ∀ i, Differentiable ℝ (φ i))
    (c : ℕ → ℝ) {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Differentiable ℝ f) {χ : Euc d → ℝ}
    (X : EucConfig d N) :
    fderiv ℝ (fun X => f (s45_Yv n N φ c X)) X (fun k => gradient χ (X k)) =
      ∑ j : Fin n, (Real.sqrt N * pair (empirical X) (fun x => ⟪gradient χ x, gradient (φ j) x⟫)) *
        fderiv ℝ f (s45_Yv n N φ c X) (EuclideanSpace.single j 1) := by
  have hN' : 0 < N := hN
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  rw [s45_F_fderiv hN hφ c hf]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [s45_L_apply, pair_empirical hN']
  simp_rw [s45_fderiv_eq_inner (φ j), real_inner_comm (gradient χ _)]
  field_simp

theorem s45_vec_stein (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β C c BU Cs : ℝ}
    (ha : 0 < a) (hβ : 0 < β) (hN : 2 ≤ N) (hT : ThermalData d s a β C c BU)
    (hS : S45Static d s a β Cs N) {n : ℕ} {φ χ : ℕ → Euc d → ℝ} {B Bφ Dφ : ℕ → ℝ}
    (hφ1 : ∀ i, ContDiff ℝ 1 (φ i)) (hφb : ∀ i x, |φ i x| ≤ Bφ i)
    (hφD : ∀ i x, ‖fderiv ℝ (φ i) x‖ ≤ Dφ i)
    (hfeat : ∀ i, S45Feat d s a β (φ i) (χ i) (B i))
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ ∞ f) {Cf Cf' : ℝ} (hCf : ∀ x, |f x| ≤ Cf)
    (hCf' : ∀ x, ‖fderiv ℝ f x‖ ≤ Cf') (i : Fin n) :
    ∫ X, s45_Yi N (φ i) (pair (s45_nu d s a β N) (φ i)) X *
        f (s45_Yv n N φ (fun j => pair (s45_nu d s a β N) (φ j)) X) ∂(s45_P d s a β N) =
      ∫ X, (Real.sqrt N * s45_Rp (thermalMeasure d s a β) (s45_nu d s a β N) (s45_P d s a β N)
          (commutatorKernel d s (gradient (χ i))) X) *
          f (s45_Yv n N φ (fun j => pair (s45_nu d s a β N) (φ j)) X) ∂(s45_P d s a β N) +
      ∑ j : Fin n, ∫ X, (β⁻¹ * pair (empirical X) (fun x => ⟪gradient (χ i) x, gradient (φ j) x⟫)) *
          fderiv ℝ f (s45_Yv n N φ (fun j => pair (s45_nu d s a β N) (φ j)) X)
            (EuclideanSpace.single j 1) ∂(s45_P d s a β N) := by
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  haveI : IsProbabilityMeasure (s45_P d s a β N) := hS.prob
  set P := s45_P d s a β N with hP
  set ν := s45_nu d s a β N with hν
  set c' : ℕ → ℝ := fun j => pair ν (φ j) with hc'
  set Y := s45_Yv n N φ c' with hY
  set F : EucConfig d N → ℝ := fun X => f (Y X) with hFdef
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by exact_mod_cast le_top)
  have hfd : Differentiable ℝ f := hf1.differentiable one_ne_zero
  have hφd : ∀ j, Differentiable ℝ (φ j) := fun j => (hφ1 j).differentiable one_ne_zero
  have hF : ContDiff ℝ 1 F := s45_F_contDiff hN1 hφ1 c' hf
  have hBF : ∀ X, |F X| ≤ Cf := fun X => hCf _
  have hDF : ∀ X, ‖fderiv ℝ F X‖ ≤ ∑ j : Fin n, Real.sqrt N * Dφ j * Cf' := fun X =>
    s45_F_fderiv_bound hN1 hφd c' hφD hfd hCf' X
  obtain ⟨c0, hstar⟩ := s45_star hd hs0 hsd hβ hT (hfeat i).smooth (hfeat i).B1 (hfeat i).B2 (hfeat i).corr
  have hid : ∫ X, (pair (empirical X) (φ i) - pair ν (φ i)) * F X ∂P =
      ∫ X, s45_Rp (thermalMeasure d s a β) ν P (commutatorKernel d s (gradient (χ i))) X * F X ∂P +
        (β * N)⁻¹ * ∫ X, fderiv ℝ F X (fun k => gradient (χ i) (X k)) ∂P :=
    s45_stein_id hd hs0 hsd ha hβ hN hT hS (hfeat i).smooth (hfeat i).B1 (hfeat i).B2
      (hφ1 i).continuous.measurable (hφb i) hstar hF hBF hDF
  -- the derivative term
  have hder : ∀ X, fderiv ℝ F X (fun k => gradient (χ i) (X k)) =
      ∑ j : Fin n, (Real.sqrt N * pair (empirical X) (fun x => ⟪gradient (χ i) x, gradient (φ j) x⟫)) *
        fderiv ℝ f (Y X) (EuclideanSpace.single j 1) := fun X =>
    s45_fderiv_F_eq hN1 hφd c' hfd X
  -- integrability of the `T`-terms
  have hYc : Continuous Y := (s45_Yv_contDiff hN1 hφ1 c').continuous
  have hχ1 : ContDiff ℝ 1 (gradient (χ i)) := s45_contDiff_gradient (hfeat i).smooth
  have hfc : ∀ j : Fin n, Continuous fun x : Euc d => ⟪gradient (χ i) x, gradient (φ j) x⟫ := fun j =>
    hχ1.continuous.inner (s45_gradient_continuous (hφ1 j))
  have hcj : ∀ j : Fin n, Continuous fun X : EucConfig d N =>
      fderiv ℝ f (Y X) (EuclideanSpace.single j 1) := fun j =>
    ((hf.continuous_fderiv (by simp)).comp hYc).clm_apply continuous_const
  have hcjb : ∀ (j : Fin n) X, |fderiv ℝ f (Y X) (EuclideanSpace.single j 1)| ≤ Cf' := by
    intro j X
    rw [← Real.norm_eq_abs]
    refine ((fderiv ℝ f _).le_opNorm _).trans ?_
    simpa using mul_le_mul_of_nonneg_right (hCf' (Y X))
      (by simp : (0 : ℝ) ≤ ‖(EuclideanSpace.single j (1 : ℝ) : EuclideanSpace ℝ (Fin n))‖)
  have hfb : ∀ (j : Fin n) x, |⟪gradient (χ i) x, gradient (φ j) x⟫| ≤ B i * Dφ j := by
    intro j x
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [s45_norm_gradient, s45_norm_gradient (φ j)]
    have h1 : ‖fderiv ℝ (χ i) x‖ ≤ B i := by
      rw [← s45_norm_gradient]; exact (hfeat i).B1 x
    exact mul_le_mul (by simpa using h1) (hφD j x) (norm_nonneg _) ((norm_nonneg _).trans h1)
  have hTint : ∀ j : Fin n, Integrable (fun X : EucConfig d N =>
      (β⁻¹ * pair (empirical X) (fun x => ⟪gradient (χ i) x, gradient (φ j) x⟫)) *
        fderiv ℝ f (Y X) (EuclideanSpace.single j 1)) P := by
    intro j
    refine Integrable.of_bound (C := β⁻¹ * (B i * Dφ j) * Cf')
      (((measurable_const.mul (s45_measurable_pair_empirical hN1 (hfc j).measurable)).mul
        (hcj j).measurable).aestronglyMeasurable) (Filter.Eventually.of_forall fun X => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (inv_pos.2 hβ)]
    have h1 := s45_abs_pair_empirical_le hN1 (hfb j) X
    have hB0 : 0 ≤ B i * Dφ j := (abs_nonneg _).trans (hfb j 0)
    exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hβ.le)) (hcjb j X) (abs_nonneg _)
      (by positivity)
  -- assembling
  have hsq : Real.sqrt N ^ 2 = N := Real.sq_sqrt hN0.le
  have eA : ∫ X, s45_Yi N (φ i) (pair ν (φ i)) X * f (Y X) ∂P =
      Real.sqrt N * ∫ X, (pair (empirical X) (φ i) - pair ν (φ i)) * F X ∂P := by
    rw [← integral_const_mul]
    congr 1; funext X
    simp only [s45_Yi, hFdef]; ring
  have eB : ∫ X, (Real.sqrt N * s45_Rp (thermalMeasure d s a β) ν P
      (commutatorKernel d s (gradient (χ i))) X) * f (Y X) ∂P =
      Real.sqrt N * ∫ X, s45_Rp (thermalMeasure d s a β) ν P
        (commutatorKernel d s (gradient (χ i))) X * F X ∂P := by
    rw [← integral_const_mul]
    congr 1; funext X
    simp only [hFdef]; ring
  have eD : ∑ j : Fin n, ∫ X, (β⁻¹ * pair (empirical X) (fun x => ⟪gradient (χ i) x, gradient (φ j) x⟫)) *
      fderiv ℝ f (Y X) (EuclideanSpace.single j 1) ∂P =
      Real.sqrt N * ((β * N)⁻¹ * ∫ X, fderiv ℝ F X (fun k => gradient (χ i) (X k)) ∂P) := by
    rw [← integral_finsetSum _ fun j _ => hTint j, ← integral_const_mul, ← integral_const_mul]
    congr 1; funext X
    rw [hder X, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    set p := pair (empirical X) (fun x => ⟪gradient (χ i) x, gradient (φ j) x⟫)
    set q := fderiv ℝ f (Y X) (EuclideanSpace.single j 1)
    calc β⁻¹ * p * q = Real.sqrt N * ((β * N)⁻¹ * ((Real.sqrt N * p) * q)) := by
          have : Real.sqrt N * ((β * N)⁻¹ * ((Real.sqrt N * p) * q)) =
              (Real.sqrt N ^ 2) * (β * N)⁻¹ * p * q := by ring
          rw [this, hsq]; field_simp
      _ = _ := rfl
  rw [eA, eB, eD, hid, mul_add]

end S45

end
