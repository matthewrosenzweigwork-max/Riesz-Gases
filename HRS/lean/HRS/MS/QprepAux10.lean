import HRS.MS.QprepAux9

/-!
# S4.6 packet A10: the vector Stein identity and the integrability of the Stein remainder for `Q_{N,γ₀}`
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

noncomputable section

namespace S46

open S45
open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d N : ℕ}

theorem s46_Rp_integrable (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β γ C c BU Cs : ℝ}
    (hT : ThermalData d s a β C c BU) (hN : 2 ≤ N) (hS : S46Static d s a β γ Cs N) {χ : Euc d → ℝ}
    (hχ : ContDiff ℝ 2 χ) {B2 : ℝ} (hB2 : ∀ x, ‖fderiv ℝ (gradient χ) x‖ ≤ B2) :
    Integrable (s45_Rp (thermalMeasure d s a β) (s46_nu d s a β γ N) (s46_P d s a β γ N)
      (commutatorKernel d s (gradient χ))) (s46_P d s a β γ N) := by
  have hN1 : 1 ≤ N := by omega
  haveI hP : IsProbabilityMeasure (s46_P d s a β γ N) := hS.prob
  set P := s46_P d s a β γ N with hPdef
  set μ := thermalMeasure d s a β with hμdef
  set v := gradient χ with hvdef
  set h := commutatorKernel d s v with hhdef
  set ν := s46_nu d s a β γ N with hνdef
  haveI hνprob : IsProbabilityMeasure ν := by
    have : ν = P.map (fun X : EucConfig d N => X ⟨0, by omega⟩) := by
      rw [hνdef]; unfold s46_nu firstMarginal; rw [dif_pos (by omega)]
    rw [this]
    constructor
    rw [Measure.map_apply (measurable_pi_apply _) MeasurableSet.univ]
    simp
  haveI hμprob : IsProbabilityMeasure μ := HRS.Whole.Q34.isProbabilityMeasure_nu hT.prob
  have hv1 : ContDiff ℝ 1 v := s45_contDiff_gradient hχ
  have hvd : Differentiable ℝ v := hv1.differentiable one_ne_zero
  have hB20 : 0 ≤ B2 := (norm_nonneg _).trans (hB2 0)
  set Λ : ℝ≥0 := ⟨B2, hB20⟩ with hΛdef
  have hLip : LipschitzWith Λ v := lipschitzWith_of_nnnorm_fderiv_le hvd (fun x => by
    have := hB2 x
    rw [← NNReal.coe_le_coe, coe_nnnorm]; exact this)
  have hhm : Measurable (Function.uncurry h) :=
    HRS.MS.Comm.comm_meas (s := s) v hv1.continuous.measurable
  obtain ⟨φN, hφNm, hνeq, hφNb, hφN2, hφNn⟩ := hS.marg
  obtain ⟨Bh, hBh0, hBh⟩ := s45_Hbounds hd hs0 hsd hT hLip hφNb hφNm ν hνeq
  have hHd_meas : Measurable fun x => (∫ y, h x y ∂μ) - ∫ y, h x y ∂ν :=
    ((hhm.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable).sub
      (hhm.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable
  have hHd_bd : ∀ x, |(∫ y, h x y ∂μ) - ∫ y, h x y ∂ν| ≤ 2 * Bh := fun x => by
    obtain ⟨h1, h2⟩ := hBh x
    calc _ ≤ |∫ y, h x y ∂μ| + |∫ y, h x y ∂ν| := abs_sub _ _
      _ ≤ 2 * Bh := by linarith
  have hDm : Measurable fun X : EucConfig d N => centeredPairFunctional h X ν :=
    HRS.MS.Wr.wr14a_measurable_D hhm ν
  obtain ⟨-, hq⟩ := hS.comm Λ v hLip
  have hDi : Integrable (fun X : EucConfig d N => centeredPairFunctional h X ν) P := by
    have hlt : evariance (fun X : EucConfig d N => centeredPairFunctional h X ν) P < ⊤ :=
      lt_of_le_of_lt hq.2.2 ENNReal.ofReal_lt_top
    exact ((evariance_lt_top_iff_memLp hDm.aestronglyMeasurable).1 hlt).integrable one_le_two
  have hYi : Integrable (fun X : EucConfig d N => pair (empirical X) (fun x => (∫ y, h x y ∂μ) -
      ∫ y, h x y ∂ν)) P :=
    Integrable.of_bound (s45_measurable_pair_empirical hN1 hHd_meas).aestronglyMeasurable (2 * Bh)
      (Filter.Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs]; exact s45_abs_pair_empirical_le hN1 hHd_bd X)
  unfold s45_Rp
  exact (hYi.sub (integrable_const _)).sub ((hDi.sub (integrable_const _)).const_mul _)


theorem s46_vec_stein (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β γ C c BU Cs : ℝ}
    (ha : 0 < a) (hβ : 0 < β) (hγ : 0 < γ) (hN : 2 ≤ N) (hT : ThermalData d s a β C c BU)
    (hS : S46Static d s a β γ Cs N) {n : ℕ} {φ χ : ℕ → Euc d → ℝ} {B Bφ Dφ : ℕ → ℝ}
    (hφ1 : ∀ i, ContDiff ℝ 1 (φ i)) (hφb : ∀ i x, |φ i x| ≤ Bφ i)
    (hφD : ∀ i x, ‖fderiv ℝ (φ i) x‖ ≤ Dφ i)
    (hfeat : ∀ i, S46Feat d s a β γ (φ i) (χ i) (B i))
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ ∞ f) {Cf Cf' : ℝ} (hCf : ∀ x, |f x| ≤ Cf)
    (hCf' : ∀ x, ‖fderiv ℝ f x‖ ≤ Cf') (i : Fin n) :
    ∫ X, s45_Yi N (φ i) (pair (s46_nu d s a β γ N) (φ i)) X *
        f (s45_Yv n N φ (fun j => pair (s46_nu d s a β γ N) (φ j)) X) ∂(s46_P d s a β γ N) =
      ∫ X, (Real.sqrt N * s45_Rp (thermalMeasure d s a β) (s46_nu d s a β γ N) (s46_P d s a β γ N)
          (commutatorKernel d s (gradient (χ i))) X) *
          f (s45_Yv n N φ (fun j => pair (s46_nu d s a β γ N) (φ j)) X) ∂(s46_P d s a β γ N) +
      ∑ j : Fin n, ∫ X, (γ⁻¹ * pair (empirical X) (fun x => ⟪gradient (χ i) x, gradient (φ j) x⟫)) *
          fderiv ℝ f (s45_Yv n N φ (fun j => pair (s46_nu d s a β γ N) (φ j)) X)
            (EuclideanSpace.single j 1) ∂(s46_P d s a β γ N) := by
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  haveI : IsProbabilityMeasure (s46_P d s a β γ N) := hS.prob
  set P := s46_P d s a β γ N with hP
  set ν := s46_nu d s a β γ N with hν
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
  obtain ⟨c0, hstar⟩ := s46_star hd hs0 hsd hγ hT (hfeat i).smooth (hfeat i).B1 (hfeat i).B2 (hfeat i).corr
  have hid : ∫ X, (pair (empirical X) (φ i) - pair ν (φ i)) * F X ∂P =
      ∫ X, s45_Rp (thermalMeasure d s a β) ν P (commutatorKernel d s (gradient (χ i))) X * F X ∂P +
        (γ * N)⁻¹ * ∫ X, fderiv ℝ F X (fun k => gradient (χ i) (X k)) ∂P :=
    s46_stein_id hd hs0 hsd ha hβ hγ hN hT hS (hfeat i).smooth (hfeat i).B1 (hfeat i).B2
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
      (γ⁻¹ * pair (empirical X) (fun x => ⟪gradient (χ i) x, gradient (φ j) x⟫)) *
        fderiv ℝ f (Y X) (EuclideanSpace.single j 1)) P := by
    intro j
    refine Integrable.of_bound (C := γ⁻¹ * (B i * Dφ j) * Cf')
      (((measurable_const.mul (s45_measurable_pair_empirical hN1 (hfc j).measurable)).mul
        (hcj j).measurable).aestronglyMeasurable) (Filter.Eventually.of_forall fun X => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (inv_pos.2 hγ)]
    have h1 := s45_abs_pair_empirical_le hN1 (hfb j) X
    have hB0 : 0 ≤ B i * Dφ j := (abs_nonneg _).trans (hfb j 0)
    exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hγ.le)) (hcjb j X) (abs_nonneg _)
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
  have eD : ∑ j : Fin n, ∫ X, (γ⁻¹ * pair (empirical X) (fun x => ⟪gradient (χ i) x, gradient (φ j) x⟫)) *
      fderiv ℝ f (Y X) (EuclideanSpace.single j 1) ∂P =
      Real.sqrt N * ((γ * N)⁻¹ * ∫ X, fderiv ℝ F X (fun k => gradient (χ i) (X k)) ∂P) := by
    rw [← integral_finsetSum _ fun j _ => hTint j, ← integral_const_mul, ← integral_const_mul]
    congr 1; funext X
    rw [hder X, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    set p := pair (empirical X) (fun x => ⟪gradient (χ i) x, gradient (φ j) x⟫)
    set q := fderiv ℝ f (Y X) (EuclideanSpace.single j 1)
    calc γ⁻¹ * p * q = Real.sqrt N * ((γ * N)⁻¹ * ((Real.sqrt N * p) * q)) := by
          have : Real.sqrt N * ((γ * N)⁻¹ * ((Real.sqrt N * p) * q)) =
              (Real.sqrt N ^ 2) * (γ * N)⁻¹ * p * q := by ring
          rw [this, hsq]; field_simp
      _ = _ := rfl
  rw [eA, eB, eD, hid, mul_add]


end S46

end
