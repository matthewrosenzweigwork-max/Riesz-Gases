import HRS.MS.Fp81S21GaussianFeatureBound2
import HRS.MS.Fp81S21FutureIndep11
import HRS.MS.Fp81S21GaussianPropagatedSourceBridge
import HRS.MS.ProClosureS111ChartSections

/-! Literal feature subtraction and convergence for propagated chart sections. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6
open HRS.MS.S111X2 HRS.MS.ProClosureS111

private theorem fp81s21_feature_classical_sub
    (p : Parameters) {δ r : ℝ} (R : Trajectory p δ)
    {f g : Euc p.d → ℝ} {u v : ℝ → Euc p.d → ℝ}
    (hu : IsClassicalAdjointW (r26t3_coeff R) r f u)
    (hv : IsClassicalAdjointW (r26t3_coeff R) r g v) :
    IsClassicalAdjointW (r26t3_coeff R) r (f - g) (fun s => u s - v s) := by
  have hsd : p.s < (p.d : ℝ) := by linarith [p.hs, Nat.cast_nonneg (α := ℝ) p.d]
  obtain ⟨c, K, hc, hK0, hρ⟩ := HRS.MS.S104e.s104e_gauss_rho
    p.hd p.hs0 hsd p.ha p.hβ δ p.c₁ p.C₁ 1 (by omega)
    R.thermal R.resulting
  obtain ⟨P, _, hU⟩ := HRS.MS.S104e.s104e_u2dec_of_gauss
    (d := p.d) hc 1 (p.d + 1)
  have hA : ∀ s ∈ Icc (0 : ℝ) r,
      U2Dec 1 ((p.d + 1 : ℕ) : ℝ) (P * K) (R.ρ s) := by
    intro s hs
    obtain ⟨hreg, hbnd⟩ := hρ s hs.1
    exact hU (R.ρ s) K hK0 hreg (fun k hk x => hbnd k hk x)
  have hlin := HRS.MS.R2WinOrbNL.s103c_lincomb p.hd p.hs0 hsd
    (show (p.d : ℝ) < ((p.d + 1 : ℕ) : ℝ) by exact_mod_cast Nat.lt_succ_self p.d)
    R.ρ hA 1 (-1) hu hv
  have ef : (fun x => (1 : ℝ) * f x + (-1 : ℝ) * g x) = f - g := by
    funext x
    simp only [Pi.sub_apply, one_mul, neg_one_mul, sub_eq_add_neg]
  have euv : (fun s x => (1 : ℝ) * u s x + (-1 : ℝ) * v s x) =
      (fun s => u s - v s) := by
    funext s x
    simp only [Pi.sub_apply, one_mul, neg_one_mul, sub_eq_add_neg]
  rw [ef, euv] at hlin
  exact hlin

/-- Subtraction holds for supplied classical adjoints, including chart errors. -/
theorem fp81s21_combinedFeature_classical_sub
    (p : Parameters) {δ r : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2) (hr : 0 ≤ r)
    [IsProbabilityMeasure (r26t3_mu R 0)]
    {Mg : ℝ} {K : Lp ℝ 2 (r26t3_mu R 0) →L[ℝ] Lp ℝ 2 (r26t3_mu R 0)}
    (hK : KRep (rieszKernel p.d p.s) (r26t3_mu R 0) K Mg)
    {f g : Euc p.d → ℝ} {u v : ℝ → Euc p.d → ℝ}
    (hu : IsClassicalAdjointW (r26t3_coeff R) r f u)
    (hv : IsClassicalAdjointW (r26t3_coeff R) r g v) :
    fp81s21_combinedFeature p R hK r f - fp81s21_combinedFeature p R hK r g =
      fp81s21_combinedFeature p R hK r (f - g) := by
  have hd := fp81s21_feature_classical_sub p R hu hv
  have eu := fp81s21_feature_classical_eq p R hr hu
  have ev := fp81s21_feature_classical_eq p R hr hv
  have ed := fp81s21_feature_classical_eq p R hr hd
  have hmu := HRS.MS.S111X1.x1_classical_memLp hu ⟨le_rfl, hr⟩ (r26t3_mu R 0)
  have hmv := HRS.MS.S111X1.x1_classical_memLp hv ⟨le_rfl, hr⟩ (r26t3_mu R 0)
  have hlp : s111x2_toLp (r26t3_mu R 0) (u 0 - v 0) =
      s111x2_toLp (r26t3_mu R 0) (u 0) - s111x2_toLp (r26t3_mu R 0) (v 0) := by
    apply Lp.ext
    filter_upwards [s111x2_toLp_ae (hmu.sub hmv), s111x2_toLp_ae hmu,
      s111x2_toLp_ae hmv, Lp.coeFn_sub (s111x2_toLp (r26t3_mu R 0) (u 0))
        (s111x2_toLp (r26t3_mu R 0) (v 0))] with x hd hu hv hs
    rw [hd, hs]
    simp only [Pi.sub_apply]
    rw [hu, hv]
  have hi : fp81s21_initialGaussianFeature p R hK r (f - g) =
      fp81s21_initialGaussianFeature p R hK r f -
        fp81s21_initialGaussianFeature p R hK r g := by
    simp only [fp81s21_initialGaussianFeature, initialGaussianFeature,
      ed 0 ⟨le_rfl, hr⟩, eu 0 ⟨le_rfl, hr⟩, ev 0 ⟨le_rfl, hr⟩,
      hlp, map_sub]
  have hnu := (fp81s21_feature_classical_noise p R hδ hδh hr hu).1
  have hnv := (fp81s21_feature_classical_noise p R hδ hδh hr hv).1
  have hnd := (fp81s21_feature_classical_noise p R hδ hδh hr hd).1
  have hk : movingNoiseKernel R 0 r (f - g) =
      movingNoiseKernel R 0 r f - movingNoiseKernel R 0 r g := by
    funext q
    by_cases hq : q.1 ∈ Icc (0 : ℝ) r
    · have hgrad : gradient (u q.1 - v q.1) q.2 =
          gradient (u q.1) q.2 - gradient (v q.1) q.2 := by
        simp only [gradient, fderiv_sub
          ((hu.c2 q.1 hq).differentiable (by norm_num) q.2)
          ((hv.c2 q.1 hq).differentiable (by norm_num) q.2), map_sub]
      simp only [Pi.sub_apply, movingNoiseKernel, if_pos hq, r26t3_U,
        ed q.1 hq, eu q.1 hq, ev q.1 hq, hgrad, smul_sub]
    · simp only [Pi.sub_apply, movingNoiseKernel, if_neg hq, sub_zero]
  have hn : movingNoiseFeature R 0 r (f - g) =
      movingNoiseFeature R 0 r f - movingNoiseFeature R 0 r g := by
    unfold movingNoiseFeature
    rw [dif_pos hnd, dif_pos hnu, dif_pos hnv]
    apply Lp.ext
    filter_upwards [hnd.coeFn_toLp, hnu.coeFn_toLp, hnv.coeFn_toLp,
      Lp.coeFn_sub (hnu.toLp _) (hnv.toLp _)] with q hdq huq hvq hsub
    rw [hdq, hsub, Pi.sub_apply, huq, hvq]
    exact congrFun hk q
  unfold fp81s21_combinedFeature
  rw [hi, hn]
  rfl

private theorem fp81s21_feature_chart_convergence
    (p : Parameters) {δ r : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2) (hr : 0 ≤ r)
    [IsProbabilityMeasure (r26t3_mu R 0)]
    {Mg : ℝ} {K : Lp ℝ 2 (r26t3_mu R 0) →L[ℝ] Lp ℝ 2 (r26t3_mu R 0)}
    (hK : KRep (rieszKernel p.d p.s) (r26t3_mu R 0) K Mg)
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (f : Euc p.d → ℝ) (u : ℝ → Euc p.d → ℝ)
    (hfW : IsR2WeightedTest (2 * p.d + 8) ((p.d : ℝ) + 2) f)
    (hu : IsClassicalAdjointW (r26t3_coeff R) r f u)
    (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ (g : Euc p.d → ℝ) (v : ℝ → Euc p.d → ℝ),
      IsClassicalAdjointW (r26t3_coeff R) r g v →
      ‖fp81s21_combinedFeature p R hK r g‖ ^ 2 ≤
        B * ∫ x, g x ^ 2 ∂(HRS.Whole.withDensityReal R.ρβ)) :
    Tendsto (fun n => fp81s21_combinedFeature p R hK r (chartSection E (E.encode f) n))
      atTop (𝓝 (fp81s21_combinedFeature p R hK r f)) := by
  have hreg : (2 : ℝ) + (p.d : ℝ) / 2 < ((2 * p.d + 8 : ℕ) : ℝ) := by
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) p.d]
  have hP : (p.d : ℝ) < 2 * ((p.d : ℝ) + 2) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) p.d]
  obtain ⟨A, _, hOp⟩ := physical_weighted_L2_operators p.hd p.s p.a p.β
    ((p.d : ℝ) + 2) (2 * p.d + 8) p.hs0 p.hs p.ha p.hβ hreg hP R.ρβ R.thermal
  let ψ : ℕ → compactSmoothSubmodule p.d := chartSection E (E.encode f)
  have hb : ∀ n, ‖fp81s21_combinedFeature p R hK r (ψ n) -
      fp81s21_combinedFeature p R hK r f‖ ^ 2 ≤
      B * (A * (weightedSobolevE (2 * p.d + 8) ((p.d : ℝ) + 2)
        ((ψ n : Euc p.d → ℝ) - f)).toReal ^ 2) := by
    intro n
    have hn := fp81s21_U_osc_test_classical p R
      (r2Test_isOscTest (wholeSpaceIndex p.d : ℝ) (ψ n).property) hr
    rw [fp81s21_combinedFeature_classical_sub p R hδ hδh hr hK hn hu]
    exact (hbound _ _ (fp81s21_feature_classical_sub p R hn hu)).trans
      (mul_le_mul_of_nonneg_left
        (hOp _ (chartSection_error_weighted E hP f hfW n)).2.1 hB)
  have he := chartSection_error_tendsto E hP f hfW
  have hlim : Tendsto (fun n : ℕ => B * (A *
      (weightedSobolevE (2 * p.d + 8) ((p.d : ℝ) + 2)
        ((ψ n : Euc p.d → ℝ) - f)).toReal ^ 2)) atTop (𝓝 0) := by
    simpa [ψ] using ((he.pow 2).const_mul A).const_mul B
  have hsq := squeeze_zero (fun n => sq_nonneg
    ‖fp81s21_combinedFeature p R hK r (ψ n) - fp81s21_combinedFeature p R hK r f‖) hb hlim
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsq
  simpa only [Function.comp_def, Real.sqrt_zero, Real.sqrt_sq (norm_nonneg _)] using hsqrt

/-- The canonical compact chart sections converge to the literal propagated
feature. The radius is selected before every physical/source package. -/
theorem fp81s21_gaussian_propagated_feature_convergence (p : Parameters) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ R : Trajectory p δ,
      letI := fp81s21_initialMeasure_isProbability p R
      ∀ Q : fp81s21_Physical35 p R, ∀ a : ℝ, 0 ≤ a →
      ∀ r ∈ Icc (0 : ℝ) (a + p.T), ∀ t ∈ Icc r (a + p.T),
      ∀ α : MultiIndex p.d,
      let f := propagatorW (r26t3_coeff R) r t
        (oscTestFun (wholeSpaceIndex p.d : ℝ) α)
      Tendsto (fun n => fp81s21_combinedFeature p R Q.src.hK r
        (chartSection Q.E (Q.E.encode f) n))
        atTop (𝓝 (fp81s21_combinedFeature p R Q.src.hK r f)) := by
  obtain ⟨δA, hA, hAh, hbound⟩ := fp81s21_combinedFeature_classical_bound p
  obtain ⟨δW, hW, hWh, hthermal⟩ := fp81s21_gaussian_propagated_thermal_approximation p
  refine ⟨min δA δW, lt_min hA hW, (min_le_left _ _).trans hAh, ?_⟩
  intro δ hδ hδle R
  letI := fp81s21_initialMeasure_isProbability p R
  intro Q a ha r hr t ht α
  obtain ⟨B, hB, hb⟩ := hbound δ hδ (hδle.trans (min_le_left _ _)) R
  have hfW := (hthermal δ hδ (hδle.trans (min_le_right _ _)) R Q a ha r hr t ht α).1
  have hu := s111x2_cls_restrict
    (fp81s21_U_osc_test_classical p R
      (HRS.MS.GenPath.s56_isOscTest (wholeSpaceIndex p.d : ℝ) α) (hr.1.trans ht.1))
    hr.1 ht.1
  exact fp81s21_feature_chart_convergence p R hδ
    (hδle.trans ((min_le_left _ _).trans hAh)) hr.1 Q.src.hK Q.E _ _ hfW hu B hB
    (hb _ _ Q.src.hK r hr.1)

#print axioms fp81s21_feature_classical_sub
#print axioms fp81s21_combinedFeature_classical_sub
#print axioms fp81s21_feature_chart_convergence
#print axioms fp81s21_gaussian_propagated_feature_convergence
end HRS.Fp81.S21
end
