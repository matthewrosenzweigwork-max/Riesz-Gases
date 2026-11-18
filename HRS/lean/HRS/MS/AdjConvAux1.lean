import HRS.MS.SuppU2Aux13

/-!
# ADLU / AD-0: gradient of `quadV`, plain-integral convention lemmas, generator split

Infrastructure for S4.12 (`adjoint_decay`), new statements (not manuscript rows); `Adjoint.lean`,
`Dynamics.lean` are untouched.

* `ad_gradient_quadV`: for symmetric `Q`, `∇(xᵀQx/2 + c·x) = Qx + c`.
* `ad_conv_plain`: for `0 ≤ s ≤ d - 2` (so `s + 1 < d`) and a scalar `h` with
  `y ↦ h y • ∇g(x - y)` integrable, the cancellation convention `convGradConvW (∇g) h x` equals the plain
  integral `gradGConvPlain d s h x` (oddness of `∇g` and `∫_{‖z‖ ≤ 1/4} ∇g = 0`, local
  integrability of `‖z‖^{-(s+1)}`).
* `ad_generator_split`: the backward generator `generatorW C r φ x` splits as
  `ν Δφ + ⟪b_r, ∇φ⟫ - Div g*(ρ_r Mᵀ ∇φ)` with the plain divergence convolution `divGConvPlain`.
  The decay input is the pointwise form of the `AdjointDecayHyp` density bound
  (`|ρ_r y| ≤ A (1+‖y‖)^{-L}`, `ρ_r` continuous, `L > d`) and `φ ∈ C¹` with bounded gradient
  (so that every component integrand is absolutely integrable); these are the hypotheses that make the
  Bochner integrals genuine.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

namespace HRS.MS.Adj
open HRS HRS.Whole

variable {d : ℕ}

/-! ### (a) gradient of `quadV` -/

lemma adlu_matVec_selfAdj {Q : Matrix (Fin d) (Fin d) ℝ} (hQ : Q.IsSymm) (u v : Euc d) :
    inner ℝ (Torus.matVec Q u) v = inner ℝ u (Torus.matVec Q v) := by
  have hH : Q.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]; exact hQ
  exact (Matrix.isSymmetric_toEuclideanLin_iff.mpr hH) u v

/-- `∇ quadV Q c (x) = Q x + c` for symmetric `Q`. -/
theorem ad_gradient_quadV {Q : Matrix (Fin d) (Fin d) ℝ} (hQ : Q.IsSymm) (c x : Euc d) :
    gradient (quadV Q c) x = Torus.matVec Q x + c := by
  have hA : HasFDerivAt (fun y : Euc d => Torus.matVec Q y)
      ((Matrix.toEuclideanLin Q).toContinuousLinearMap) x :=
    (Matrix.toEuclideanLin Q).toContinuousLinearMap.hasFDerivAt
  have h1 := (hasFDerivAt_id x).inner ℝ hA
  have h2 := ((hasFDerivAt_const c x).inner ℝ (hasFDerivAt_id x))
  have h3 := (h1.const_mul (1/2 : ℝ)).add h2
  have hg : HasGradientAt (quadV Q c) (Torus.matVec Q x + c) x := by
    rw [hasGradientAt_iff_hasFDerivAt]
    refine (show HasFDerivAt (quadV Q c) _ x from h3).congr_fderiv ?_
    refine ContinuousLinearMap.ext fun v => ?_
    simp
    have e1 : inner ℝ x (Matrix.toEuclideanLin Q v) = inner ℝ (Torus.matVec Q x) v :=
      (adlu_matVec_selfAdj hQ x v).symm
    rw [e1, real_inner_comm v]
    ring
  exact hg.gradient

/-! ### (b) the cancellation convention equals the plain convolution -/

lemma adlu_grad_neg (s : ℝ) {z : Euc d} (hz : z ≠ 0) :
    rieszKernelGrad d s (-z) = -rieszKernelGrad d s z := by
  have hz' : -z ≠ 0 := neg_ne_zero.mpr hz
  rw [u2_rieszKernelGrad_eq s hz', u2_rieszKernelGrad_eq s hz, norm_neg, smul_neg]

lemma adlu_grad_norm (s : ℝ) {z : Euc d} (hz : z ≠ 0) :
    ‖rieszKernelGrad d s z‖ = |u2_sigma s| * ‖z‖ ^ (-(s + 1)) := by
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  rw [u2_rieszKernelGrad_eq s hz, norm_smul, Real.norm_eq_abs, abs_neg, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (‖z‖ ^ 2) ^ (-s / 2 - 1))]
  have h1 : (‖z‖ ^ 2) ^ (-s / 2 - 1) = ‖z‖ ^ (-s - 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hzpos.le]
    congr 1
    push_cast
    ring
  rw [h1, show -(s + 1) = (-s - 2) + 1 by ring, Real.rpow_add_one hzpos.ne']
  ring

lemma adlu_grad_integrableOn (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s ≤ (d : ℝ) - 2) :
    IntegrableOn (rieszKernelGrad d s) (closedBall (0 : Euc d) (1 / 4)) volume := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hb := u2_integrableOn_ball_rpow (d := d) (by omega) (a := s + 1) (by linarith) (by linarith)
  have hsub : closedBall (0 : Euc d) (1 / 4) ⊆ ball (0 : Euc d) 1 := by
    intro z hz
    rw [mem_closedBall_zero_iff] at hz
    rw [mem_ball_zero_iff]
    linarith
  have hb' := (hb.mono_set hsub).const_mul |u2_sigma s|
  refine hb'.mono' (u2_K_measurable (d := d) s).aestronglyMeasurable ?_
  refine ae_restrict_of_ae ?_
  filter_upwards [u2_ae_ne_zero (d := d) (by omega)] with z hz
  rw [adlu_grad_norm s hz]

lemma adlu_integral_ball_grad (hd : 2 ≤ d) {s : ℝ} :
    ∫ z in closedBall (0 : Euc d) (1 / 4), rieszKernelGrad d s z = 0 := by
  set S : Set (Euc d) := closedBall (0 : Euc d) (1 / 4) with hS
  have hSm : MeasurableSet S := measurableSet_closedBall
  rw [← integral_indicator hSm]
  set J : Euc d := ∫ z, S.indicator (rieszKernelGrad d s) z with hJ
  have h1 : ∫ z, S.indicator (rieszKernelGrad d s) (-z) = J := integral_neg_eq_self _ _
  have h2 : ∫ z, S.indicator (rieszKernelGrad d s) (-z) = -J := by
    rw [hJ, ← integral_neg]
    refine integral_congr_ae ?_
    filter_upwards [u2_ae_ne_zero (d := d) (by omega)] with z hz
    by_cases hzS : z ∈ S
    · have : -z ∈ S := by
        rw [hS, mem_closedBall_zero_iff] at hzS ⊢
        rwa [norm_neg]
      rw [Set.indicator_of_mem this, Set.indicator_of_mem hzS, adlu_grad_neg s hz]
    · have : -z ∉ S := by
        rw [hS, mem_closedBall_zero_iff] at hzS ⊢
        rwa [norm_neg]
      rw [Set.indicator_of_notMem this, Set.indicator_of_notMem hzS, neg_zero]
  have h3 : J = -J := h1.symm.trans h2
  have h4 : (2 : ℝ) • J = 0 := by
    rw [two_smul]
    nth_rewrite 1 [h3]
    exact neg_add_cancel J
  exact (smul_eq_zero.mp h4).resolve_left (by norm_num)

/-- (b) For `0 ≤ s ≤ d - 2`, if `y ↦ h y • ∇g(x - y)` is integrable then the cancellation convention
`convGradConvW (∇g) h x` is the plain integral `gradGConvPlain d s h x`. -/
theorem ad_conv_plain (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s ≤ (d : ℝ) - 2)
    (h : Euc d → ℝ) {x : Euc d}
    (hint : Integrable (fun y => h y • rieszKernelGrad d s (x - y)) volume) :
    convGradConvW (rieszKernelGrad d s) h x = gradGConvPlain d s h x := by
  set S : Set (Euc d) := closedBall (0 : Euc d) (1 / 4) with hS
  have hSm : MeasurableSet S := measurableSet_closedBall
  have hG := adlu_grad_integrableOn hd hs0 hsd
  have hF2 : Integrable (fun y => S.indicator (fun z => h x • rieszKernelGrad d s z) (x - y))
      volume := by
    have : Integrable (S.indicator (fun z => h x • rieszKernelGrad d s z)) volume :=
      (integrable_indicator_iff hSm).mpr (hG.smul (h x))
    exact this.comp_sub_left x
  have hpt : ∀ y, (if ‖x - y‖ ≤ 1 / 4 then (h y - h x) • rieszKernelGrad d s (x - y)
      else h y • rieszKernelGrad d s (x - y)) =
      h y • rieszKernelGrad d s (x - y) -
        S.indicator (fun z => h x • rieszKernelGrad d s z) (x - y) := by
    intro y
    by_cases hy : ‖x - y‖ ≤ 1 / 4
    · have : x - y ∈ S := by rw [hS, mem_closedBall_zero_iff]; exact hy
      rw [if_pos hy, Set.indicator_of_mem this, sub_smul]
    · have : x - y ∉ S := by rw [hS, mem_closedBall_zero_iff]; exact hy
      rw [if_neg hy, Set.indicator_of_notMem this, sub_zero]
  have hI : ∫ y, S.indicator (fun z => h x • rieszKernelGrad d s z) (x - y) = 0 := by
    rw [integral_sub_left_eq_self (S.indicator (fun z => h x • rieszKernelGrad d s z)) volume x,
      integral_indicator hSm, integral_smul, adlu_integral_ball_grad hd, smul_zero]
  unfold convGradConvW gradGConvPlain
  simp_rw [hpt]
  rw [integral_sub hint hF2, hI, sub_zero]

/-! ### (c) the generator split -/

lemma adlu_integrable_conv (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s ≤ (d : ℝ) - 2)
    {h : Euc d → ℝ} (hc : Continuous h) {A L : ℝ} (hL : (d : ℝ) < L) (hA : 0 ≤ A)
    (hh0 : ∀ y, ‖h y‖ ≤ A * u2Wt L y) (x : Euc d) :
    Integrable (fun y => h y • rieszKernelGrad d s (x - y)) volume := by
  have hcomp : ∀ i' : Fin d, Integrable (fun y => (h y • rieszKernelGrad d s (x - y)) i') volume := by
    intro i'
    have h1 := u2_conv_integrable (u2_kerFull hd hs0 hsd i').ker hL hc hA hh0 x
    have h2 := h1.comp_sub_left x
    refine h2.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [sub_sub_cancel, u2_kap, PiLp.smul_apply, smul_eq_mul]
    ring
  refine u2_integrable_of_coord ?_ hcomp
  exact (hc.aestronglyMeasurable).smul
    ((u2_K_measurable (d := d) s).comp (measurable_const.sub measurable_id)).aestronglyMeasurable

lemma adlu_conv_comp (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s ≤ (d : ℝ) - 2)
    {h : Euc d → ℝ} (hc : Continuous h) {A L : ℝ} (hL : (d : ℝ) < L) (hA : 0 ≤ A)
    (hh0 : ∀ y, ‖h y‖ ≤ A * u2Wt L y) (x : Euc d) (j : Fin d) :
    (convGradConvW (rieszKernelGrad d s) h x) j = ∫ y, rieszKernelGrad d s (x - y) j * h y := by
  have hF := adlu_integrable_conv hd hs0 hsd hc hL hA hh0 x
  rw [ad_conv_plain hd hs0 hsd h hF]
  have := ContinuousLinearMap.integral_comp_comm (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ) hF
  unfold gradGConvPlain
  have e1 : (∫ y, h y • rieszKernelGrad d s (x - y)) j =
      ∫ y, (h y • rieszKernelGrad d s (x - y)) j := by
    simpa using this.symm
  rw [e1]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [PiLp.smul_apply, smul_eq_mul]
  ring

lemma adlu_continuous_gradient {φ : Euc d → ℝ} (hφ : ContDiff ℝ 1 φ) :
    Continuous (gradient φ) := by
  unfold gradient
  exact (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp (hφ.continuous_fderiv one_ne_zero)

lemma adlu_continuous_matVec (M : Matrix (Fin d) (Fin d) ℝ) :
    Continuous (Torus.matVec M) :=
  (Matrix.toEuclideanLin M).toContinuousLinearMap.continuous

/-- (c) Under the pointwise decay hypotheses (`|ρ_r y| ≤ A (1+‖y‖)^{-L}`, `L > d`, `ρ_r` continuous;
`φ ∈ C¹` with bounded gradient) and `0 ≤ s ≤ d - 2`, the backward generator splits with the plain
divergence convolution. -/
theorem ad_generator_split (hd : 2 ≤ d) (C : WholeCoeff d) (hs0 : 0 ≤ C.s)
    (hsd : C.s ≤ (d : ℝ) - 2) (r : ℝ) (φ : Euc d → ℝ) (x : Euc d)
    (hρc : Continuous (C.ρ r)) {A L : ℝ} (hA : 0 ≤ A) (hL : (d : ℝ) < L)
    (hρ : ∀ y, |C.ρ r y| ≤ A * u2Wt L y) (hφ : ContDiff ℝ 1 φ) {Bφ : ℝ}
    (hB : ∀ y, ‖gradient φ y‖ ≤ Bφ) :
    generatorW C r φ x = C.ν * Laplacian.laplacian φ x + inner ℝ (C.drift r x) (gradient φ x) -
      divGConvPlain d C.s (fun y => C.ρ r y • Torus.matVec C.M.transpose (gradient φ y)) x := by
  set T : Euc d →L[ℝ] Euc d := (Matrix.toEuclideanLin C.M.transpose).toContinuousLinearMap with hT
  have hTv : ∀ v, Torus.matVec C.M.transpose v = T v := fun v => rfl
  have hcomp : ∀ j : Fin d, ∀ y, ‖C.ρ r y * (Torus.matVec C.M.transpose (gradient φ y)) j‖ ≤
      (A * (‖T‖ * Bφ)) * u2Wt L y := by
    intro j y
    have h1 : |(Torus.matVec C.M.transpose (gradient φ y)) j| ≤ ‖T‖ * Bφ := by
      have := PiLp.norm_apply_le (Torus.matVec C.M.transpose (gradient φ y)) j
      rw [Real.norm_eq_abs] at this
      refine this.trans ?_
      rw [hTv]
      exact (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hB y) (norm_nonneg _))
    have h2 := hρ y
    have hw := u2Wt_pos (d := d) L y
    rw [Real.norm_eq_abs, abs_mul]
    calc |C.ρ r y| * |(Torus.matVec C.M.transpose (gradient φ y)) j|
        ≤ (A * u2Wt L y) * (‖T‖ * Bφ) :=
          mul_le_mul h2 h1 (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hAnn : 0 ≤ A * (‖T‖ * Bφ) := by
    have h0 : 0 ≤ ‖T‖ * Bφ := by
      refine le_trans ?_ (mul_le_mul_of_nonneg_left (hB 0) (norm_nonneg _))
      exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
    positivity
  have hcont : ∀ j : Fin d, Continuous (fun y => C.ρ r y * (Torus.matVec C.M.transpose (gradient φ y)) j) := by
    intro j
    exact hρc.mul ((EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).continuous.comp
      ((adlu_continuous_matVec _).comp (adlu_continuous_gradient hφ)))
  have hsum : ∑ j : Fin d, (convGradConvW (rieszKernelGrad d C.s)
      (fun y => C.ρ r y * (Torus.matVec C.M.transpose (gradient φ y)) j) x) j =
      divGConvPlain d C.s (fun y => C.ρ r y • Torus.matVec C.M.transpose (gradient φ y)) x := by
    unfold divGConvPlain
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [adlu_conv_comp hd hs0 hsd (hcont j) hL hAnn (hcomp j) x j]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [PiLp.smul_apply, smul_eq_mul]
  unfold generatorW
  rw [hsum]

/-- (c), in the hypotheses of `AdjointDecayHyp`: for `r ∈ [0,T]` and `φ ∈ C¹` with bounded gradient,
the generator of the dynamics `(s, M, quadV Q c, ν)` along `ρ` is
`ν Δφ + ⟪M ∇g*ρ_r - (Qx + c), ∇φ⟫ - Div g*(ρ_r Mᵀ ∇φ)` (plain divergence convolution). -/
theorem ad_generator_split_hyp (hd : 2 ≤ d) {θ : Euc d → ℝ} {s : ℝ} {M Q : Matrix (Fin d) (Fin d) ℝ}
    {c : Euc d} {T νstar : ℝ} {k : ℕ} {L Λ K ν : ℝ} {ρ : ℝ → Euc d → ℝ}
    (D : AdjointDecayHyp θ s M Q c T νstar k L Λ K ν ρ) {r : ℝ} (hr : r ∈ Set.Icc 0 T)
    (φ : Euc d → ℝ) (x : Euc d) (hφ : ContDiff ℝ 1 φ) {Bφ : ℝ} (hB : ∀ y, ‖gradient φ y‖ ≤ Bφ) :
    generatorW ((⟨s, M, quadV Q c, ν⟩ : WholeDyn d).coeff ρ) r φ x =
      ν * Laplacian.laplacian φ x +
        inner ℝ (Torus.matVec M (convGradConvW (rieszKernelGrad d s) (ρ r) x) - (Torus.matVec Q x + c))
          (gradient φ x) -
      divGConvPlain d s (fun y => ρ r y • Torus.matVec M.transpose (gradient φ y)) x := by
  obtain ⟨_, hρsm, hwse⟩ := D.density r hr
  have hdR : (d : ℝ) < L := by
    have := D.L_range
    have h0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have h1 := D.s_range.1
    linarith
  have hL0 : 0 ≤ L := by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have hΛ : ∀ j ≤ 0, ∀ (I : Fin j → Fin d) (x : Euc d),
      jbracket x ^ L * |partialDeriv I (ρ r) x| ≤ max Λ 0 :=
    fun j hj I x => u2_wse_bound hwse j (by omega) I x
  have hbd : ∀ y, |ρ r y| ≤ ((d : ℝ) ^ 0 * 2 ^ L * max Λ 0) * u2Wt L y := by
    intro y
    have := u2_norm_le_of_partial (by omega) (k := 0) hL0 (le_max_right Λ 0) hΛ 0 le_rfl y
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  have hρc : Continuous (ρ r) := hρsm.continuous
  have h := ad_generator_split hd ((⟨s, M, quadV Q c, ν⟩ : WholeDyn d).coeff ρ) D.s_range.1
    D.s_range.2 r φ x hρc (A := (d : ℝ) ^ 0 * 2 ^ L * max Λ 0) (by positivity) hdR
    (fun y => hbd y) hφ hB
  rw [h]
  have hdr : ((⟨s, M, quadV Q c, ν⟩ : WholeDyn d).coeff ρ).drift r x =
      Torus.matVec M (convGradConvW (rieszKernelGrad d s) (ρ r) x) - (Torus.matVec Q x + c) := by
    show meanFieldDriftW ⟨s, M, quadV Q c, ν⟩ (ρ r) x = _
    unfold meanFieldDriftW
    simp only
    rw [ad_gradient_quadV D.Q_symm]
  rw [hdr]
  rfl

end HRS.MS.Adj
