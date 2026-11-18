import HRS.MS.PoisSgAux2

/-!
# POIS-MOLL, part 1: passage of uniform derivative bounds to a pointwise limit, and mollification

Abstract analysis (no probability), helper lemmas prefixed `moll_`.

* `moll_dir_tendsto`: if `g_n → g` pointwise and the directional derivatives `D g_n(·) v` are
  uniformly Lipschitz, then `D g_n(x) v → D g(x) v` (difference quotients).
* `moll_closing`: if `f_n, f ∈ C^{j0}`, `f_n → f` pointwise and `‖D^i f_n‖ ≤ C i` for `i ≤ j0` and all
  `n`, then `‖D^i f‖ ≤ C i` for `i ≤ j0`.  (Bounds on `D^i f_n` give pointwise convergence
  `D^i f_n → D^i f` for `i < j0` by the difference-quotient lemma, and the top order follows from the
  Lipschitz bound of `D^{j0-1} f_n`.)
-/

open MeasureTheory Set Filter Topology
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.PoisFlow HRS.MS.PoisSg
open scoped Convolution ContDiff

set_option linter.unusedSectionVars false

noncomputable section

namespace HRS.MS.PoisMoll

section Closing

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- Taylor-type estimate for a function with Lipschitz directional derivative. -/
theorem moll_taylor {g : E → F} {C : ℝ} {v : E} (hdiff : Differentiable ℝ g) (hC : 0 ≤ C)
    (hlip : ∀ y z, ‖fderiv ℝ g y v - fderiv ℝ g z v‖ ≤ C * ‖y - z‖) (x : E) {s : ℝ}
    (hs : 0 < s) :
    ‖fderiv ℝ g x v - s⁻¹ • (g (x + s • v) - g x)‖ ≤ C * s * ‖v‖ := by
  set φ : ℝ → F := fun t => g (x + t • v) - t • fderiv ℝ g x v with hφ
  have hder : ∀ t : ℝ, HasDerivAt φ (fderiv ℝ g (x + t • v) v - fderiv ℝ g x v) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => x + t • v) v t := by
      simpa using ((hasDerivAt_id t).smul_const v).const_add x
    have h2 := (hdiff (x + t • v)).hasFDerivAt.comp_hasDerivAt t h1
    have h3 : HasDerivAt (fun t : ℝ => t • fderiv ℝ g x v) (fderiv ℝ g x v) t := by
      simpa using (hasDerivAt_id t).smul_const (fderiv ℝ g x v)
    exact h2.sub h3
  have hbd : ∀ t ∈ Icc (0 : ℝ) s, ‖fderiv ℝ g (x + t • v) v - fderiv ℝ g x v‖ ≤ C * s * ‖v‖ := by
    intro t ht
    refine (hlip _ _).trans ?_
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.1]
    calc C * (t * ‖v‖) = C * t * ‖v‖ := by ring
      _ ≤ C * s * ‖v‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact mul_le_mul_of_nonneg_left ht.2 hC
  have hmv := (convex_Icc (0 : ℝ) s).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ => (hder t).hasDerivWithinAt) hbd (left_mem_Icc.2 hs.le) (right_mem_Icc.2 hs.le)
  have e : φ s - φ 0 = (g (x + s • v) - g x) - s • fderiv ℝ g x v := by
    simp only [hφ, zero_smul, sub_zero, add_zero]; abel
  rw [e, sub_zero, Real.norm_of_nonneg hs.le] at hmv
  have e2 : fderiv ℝ g x v - s⁻¹ • (g (x + s • v) - g x) =
      -(s⁻¹ • ((g (x + s • v) - g x) - s • fderiv ℝ g x v)) := by
    have h : s⁻¹ • (s • fderiv ℝ g x v) = fderiv ℝ g x v := by
      rw [smul_smul, inv_mul_cancel₀ hs.ne', one_smul]
    simp only [smul_sub, h]; abel
  rw [e2, norm_neg, norm_smul, norm_inv, Real.norm_of_nonneg hs.le]
  calc s⁻¹ * ‖(g (x + s • v) - g x) - s • fderiv ℝ g x v‖ ≤ s⁻¹ * (C * s * ‖v‖ * s) :=
        mul_le_mul_of_nonneg_left hmv (inv_nonneg.2 hs.le)
    _ = C * s * ‖v‖ := by field_simp

/-- Pointwise convergence of the directional derivatives. -/
theorem moll_dir_tendsto {g : ℕ → E → F} {g0 : E → F} {x v : E} {C : ℝ} (hC : 0 ≤ C)
    (hdiff : ∀ n, Differentiable ℝ (g n)) (hd0 : DifferentiableAt ℝ g0 x)
    (hlip : ∀ n y z, ‖fderiv ℝ (g n) y v - fderiv ℝ (g n) z v‖ ≤ C * ‖y - z‖)
    (hlim : ∀ y, Tendsto (fun n => g n y) atTop (𝓝 (g0 y))) :
    Tendsto (fun n => fderiv ℝ (g n) x v) atTop (𝓝 (fderiv ℝ g0 x v)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have h1 : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have h2 : HasDerivAt (fun t : ℝ => g0 (x + t • v)) (fderiv ℝ g0 x v) 0 := by
    have := hd0.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) h1 (by simp)
    exact this
  have hslope := h2.tendsto_slope_zero_right
  have hev1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), dist (t⁻¹ • (g0 (x + t • v) - g0 x))
      (fderiv ℝ g0 x v) < ε / 3 := by
    have := hslope.eventually (Metric.ball_mem_nhds _ (show 0 < ε / 3 by positivity))
    filter_upwards [this] with t ht
    simp only [zero_add, zero_smul, add_zero] at ht
    exact ht
  have hev2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < ε / (3 * (C * ‖v‖ + 1)) := by
    have hpos : 0 < ε / (3 * (C * ‖v‖ + 1)) := by positivity
    filter_upwards [Ioo_mem_nhdsGT hpos] with t ht using ht.2
  obtain ⟨s, ⟨hs1, hs2⟩, hs0⟩ := ((hev1.and hev2).and
    (eventually_mem_nhdsWithin : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioi (0 : ℝ))).exists
  have hs0' : 0 < s := hs0
  have hCs : C * s * ‖v‖ < ε / 3 := by
    have hD : 0 < C * ‖v‖ + 1 := by positivity
    have : s * (3 * (C * ‖v‖ + 1)) < ε := by
      have := (lt_div_iff₀ (by positivity : (0 : ℝ) < 3 * (C * ‖v‖ + 1))).1 hs2
      exact this
    nlinarith [mul_nonneg hC (norm_nonneg v), hs0']
  have hlimq : Tendsto (fun n => s⁻¹ • (g n (x + s • v) - g n x)) atTop
      (𝓝 (s⁻¹ • (g0 (x + s • v) - g0 x))) :=
    (((hlim _).sub (hlim x)).const_smul s⁻¹)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hlimq (ε / 3) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hn1 : dist (fderiv ℝ (g n) x v) (s⁻¹ • (g n (x + s • v) - g n x)) < ε / 3 := by
    rw [dist_eq_norm]
    exact lt_of_le_of_lt (moll_taylor (hdiff n) hC (hlip n) x hs0') hCs
  have := hN n hn
  calc dist (fderiv ℝ (g n) x v) (fderiv ℝ g0 x v)
      ≤ dist (fderiv ℝ (g n) x v) (s⁻¹ • (g n (x + s • v) - g n x)) +
        dist (s⁻¹ • (g n (x + s • v) - g n x)) (s⁻¹ • (g0 (x + s • v) - g0 x)) +
        dist (s⁻¹ • (g0 (x + s • v) - g0 x)) (fderiv ℝ g0 x v) := dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by gcongr
    _ = ε := by ring

/-- A pointwise limit of uniformly Lipschitz functions has directional derivatives bounded by the
Lipschitz constant. -/
theorem moll_dir_bound {g : ℕ → E → F} {g0 : E → F} {x : E} {K : ℝ} (hK : 0 ≤ K)
    (hlip : ∀ n y z, ‖g n y - g n z‖ ≤ K * ‖y - z‖)
    (hlim : ∀ y, Tendsto (fun n => g n y) atTop (𝓝 (g0 y))) (u : E) :
    ‖fderiv ℝ g0 x u‖ ≤ K * ‖u‖ := by
  have hl0 : ∀ y z, ‖g0 y - g0 z‖ ≤ K * ‖y - z‖ := fun y z =>
    le_of_tendsto ((hlim y).sub (hlim z)).norm (Eventually.of_forall fun n => hlip n y z)
  have hL : LipschitzWith K.toNNReal g0 := LipschitzWith.of_dist_le_mul fun y z => by
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hK]; exact hl0 y z
  have h1 := norm_fderiv_le_of_lipschitz (𝕜 := ℝ) (x₀ := x) hL
  rw [Real.coe_toNNReal _ hK] at h1
  exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right h1 (norm_nonneg _))

/-- Lipschitz bound for `D^i f` from a bound on `D^{i+1} f`. -/
theorem moll_lip_iter {f : E → F} {i j0 : ℕ} {C : ℝ} (hf : ContDiff ℝ (j0 : WithTop ℕ∞) f)
    (hi : i < j0) (hb : ∀ y, ‖iteratedFDeriv ℝ (i + 1) f y‖ ≤ C) (y z : E) :
    ‖iteratedFDeriv ℝ i f y - iteratedFDeriv ℝ i f z‖ ≤ C * ‖y - z‖ := by
  have hd : Differentiable ℝ (iteratedFDeriv ℝ i f) :=
    hf.differentiable_iteratedFDeriv (by exact_mod_cast hi)
  exact (convex_univ (𝕜 := ℝ) (E := E)).norm_image_sub_le_of_norm_fderiv_le
    (fun x _ => hd x) (fun x _ => by rw [norm_fderiv_iteratedFDeriv]; exact hb x)
    (mem_univ z) (mem_univ y)

/-- Pointwise convergence of the iterated derivatives `D^i f_n → D^i f` for `i < j0`. -/
theorem moll_iter_tendsto {f : ℕ → E → F} {f0 : E → F} {j0 : ℕ} {C : ℕ → ℝ}
    (hf : ∀ n, ContDiff ℝ (j0 : WithTop ℕ∞) (f n)) (hf0 : ContDiff ℝ (j0 : WithTop ℕ∞) f0)
    (hlim : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (f0 x)))
    (hb : ∀ n i, i ≤ j0 → ∀ x, ‖iteratedFDeriv ℝ i (f n) x‖ ≤ C i) :
    ∀ i, (i = 0 ∨ i < j0) → ∀ x (v : Fin i → E),
      Tendsto (fun n => iteratedFDeriv ℝ i (f n) x v) atTop (𝓝 (iteratedFDeriv ℝ i f0 x v)) := by
  intro i
  induction i with
  | zero =>
    intro _ x v
    simpa using hlim x
  | succ i ih =>
    intro hi x v
    have hij : i < j0 := by omega
    have hi1 : i + 1 ≤ j0 := by omega
    have hd : ∀ n, Differentiable ℝ (iteratedFDeriv ℝ i (f n)) := fun n =>
      (hf n).differentiable_iteratedFDeriv (by exact_mod_cast hij)
    have hd0 : Differentiable ℝ (iteratedFDeriv ℝ i f0) :=
      hf0.differentiable_iteratedFDeriv (by exact_mod_cast hij)
    have key : ∀ (h : E → F) (hh : Differentiable ℝ (iteratedFDeriv ℝ i h)) y,
        fderiv ℝ (fun y => iteratedFDeriv ℝ i h y (Fin.tail v)) y (v 0) =
          iteratedFDeriv ℝ (i + 1) h y v := fun h hh y =>
      ((hh y).iteratedFDeriv_succ_apply_left' (m := v)).symm
    have hC0 : 0 ≤ C (i + 2) := (norm_nonneg _).trans (hb 0 (i + 2) (by omega) 0)
    have hlipn : ∀ n y z, ‖iteratedFDeriv ℝ (i + 1) (f n) y - iteratedFDeriv ℝ (i + 1) (f n) z‖ ≤
        C (i + 2) * ‖y - z‖ := fun n y z =>
      moll_lip_iter (hf n) (by omega) (fun y => hb n (i + 2) (by omega) y) y z
    have hdir := moll_dir_tendsto (g := fun n y => iteratedFDeriv ℝ i (f n) y (Fin.tail v))
      (g0 := fun y => iteratedFDeriv ℝ i f0 y (Fin.tail v)) (x := x) (v := v 0)
      (C := C (i + 2) * ∏ j, ‖v j‖)
      (mul_nonneg hC0 (Finset.prod_nonneg fun _ _ => norm_nonneg _))
      (fun n => (hd n).continuousMultilinear_apply_const _)
      ((hd0 x).continuousMultilinear_apply_const _) (fun n y z => ?_)
      (fun y => ih (Or.inr hij) y (Fin.tail v))
    · simpa only [key _ (hd _), key _ hd0] using hdir
    · rw [key _ (hd n), key _ (hd n), ← sub_apply]
      refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
      have := hlipn n y z
      calc _ ≤ (C (i + 2) * ‖y - z‖) * ∏ j, ‖v j‖ :=
            mul_le_mul_of_nonneg_right this (Finset.prod_nonneg fun _ _ => norm_nonneg _)
        _ = _ := by ring

/-- **Closing lemma.**  If `f_n → f` pointwise, all `f_n`, `f` are `C^{j0}` and
`‖D^i f_n x‖ ≤ C i` for all `n`, `x` and `i ≤ j0`, then `‖D^i f x‖ ≤ C i` for all `i ≤ j0`.
(The bounds are needed for `f_n` at orders `≤ j0` only; no convergence of derivatives is assumed.) -/
theorem moll_closing {f : ℕ → E → F} {f0 : E → F} {j0 : ℕ} {C : ℕ → ℝ}
    (hf : ∀ n, ContDiff ℝ (j0 : WithTop ℕ∞) (f n)) (hf0 : ContDiff ℝ (j0 : WithTop ℕ∞) f0)
    (hlim : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (f0 x)))
    (hb : ∀ n i, i ≤ j0 → ∀ x, ‖iteratedFDeriv ℝ i (f n) x‖ ≤ C i) :
    ∀ i, i ≤ j0 → ∀ x, ‖iteratedFDeriv ℝ i f0 x‖ ≤ C i := by
  intro i hi x
  have hC : ∀ i, i ≤ j0 → 0 ≤ C i := fun i hi => (norm_nonneg _).trans (hb 0 i hi 0)
  by_cases hcase : i = 0 ∨ i < j0
  · refine ContinuousMultilinearMap.opNorm_le_bound (hC i hi) fun v => ?_
    refine le_of_tendsto (moll_iter_tendsto hf hf0 hlim hb i hcase x v).norm
      (Eventually.of_forall fun n => ?_)
    exact (ContinuousMultilinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hb n i hi x) (Finset.prod_nonneg fun _ _ => norm_nonneg _))
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    have hi' : i' < j0 := by omega
    have hij : i' + 1 = j0 := by omega
    refine ContinuousMultilinearMap.opNorm_le_bound (hC _ hi) fun v => ?_
    have hd0 : Differentiable ℝ (iteratedFDeriv ℝ i' f0) :=
      hf0.differentiable_iteratedFDeriv (by exact_mod_cast hi')
    have hK : 0 ≤ C (i' + 1) * ∏ j, ‖Fin.tail v j‖ :=
      mul_nonneg (hC _ hi) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    have h1 := moll_dir_bound (g := fun n y => iteratedFDeriv ℝ i' (f n) y (Fin.tail v))
      (g0 := fun y => iteratedFDeriv ℝ i' f0 y (Fin.tail v)) (x := x) hK (fun n y z => by
        rw [← sub_apply]
        refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
        calc _ ≤ (C (i' + 1) * ‖y - z‖) * ∏ j, ‖Fin.tail v j‖ :=
              mul_le_mul_of_nonneg_right
                (moll_lip_iter (hf n) hi' (fun y => hb n (i' + 1) hi y) y z)
                (Finset.prod_nonneg fun _ _ => norm_nonneg _)
          _ = _ := by ring)
      (fun y => moll_iter_tendsto hf hf0 hlim hb i' (Or.inr hi') y (Fin.tail v)) (v 0)
    rw [(hd0 x).iteratedFDeriv_succ_apply_left' (m := v)]
    refine h1.trans ?_
    rw [Fin.prod_univ_succ]
    simp only [Fin.tail]
    nlinarith [mul_nonneg hK (norm_nonneg (v 0))]

end Closing

/-! ### Mollification by the normed bump of radius `1/(n+1)` -/

section Mollify

variable {d : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- The bump function of outer radius `1/(n+1)`. -/
def mollBump (d n : ℕ) : ContDiffBump (0 : Euc d) where
  rIn := 1 / (2 * ((n : ℝ) + 1))
  rOut := 1 / ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [div_lt_div_iff₀ (by positivity) this]; nlinarith

/-- The mollifier (a probability density supported in the ball of radius `1/(n+1)`). -/
def mollKer (d n : ℕ) : Euc d → ℝ := (mollBump d n).normed volume

/-- Mollification `F ↦ η_n * F`. -/
def mollify (n : ℕ) (F : Euc d → V) (x : Euc d) : V := ∫ t, mollKer d n t • F (x - t)

theorem moll_ker_nonneg (n : ℕ) (t : Euc d) : 0 ≤ mollKer d n t := (mollBump d n).nonneg_normed t

theorem moll_ker_integral (n : ℕ) : ∫ t, mollKer d n t = 1 := (mollBump d n).integral_normed

theorem moll_ker_support (n : ℕ) : Function.support (mollKer d n) = Metric.ball 0 (1 / ((n : ℝ) + 1)) :=
  (mollBump d n).support_normed_eq

theorem moll_ker_contDiff (n : ℕ) : ContDiff ℝ ∞ (mollKer d n) := (mollBump d n).contDiff_normed

theorem moll_ker_compact (n : ℕ) : HasCompactSupport (mollKer d n) :=
  (mollBump d n).hasCompactSupport_normed

theorem moll_ker_zero (n : ℕ) {t : Euc d} (ht : 1 / ((n : ℝ) + 1) ≤ ‖t‖) : mollKer d n t = 0 := by
  by_contra h
  have : t ∈ Function.support (mollKer d n) := h
  rw [moll_ker_support] at this
  simp only [Metric.mem_ball, dist_zero_right] at this
  linarith

omit [CompleteSpace V] in
theorem moll_eq_convolution (n : ℕ) (F : Euc d → V) :
    mollify n F = (mollKer d n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] F) := by
  funext x; rfl

theorem moll_contDiff (n : ℕ) {F : Euc d → V} (hF : Continuous F) :
    ContDiff ℝ ∞ (mollify n F) := by
  rw [moll_eq_convolution]
  exact (moll_ker_compact n).contDiff_convolution_left _ (moll_ker_contDiff n)
    (hF.locallyIntegrable)

theorem moll_approx (n : ℕ) {F : Euc d → V} {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖) (x : Euc d) :
    ‖mollify n F x - F x‖ ≤ L / ((n : ℝ) + 1) := by
  have hF : Continuous F :=
    (LipschitzWith.of_dist_le_mul (K := L.toNNReal) fun x y => by
      rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hL0]; exact hL x y).continuous
  have := (mollBump d n).dist_normed_convolution_le (μ := volume) (x₀ := x)
    (ε := L / ((n : ℝ) + 1)) hF.aestronglyMeasurable (fun y hy => by
      rw [dist_eq_norm]
      refine (hL y x).trans ?_
      have : ‖y - x‖ < 1 / ((n : ℝ) + 1) := by
        have := hy
        simpa [mollBump, Metric.mem_ball, dist_eq_norm] using this
      calc L * ‖y - x‖ ≤ L * (1 / ((n : ℝ) + 1)) := mul_le_mul_of_nonneg_left this.le hL0
        _ = L / ((n : ℝ) + 1) := by ring)
  rw [dist_eq_norm] at this
  exact this

theorem moll_tendsto {F : Euc d → V} (hF : Continuous F) (x : Euc d) :
    Tendsto (fun n => mollify n F x) atTop (𝓝 (F x)) := by
  refine ContDiffBump.convolution_tendsto_right_of_continuous (μ := volume)
    (φ := fun n : ℕ => mollBump d n) (l := atTop) ?_ hF x
  simpa [mollBump] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

theorem moll_set_integral_eq (n : ℕ) {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (f : Euc d → W) (hf : ∀ t : Euc d, 1 / ((n : ℝ) + 1) ≤ ‖t‖ → f t = 0) :
    ∫ t in Metric.ball (0 : Euc d) (1 / ((n : ℝ) + 1)), f t = ∫ t, f t := by
  refine setIntegral_eq_integral_of_forall_compl_eq_zero (fun t ht => hf t ?_)
  simpa [Metric.mem_ball] using ht

/-- Mollification does not increase the derivative bounds: `‖D^j (η_n * F)‖ ≤ M j` if
`‖D^j F‖ ≤ M j`, for `j ≤ k`. -/
theorem moll_iter_le (n : ℕ) {F : Euc d → V} {k : ℕ} (hF : ContDiff ℝ (k : WithTop ℕ∞) F)
    {M : ℕ → ℝ} (hb : ∀ j ≤ k, ∀ y, ‖iteratedFDeriv ℝ j F y‖ ≤ M j) (j : ℕ) (hj : j ≤ k)
    (x : Euc d) : ‖iteratedFDeriv ℝ j (mollify n F) x‖ ≤ M j := by
  set r : ℝ := 1 / ((n : ℝ) + 1) with hr
  set ν : Measure (Euc d) := volume.restrict (Metric.ball (0 : Euc d) r) with hν
  have : IsFiniteMeasure ν := ⟨by rw [hν, Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  set G : Euc d → Euc d → V := fun t x => mollKer d n t • F (x - t) with hG
  have hshift : ∀ t : Euc d, ContDiff ℝ (k : WithTop ℕ∞) (fun x => F (x - t)) := fun t =>
    hF.comp (contDiff_id.sub contDiff_const)
  have hGc : ∀ t, ContDiff ℝ (k : WithTop ℕ∞) (G t) := fun t => (hshift t).const_smul _
  have hGiter : ∀ t x i, i ≤ k →
      iteratedFDeriv ℝ i (G t) x = mollKer d n t • iteratedFDeriv ℝ i F (x - t) := by
    intro t x i hi
    have h1 : G t = fun x => mollKer d n t • F (x - t) := rfl
    rw [h1, iteratedFDeriv_const_smul_apply' (((hshift t).of_le (by exact_mod_cast hi)).contDiffAt),
      iteratedFDeriv_comp_sub]
  have hint : ∀ x, ∫ t, G t x ∂ν = mollify n F x := fun x =>
    moll_set_integral_eq n (fun t => G t x) (fun t ht => by
      simp [hG, moll_ker_zero n ht])
  obtain ⟨S, hS⟩ : ∃ S, ∀ t, ‖mollKer d n t‖ ≤ S :=
    (moll_ker_contDiff n).continuous.bounded_above_of_compact_support (moll_ker_compact n)
  have hbd : ∀ i ≤ k, ∃ M' : ℝ, ∀ t x, ‖iteratedFDeriv ℝ i (G t) x‖ ≤ M' := by
    intro i hi
    refine ⟨S * M i, fun t x => ?_⟩
    rw [hGiter t x i hi, norm_smul]
    exact mul_le_mul (hS t) (hb i hi _) (norm_nonneg _) ((norm_nonneg _).trans (hS t))
  have hmeas : ∀ i ≤ k, ∀ x, AEStronglyMeasurable (fun t => iteratedFDeriv ℝ i (G t) x) ν := by
    intro i hi x
    have : (fun t => iteratedFDeriv ℝ i (G t) x) =
        fun t => mollKer d n t • iteratedFDeriv ℝ i F (x - t) :=
      funext fun t => hGiter t x i hi
    rw [this]
    exact ((moll_ker_contDiff n).continuous.smul
      ((hF.continuous_iteratedFDeriv (by exact_mod_cast hi)).comp
        (continuous_const.sub continuous_id))).aestronglyMeasurable
  obtain ⟨-, hform⟩ := sg_iteratedFDeriv_integral (μ := ν) G k hGc hbd hmeas
  have hfun : (fun x => ∫ t, G t x ∂ν) = mollify n F := funext hint
  rw [hfun] at hform
  rw [hform j hj x]
  have hKint : Integrable (fun t => mollKer d n t * M j) ν :=
    ((mollBump d n).integrable_normed (μ := volume)).restrict.mul_const _
  refine (norm_integral_le_of_norm_le hKint (ae_of_all _ fun t => ?_)).trans ?_
  · rw [hGiter t x j hj, norm_smul, Real.norm_of_nonneg (moll_ker_nonneg n t)]
    exact mul_le_mul_of_nonneg_left (hb j hj _) (moll_ker_nonneg n t)
  · rw [integral_mul_const, hν, moll_set_integral_eq n (fun t => mollKer d n t) (fun t ht =>
      moll_ker_zero n ht), moll_ker_integral, one_mul]

/-- All derivatives of the mollification of a bounded continuous function are bounded (by a
constant depending on `n`, `k` and the bound). -/
theorem moll_iter_bdd (n : ℕ) {F : Euc d → V} (hF : Continuous F) {M0 : ℝ}
    (hb : ∀ y, ‖F y‖ ≤ M0) (k : ℕ) :
    ∃ Ck : ℝ, ∀ x, ‖iteratedFDeriv ℝ k (mollify n F) x‖ ≤ Ck := by
  set r : ℝ := 1 / ((n : ℝ) + 1) with hr
  have hr0 : 0 < r := by positivity
  obtain ⟨S, hS0, hS⟩ := (moll_ker_compact n).exists_bound_iteratedFDeriv (𝕜 := ℝ)
    (moll_ker_contDiff n) k
  refine ⟨M0 * S * (volume (Metric.ball (0 : Euc d) (r + 1))).toReal, fun x₀ => ?_⟩
  set ν : Measure (Euc d) := volume.restrict (Metric.ball x₀ (r + 1)) with hν
  have : IsFiniteMeasure ν := ⟨by rw [hν, Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  set G : Euc d → Euc d → V := fun y x => mollKer d n (x - y) • F y with hG
  have hKshift : ∀ y, ContDiff ℝ (k : WithTop ℕ∞) (fun x => mollKer d n (x - y)) := fun y =>
    ((moll_ker_contDiff n).of_le (mod_cast le_top)).comp (contDiff_id.sub contDiff_const)
  have hGc : ∀ y, ContDiff ℝ (k : WithTop ℕ∞) (G y) := fun y => (hKshift y).smul contDiff_const
  have hGiter : ∀ y x i, i ≤ k → iteratedFDeriv ℝ i (G y) x =
      (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) (F y)).compContinuousMultilinearMap
        (iteratedFDeriv ℝ i (mollKer d n) (x - y)) := by
    intro y x i hi
    have := iteratedFDeriv_smul_const_apply (𝕜 := ℝ) (v := F y)
      (f := fun x => mollKer d n (x - y)) (i := i) (x := x)
      (((hKshift y).of_le (by exact_mod_cast hi)).contDiffAt)
    rw [iteratedFDeriv_comp_sub] at this
    exact this
  have hnorm : ∀ y x i, i ≤ k → ‖iteratedFDeriv ℝ i (G y) x‖ ≤ M0 * S := by
    intro y x i hi
    rw [hGiter y x i hi]
    refine (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans ?_
    have h1 : ‖ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) (F y)‖ ≤ M0 := by
      rw [ContinuousLinearMap.norm_smulRight_apply]
      calc ‖ContinuousLinearMap.id ℝ ℝ‖ * ‖F y‖ ≤ 1 * ‖F y‖ :=
            mul_le_mul_of_nonneg_right ContinuousLinearMap.norm_id_le (norm_nonneg _)
        _ ≤ M0 := by rw [one_mul]; exact hb y
    exact mul_le_mul h1 (hS i hi _) (norm_nonneg _) ((norm_nonneg _).trans h1)
  have hbd : ∀ i ≤ k, ∃ M' : ℝ, ∀ y x, ‖iteratedFDeriv ℝ i (G y) x‖ ≤ M' := fun i hi =>
    ⟨M0 * S, fun y x => hnorm y x i hi⟩
  have hmeas : ∀ i ≤ k, ∀ x, AEStronglyMeasurable (fun y => iteratedFDeriv ℝ i (G y) x) ν := by
    intro i hi x
    have : (fun y => iteratedFDeriv ℝ i (G y) x) = fun y =>
        (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) (F y)).compContinuousMultilinearMap
          (iteratedFDeriv ℝ i (mollKer d n) (x - y)) := funext fun y => hGiter y x i hi
    rw [this]
    refine Continuous.aestronglyMeasurable ?_
    have hc1 : Continuous fun y => ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) (F y) :=
      ((ContinuousLinearMap.smulRightL ℝ ℝ V (ContinuousLinearMap.id ℝ ℝ)).continuous.comp hF)
    have hc2 : Continuous fun y => iteratedFDeriv ℝ i (mollKer d n) (x - y) :=
      ((moll_ker_contDiff n).continuous_iteratedFDeriv (mod_cast le_top)).comp
        (continuous_const.sub continuous_id)
    exact (isBoundedBilinearMap_compMultilinear (𝕜 := ℝ)
      (E := fun _ : Fin i => Euc d) (F := ℝ) (G := V)).continuous.comp (hc1.prodMk hc2)
  have hev : mollify n F =ᶠ[𝓝 x₀] fun x => ∫ y, G y x ∂ν := by
    filter_upwards [Metric.ball_mem_nhds x₀ one_pos] with x hx
    rw [moll_eq_convolution, convolution_lsmul_swap]
    rw [hν]
    symm
    refine setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => ?_)
    have hy' : r + 1 ≤ ‖y - x₀‖ := by
      simpa [Metric.mem_ball, dist_eq_norm] using hy
    have hx' : ‖x - x₀‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hx
    have : r ≤ ‖x - y‖ := by
      have h3 : ‖y - x₀‖ ≤ ‖x - y‖ + ‖x - x₀‖ := by
        calc ‖y - x₀‖ = ‖-(x - y) + (x - x₀)‖ := by congr 1; abel
          _ ≤ ‖-(x - y)‖ + ‖x - x₀‖ := norm_add_le _ _
          _ = ‖x - y‖ + ‖x - x₀‖ := by rw [norm_neg]
      linarith
    show mollKer d n (x - y) • F y = 0
    rw [moll_ker_zero n this, zero_smul]
  obtain ⟨-, hform⟩ := sg_iteratedFDeriv_integral (μ := ν) G k hGc hbd hmeas
  rw [(Filter.EventuallyEq.iteratedFDeriv ℝ hev k).eq_of_nhds, hform k le_rfl x₀]
  refine (norm_integral_le_of_norm_le_const (ae_of_all _ fun y => hnorm y x₀ k le_rfl)).trans ?_
  have : ν.real Set.univ = (volume (Metric.ball (0 : Euc d) (r + 1))).toReal := by
    rw [Measure.real, hν, Measure.restrict_apply_univ, Measure.addHaar_ball_center]
  rw [this]

end Mollify

end HRS.MS.PoisMoll
