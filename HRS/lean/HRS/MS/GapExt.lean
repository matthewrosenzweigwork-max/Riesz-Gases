import HRS.MS.GapPoincAux1
import HRS.MS.GapRefAux2
import HRS.Whole.Thermal

/-!
# GAP-4: extension of the Poincare inequality to `C^1` functions, assembly of `reflection_gap_poincare`

Supplement foundation packet GAP-4 (`docs/S4_PLAN.md`, section 2.4, steps 6 and 7; row S4.9).  Namespace
`HRS.MS.Gap`, helper prefix `gap234_`.

* `gap_ext`: for `GapRef d ρ q B` (`μ = ρ dx`), `q > 0`, `B ∈ C_b^2`, there is `c > 0` such that every `f ∈ C^1`
  with bounded gradient and `f ∈ L²(μ)` satisfies `c Var_μ f ≤ ∫ ‖∇f‖² dμ`.
  Route: (A) for `h ∈ C^1` bounded with bounded gradient, the mollifications `h_n = η_n * h`
  (`η_n = invBump n` normalised, `PoisInvAux1.invMoll`) lie in the bounded `C²` class `gap234_Sm`
  (`‖D h_n‖ ≤ ‖Dh‖_∞`, `D² h_n` bounded because `D²(h * η) = h * D²η` for bounded `h`), so the smooth inequality
  `gap_smooth_const` (applied to `h_n - ∫ h_n`) gives it for `h_n`; `h_n → h`, `∇h_n → ∇h` pointwise with uniform
  bounds, so dominated convergence passes to the limit.  (B) for general `f`, the truncations
  `n sin(f/n)` are bounded `C^1` with `‖∇‖ ≤ ‖∇f‖_∞`, converge to `f` pointwise with `|n sin(f/n)| ≤ |f|`, and
  dominated convergence passes to the limit again.
* `reflection_gap_poincare_proof : type_of% @HRS.Whole.reflection_gap_poincare` (the frozen S4.9 statement).

Statement adjustments relative to the plan sketch (documented, harmless): the truncation is `n sin(f/n)` (bounded,
`1`-Lipschitz, `n sin(y/n) → y`) and the mollification is applied to the truncated function (so that the second
derivative of the mollification is bounded by `‖h‖_∞ ∫‖D²η‖`); the variance is handled through the formula
`Var f = ∫ f² - (∫ f)²` (`ProbabilityTheory.variance_eq_sub`).
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff ENNReal NNReal Interval Convolution
open HRS HRS.Whole HRS.MS.PoisInv

noncomputable section

namespace HRS.MS.Gap

variable {d : ℕ}

/-! ### Differentiation of convolutions with a compactly supported kernel -/

/-- Derivative of `x ↦ ∫ η s * h(x - s) ds` for `h ∈ C^1` with bounded derivative (derivative on `h`). -/
theorem gap234_conv_hasFDerivAt_right {η h : Euc d → ℝ} (hη : Continuous η)
    (hηc : HasCompactSupport η) (hh : ContDiff ℝ 1 h) {C : ℝ} (hC : ∀ y, ‖fderiv ℝ h y‖ ≤ C)
    (x₀ : Euc d) :
    HasFDerivAt (fun x => ∫ s, η s * h (x - s)) (∫ s, η s • fderiv ℝ h (x₀ - s)) x₀ := by
  have hhc : Continuous h := hh.continuous
  have hfd : Continuous (fderiv ℝ h) := hh.continuous_fderiv one_ne_zero
  have hdiff : ∀ x : Euc d, ∀ s : Euc d,
      HasFDerivAt (fun x => η s * h (x - s)) (η s • fderiv ℝ h (x - s)) x := by
    intro x s
    have h1 : HasFDerivAt (fun x : Euc d => x - s) (ContinuousLinearMap.id ℝ (Euc d)) x :=
      (hasFDerivAt_id x).sub_const s
    have h2 := (hh.differentiable one_ne_zero (x - s)).hasFDerivAt.comp x h1
    have h3 := h2.const_mul (η s)
    simpa using h3
  have hint : Integrable (fun s => |η s| * C) volume :=
    (hη.integrable_of_hasCompactSupport hηc).abs.mul_const C
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (μ := volume) (s := univ)
    (F := fun (x : Euc d) (s : Euc d) => η s * h (x - s))
    (F' := fun (x : Euc d) (s : Euc d) => η s • fderiv ℝ h (x - s)) (x₀ := x₀)
    (bound := fun s => |η s| * C) Filter.univ_mem ?_ ?_ ?_ ?_ hint ?_
  · exact Eventually.of_forall fun x =>
      (hη.mul (hhc.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  · exact (hη.mul (hhc.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      (hηc.mul_right)
  · exact (hη.smul (hfd.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  · refine ae_of_all _ fun s x _ => ?_
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hC _) (abs_nonneg _)
  · exact ae_of_all _ fun s x _ => hdiff x s

/-- Derivative of `x ↦ ∫ h t • κ(x - t) dt` for a bounded continuous `h` and a `C^1` compactly supported kernel
`κ` (derivative on the kernel). -/
theorem gap234_conv_hasFDerivAt_left {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] {κ : Euc d → V} (hκ : ContDiff ℝ 1 κ) (hκc : HasCompactSupport κ)
    {h : Euc d → ℝ} (hh : Continuous h) {M : ℝ} (hM : ∀ t, |h t| ≤ M) (x₀ : Euc d) :
    HasFDerivAt (fun x => ∫ t, h t • κ (x - t)) (∫ t, h t • fderiv ℝ κ (x₀ - t)) x₀ := by
  have hκ0 : Continuous κ := hκ.continuous
  have hfd : Continuous (fderiv ℝ κ) := hκ.continuous_fderiv one_ne_zero
  obtain ⟨R, hR⟩ := hκc.isCompact.isBounded.subset_closedBall (0 : Euc d)
  obtain ⟨K, hK⟩ := hfd.bounded_above_of_compact_support (hκc.fderiv ℝ)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  set S : Set (Euc d) := Metric.closedBall x₀ (R + 1) with hS
  have hSm : MeasurableSet S := measurableSet_closedBall
  have hbint : Integrable (fun t => S.indicator (fun _ => M * K) t) volume :=
    (integrable_indicator_iff hSm).2 (integrableOn_const (measure_closedBall_lt_top.ne))
  have hdiff : ∀ x : Euc d, ∀ t : Euc d,
      HasFDerivAt (fun x => h t • κ (x - t)) (h t • fderiv ℝ κ (x - t)) x := by
    intro x t
    have h1 : HasFDerivAt (fun x : Euc d => x - t) (ContinuousLinearMap.id ℝ (Euc d)) x :=
      (hasFDerivAt_id x).sub_const t
    have h2 := (hκ.differentiable one_ne_zero (x - t)).hasFDerivAt.comp x h1
    have h3 := h2.const_smul (h t)
    convert h3 using 1 <;> first | rfl | simp
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (μ := volume)
    (s := Metric.ball x₀ 1)
    (F := fun (x : Euc d) (t : Euc d) => h t • κ (x - t))
    (F' := fun (x : Euc d) (t : Euc d) => h t • fderiv ℝ κ (x - t)) (x₀ := x₀)
    (bound := fun t => S.indicator (fun _ => M * K) t) (Metric.ball_mem_nhds x₀ one_pos) ?_ ?_ ?_ ?_
    hbint ?_
  · exact Eventually.of_forall fun x =>
      (hh.smul (hκ0.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  · exact (hh.smul (hκ0.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      (by
        have : HasCompactSupport (fun t : Euc d => κ (x₀ - t)) := by
          have := hκc.comp_homeomorph ((Homeomorph.neg (Euc d)).trans (Homeomorph.addLeft x₀))
          simpa [Function.comp_def, sub_eq_add_neg] using this
        exact this.smul_left)
  · exact (hh.smul (hfd.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  · refine ae_of_all _ fun t x hx => ?_
    by_cases ht : t ∈ S
    · rw [Set.indicator_of_mem ht, norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (hM t) (hK _) (norm_nonneg _) hM0
    · rw [Set.indicator_of_notMem ht]
      have hxt : x - t ∉ tsupport κ := by
        intro hmem
        have h1 := hR hmem
        rw [mem_closedBall_zero_iff] at h1
        apply ht
        rw [hS, Metric.mem_closedBall, dist_eq_norm]
        have hx' : ‖x - x₀‖ < 1 := by simpa [dist_eq_norm] using hx
        calc ‖t - x₀‖ = ‖(x - x₀) - (x - t)‖ := by congr 1; abel
          _ ≤ ‖x - x₀‖ + ‖x - t‖ := norm_sub_le _ _
          _ ≤ R + 1 := by linarith
      rw [fderiv_of_notMem_tsupport ℝ hxt]
      simp
  · exact ae_of_all _ fun t x _ => hdiff x t

theorem gap234_int_norm_fderiv {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {κ : Euc d → V}
    (hκ : ContDiff ℝ 1 κ) (hc : HasCompactSupport κ) : Integrable (fun x => ‖fderiv ℝ κ x‖) :=
  ((hκ.continuous_fderiv one_ne_zero).norm).integrable_of_hasCompactSupport (hc.fderiv ℝ).norm

/-! ### The mollifiers -/

/-- The normalised mollifier of radius `1/(n+1)`. -/
def gap234_eta (d n : ℕ) : Euc d → ℝ := (invBump (d := d) n).normed volume

theorem gap234_eta_nonneg (n : ℕ) (x : Euc d) : 0 ≤ gap234_eta d n x :=
  (invBump (d := d) n).nonneg_normed x

theorem gap234_eta_integral (n : ℕ) : ∫ x, gap234_eta d n x = 1 :=
  (invBump (d := d) n).integral_normed

theorem gap234_eta_cont (n : ℕ) : Continuous (gap234_eta d n) :=
  (invBump (d := d) n).continuous_normed

theorem gap234_eta_smooth (n : ℕ) : ContDiff ℝ ∞ (gap234_eta d n) :=
  (invBump (d := d) n).contDiff_normed

theorem gap234_eta_compact (n : ℕ) : HasCompactSupport (gap234_eta d n) :=
  (invBump (d := d) n).hasCompactSupport_normed

theorem gap234_eta_int (n : ℕ) : Integrable (gap234_eta d n) :=
  (gap234_eta_cont n).integrable_of_hasCompactSupport (gap234_eta_compact n)

theorem gap234_invMoll_eq (n : ℕ) (h : Euc d → ℝ) (x : Euc d) :
    invMoll n h x = ∫ s, gap234_eta d n s * h (x - s) := by
  simp [invMoll, convolution_def, gap234_eta]

theorem gap234_invMoll_eq' (n : ℕ) (h : Euc d → ℝ) (x : Euc d) :
    invMoll n h x = ∫ t, h t • gap234_eta d n (x - t) := by
  rw [gap234_invMoll_eq]
  have := integral_sub_left_eq_self (fun s => gap234_eta d n s * h (x - s)) volume x
  simp only [sub_sub_cancel] at this
  rw [← this]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  simp [mul_comm]

theorem gap234_moll_fderiv {h : Euc d → ℝ} (hh : ContDiff ℝ 1 h) {C : ℝ}
    (hC : ∀ y, ‖fderiv ℝ h y‖ ≤ C) (n : ℕ) (x : Euc d) :
    fderiv ℝ (invMoll n h) x = ∫ s, gap234_eta d n s • fderiv ℝ h (x - s) := by
  have := gap234_conv_hasFDerivAt_right (gap234_eta_cont n) (gap234_eta_compact n) hh hC x
  have e : invMoll n h = fun x => ∫ s, gap234_eta d n s * h (x - s) :=
    funext (gap234_invMoll_eq n h)
  rw [e]
  exact this.fderiv

theorem gap234_moll_fderiv_bound {h : Euc d → ℝ} (hh : ContDiff ℝ 1 h) {C : ℝ}
    (hC : ∀ y, ‖fderiv ℝ h y‖ ≤ C) (n : ℕ) (x : Euc d) : ‖fderiv ℝ (invMoll n h) x‖ ≤ C := by
  rw [gap234_moll_fderiv hh hC n x]
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hint : Integrable (fun s => gap234_eta d n s * C) := (gap234_eta_int n).mul_const C
  refine (norm_integral_le_of_norm_le hint (ae_of_all _ fun s => ?_)).trans (le_of_eq ?_)
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (gap234_eta_nonneg n s)]
    exact mul_le_mul_of_nonneg_left (hC _) (gap234_eta_nonneg n s)
  · rw [integral_mul_const, gap234_eta_integral, one_mul]

theorem gap234_moll_fderiv_tendsto {h : Euc d → ℝ} (hh : ContDiff ℝ 1 h) {C : ℝ}
    (hC : ∀ y, ‖fderiv ℝ h y‖ ≤ C) (x : Euc d) :
    Tendsto (fun n : ℕ => fderiv ℝ (invMoll n h) x) atTop (𝓝 (fderiv ℝ h x)) := by
  have hfd : Continuous (fderiv ℝ h) := hh.continuous_fderiv one_ne_zero
  have := ContDiffBump.convolution_tendsto_right_of_continuous
    (φ := fun n : ℕ => invBump (d := d) n) (μ := volume) (l := atTop) (g := fderiv ℝ h) ?_ hfd x
  · refine this.congr (fun n => ?_)
    rw [gap234_moll_fderiv hh hC n x]
    simp [convolution_def, gap234_eta]
  · show Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0)
    exact tendsto_one_div_add_atTop_nhds_zero_nat

/-- The second derivative of a mollification of a bounded `C^1` function with bounded gradient is bounded
(`D(η * h) = h * Dη` is Lipschitz because `h` is). -/
theorem gap234_moll_second_bound {h : Euc d → ℝ} (hh : ContDiff ℝ 1 h) {M C : ℝ}
    (hM : ∀ t, |h t| ≤ M) (hC : ∀ y, ‖fderiv ℝ h y‖ ≤ C) (n : ℕ) (x : Euc d) :
    ‖fderiv ℝ (fderiv ℝ (invMoll n h)) x‖ ≤ C * ∫ s, ‖fderiv ℝ (gap234_eta d n) s‖ := by
  have hη := gap234_eta_smooth (d := d) n
  have hη1 : ContDiff ℝ 1 (gap234_eta d n) := hη.of_le (by norm_num)
  have hc : Continuous h := hh.continuous
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hfd : Continuous (fderiv ℝ (gap234_eta d n)) := hη1.continuous_fderiv one_ne_zero
  have hcs : HasCompactSupport (fderiv ℝ (gap234_eta d n)) := (gap234_eta_compact n).fderiv ℝ
  have hint : Integrable (fun s => ‖fderiv ℝ (gap234_eta d n) s‖) := gap234_int_norm_fderiv hη1 (gap234_eta_compact n)
  have hI0 : 0 ≤ ∫ s, ‖fderiv ℝ (gap234_eta d n) s‖ := integral_nonneg fun s => norm_nonneg _
  have s1 : ∀ x, HasFDerivAt (invMoll n h) (∫ t, h t • fderiv ℝ (gap234_eta d n) (x - t)) x := by
    intro x
    have := gap234_conv_hasFDerivAt_left (V := ℝ) hη1 (gap234_eta_compact n) hc hM x
    have e : invMoll n h = fun x => ∫ t, h t • gap234_eta d n (x - t) :=
      funext (gap234_invMoll_eq' n h)
    rw [e]
    exact this
  have hD : ∀ x, fderiv ℝ (invMoll n h) x = ∫ s, h (x - s) • fderiv ℝ (gap234_eta d n) s := by
    intro x
    rw [(s1 x).fderiv]
    have := integral_sub_left_eq_self (fun s => h (x - s) • fderiv ℝ (gap234_eta d n) s) volume x
    simp only [sub_sub_cancel] at this
    exact this
  have hI : ∀ x, Integrable (fun s => h (x - s) • fderiv ℝ (gap234_eta d n) s) := fun x =>
    ((hc.comp (continuous_const.sub continuous_id)).smul hfd).integrable_of_hasCompactSupport hcs.smul_left
  have hlipf : ∀ a b : Euc d, |h a - h b| ≤ C * ‖a - b‖ := fun a b => by
    have := (convex_univ (𝕜 := ℝ) (E := Euc d)).norm_image_sub_le_of_norm_fderiv_le
      (f := h) (C := C) (fun z _ => (hh.differentiable one_ne_zero) z) (fun z _ => hC z)
      (mem_univ b) (mem_univ a)
    rwa [Real.norm_eq_abs] at this
  have hlip : LipschitzWith (Real.toNNReal (C * ∫ s, ‖fderiv ℝ (gap234_eta d n) s‖))
      (fderiv ℝ (invMoll n h)) := by
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    rw [dist_eq_norm, dist_eq_norm, hD a, hD b, ← integral_sub (hI a) (hI b),
      Real.coe_toNNReal _ (mul_nonneg hC0 hI0)]
    have hb : Integrable (fun s => (C * ‖a - b‖) * ‖fderiv ℝ (gap234_eta d n) s‖) := hint.const_mul _
    refine (norm_integral_le_of_norm_le hb (ae_of_all _ fun s => ?_)).trans (le_of_eq ?_)
    · rw [← sub_smul, norm_smul, Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      have := hlipf (a - s) (b - s)
      simpa [sub_sub_sub_cancel_right] using this
    · rw [integral_const_mul]; ring
  exact (norm_fderiv_le_of_lipschitz ℝ hlip).trans (by rw [Real.coe_toNNReal _ (mul_nonneg hC0 hI0)])

/-- The mollifications of a bounded `C^1` function with bounded gradient lie in the bounded `C²` class. -/
theorem gap234_moll_sm {h : Euc d → ℝ} (hh : ContDiff ℝ 1 h) {Mh C : ℝ} (hM : ∀ t, |h t| ≤ Mh)
    (hC : ∀ y, ‖fderiv ℝ h y‖ ≤ C) (n : ℕ) :
    ∃ M : ℝ, gap234_Sm M (invMoll n h) := by
  have hM2 := gap234_moll_second_bound hh hM hC n
  have hMh : 0 ≤ Mh := (abs_nonneg _).trans (hM 0)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  refine ⟨max (max (3 * Mh) C) (C * ∫ s, ‖fderiv ℝ (gap234_eta d n) s‖), gap234_sm_of_bounds ?_ (fun y => ?_) (fun y => ?_) (fun y => ?_)⟩
  · exact (inv_moll_contDiff n hh.continuous).of_le (by norm_num)
  · rw [Real.norm_eq_abs]
    exact (inv_conv_bound n hh.continuous hM y).trans ((le_max_left _ _).trans (le_max_left _ _))
  · exact (gap234_moll_fderiv_bound hh hC n y).trans ((le_max_right _ _).trans (le_max_left _ _))
  · exact (hM2 y).trans (le_max_right _ _)


/-! ### Passage to the limit -/

theorem gap234_memLp_of_bound {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {u D : Euc d → ℝ}
    (hu : Continuous u) (hD2 : Integrable (fun x => D x ^ 2) μ) (hbd : ∀ x, |u x| ≤ D x) :
    MemLp u 2 μ := by
  refine (memLp_two_iff_integrable_sq hu.aestronglyMeasurable).2 ?_
  refine hD2.mono' (hu.pow 2).aestronglyMeasurable (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_pow, sq_abs]
  exact sq_le_sq.2 ((hbd x).trans (le_abs_self _))

theorem gap234_var_eq {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {u : Euc d → ℝ}
    (hu : MemLp u 2 μ) :
    ProbabilityTheory.variance u μ = ∫ x, u x ^ 2 ∂μ - (∫ x, u x ∂μ) ^ 2 := by
  rw [ProbabilityTheory.variance_eq_sub hu]
  rfl

/-- Closure of the Poincare inequality under pointwise limits with `L²`-domination. -/
theorem gap234_limit {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {c : ℝ} {f : Euc d → ℝ}
    {u : ℕ → Euc d → ℝ} (hf : ContDiff ℝ 1 f) (hu : ∀ n, ContDiff ℝ 1 (u n)) {D : Euc d → ℝ}
    (hDc : Continuous D) (hD2 : Integrable (fun x => D x ^ 2) μ) (hbd : ∀ n x, |u n x| ≤ D x)
    (hfD : ∀ x, |f x| ≤ D x) (hlim : ∀ x, Tendsto (fun n => u n x) atTop (𝓝 (f x))) {Cg : ℝ}
    (hgbd : ∀ n x, ‖gradient (u n) x‖ ≤ Cg)
    (hglim : ∀ x, Tendsto (fun n => gradient (u n) x) atTop (𝓝 (gradient f x)))
    (hQ : ∀ n, c * ProbabilityTheory.variance (u n) μ ≤ ∫ x, ‖gradient (u n) x‖ ^ 2 ∂μ) :
    c * ProbabilityTheory.variance f μ ≤ ∫ x, ‖gradient f x‖ ^ 2 ∂μ := by
  have hD0 : ∀ x, 0 ≤ D x := fun x => (abs_nonneg _).trans (hfD x)
  have hD1 : Integrable D μ := by
    refine ((integrable_const (1 : ℝ)).add hD2).mono' hDc.aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hD0 x)]
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (D x - 1)]
  have hmu : ∀ n, MemLp (u n) 2 μ := fun n =>
    gap234_memLp_of_bound (hu n).continuous hD2 (hbd n)
  have hmf : MemLp f 2 μ := gap234_memLp_of_bound hf.continuous hD2 hfD
  have T1 : Tendsto (fun n => ∫ x, u n x ^ 2 ∂μ) atTop (𝓝 (∫ x, f x ^ 2 ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => D x ^ 2)
      (fun n => ((hu n).continuous.pow 2).aestronglyMeasurable) hD2 (fun n => ae_of_all _ fun x => ?_)
      (ae_of_all _ fun x => (hlim x).pow 2)
    rw [Real.norm_eq_abs, abs_pow, sq_abs]
    exact sq_le_sq.2 ((hbd n x).trans (le_abs_self _))
  have T2 : Tendsto (fun n => ∫ x, u n x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence D
      (fun n => (hu n).continuous.aestronglyMeasurable) hD1 (fun n => ae_of_all _ fun x => ?_)
      (ae_of_all _ hlim)
    rw [Real.norm_eq_abs]; exact hbd n x
  have T3 : Tendsto (fun n => ∫ x, ‖gradient (u n) x‖ ^ 2 ∂μ) atTop
      (𝓝 (∫ x, ‖gradient f x‖ ^ 2 ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => Cg ^ 2)
      (fun n => ((gap1_grad_continuous (hu n)).norm.pow 2).aestronglyMeasurable)
      (integrable_const _) (fun n => ae_of_all _ fun x => ?_)
      (ae_of_all _ fun x => (hglim x).norm.pow 2)
    rw [Real.norm_eq_abs, abs_pow, sq_abs]
    exact pow_le_pow_left₀ (norm_nonneg _) (hgbd n x) 2
  have hL : Tendsto (fun n => c * ProbabilityTheory.variance (u n) μ) atTop
      (𝓝 (c * ProbabilityTheory.variance f μ)) := by
    have : ∀ n, ProbabilityTheory.variance (u n) μ = ∫ x, u n x ^ 2 ∂μ - (∫ x, u n x ∂μ) ^ 2 :=
      fun n => gap234_var_eq (hmu n)
    simp_rw [this, gap234_var_eq hmf]
    exact (T1.sub (T2.pow 2)).const_mul c
  exact le_of_tendsto_of_tendsto' hL T3 hQ

/-! ### The inequality on the bounded `C²` class, with variance -/

theorem gap234_smooth_var {q : ℝ} {B : Euc d → Euc d} {ρ : Euc d → ℝ} (hR : GapRef d ρ q B)
    {c : ℝ}
    (hc : ∀ {f : Euc d → ℝ} {M : ℝ}, gap234_Sm M f → ∫ x, f x ∂(HRS.Whole.withDensityReal ρ) = 0 →
      c * ∫ x, f x ^ 2 ∂(HRS.Whole.withDensityReal ρ) ≤
        ∫ x, ‖gradient f x‖ ^ 2 ∂(HRS.Whole.withDensityReal ρ))
    {f : Euc d → ℝ} {M : ℝ} (hf : gap234_Sm M f) :
    c * ProbabilityTheory.variance f (HRS.Whole.withDensityReal ρ) ≤
      ∫ x, ‖gradient f x‖ ^ 2 ∂(HRS.Whole.withDensityReal ρ) := by
  have : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) := gap1_isProb hR
  set m : ℝ := ∫ x, f x ∂(HRS.Whole.withDensityReal ρ) with hm
  have hfi : Integrable f (HRS.Whole.withDensityReal ρ) :=
    (integrable_const M).mono' hf.1.continuous.aestronglyMeasurable
      (ae_of_all _ fun x => gap234_sm_zero hf x)
  have hfd : fderiv ℝ (fun x => f x - m) = fderiv ℝ f := by
    funext x; exact fderiv_sub_const m
  have hg : gap234_Sm (M + |m|) (fun x => f x - m) := by
    have hM0 := gap234_sm_nonneg hf
    refine gap234_sm_of_bounds (hf.1.sub contDiff_const) (fun y => ?_) (fun y => ?_) (fun y => ?_)
    · rw [Real.norm_eq_abs]
      have := gap234_sm_zero hf y
      rw [Real.norm_eq_abs] at this
      calc |f y - m| ≤ |f y| + |m| := abs_sub _ _
        _ ≤ M + |m| := by linarith
    · rw [hfd]; have := gap234_sm_one hf y; linarith [abs_nonneg m]
    · rw [hfd]; have := gap234_sm_two hf y; linarith [abs_nonneg m]
  have hcen : ∫ x, (f x - m) ∂(HRS.Whole.withDensityReal ρ) = 0 := by
    rw [integral_sub hfi (integrable_const m)]
    simp [hm]
  have h1 := hc hg hcen
  have hgrad : ∀ x, gradient (fun x => f x - m) x = gradient f x := fun x => by
    unfold gradient; rw [hfd]
  simp_rw [hgrad] at h1
  have hv : ProbabilityTheory.variance f (HRS.Whole.withDensityReal ρ) =
      ∫ x, (f x - m) ^ 2 ∂(HRS.Whole.withDensityReal ρ) :=
    ProbabilityTheory.variance_eq_integral hf.1.continuous.aemeasurable
  rw [hv]
  exact h1

/-! ### Stage A: bounded `C^1` functions with bounded gradient -/

theorem gap234_stageA {q : ℝ} {B : Euc d → Euc d} {ρ : Euc d → ℝ} (hR : GapRef d ρ q B) {c : ℝ}
    (hc : ∀ {f : Euc d → ℝ} {M : ℝ}, gap234_Sm M f → ∫ x, f x ∂(HRS.Whole.withDensityReal ρ) = 0 →
      c * ∫ x, f x ^ 2 ∂(HRS.Whole.withDensityReal ρ) ≤
        ∫ x, ‖gradient f x‖ ^ 2 ∂(HRS.Whole.withDensityReal ρ))
    {h : Euc d → ℝ} (hh : ContDiff ℝ 1 h) {Mh C : ℝ} (hM : ∀ t, |h t| ≤ Mh)
    (hC : ∀ y, ‖fderiv ℝ h y‖ ≤ C) :
    c * ProbabilityTheory.variance h (HRS.Whole.withDensityReal ρ) ≤
      ∫ x, ‖gradient h x‖ ^ 2 ∂(HRS.Whole.withDensityReal ρ) := by
  have : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) := gap1_isProb hR
  have hMh : 0 ≤ Mh := (abs_nonneg _).trans (hM 0)
  have hsm : ∀ n, ContDiff ℝ 1 (invMoll n h) := fun n =>
    (inv_moll_contDiff n hh.continuous).of_le (by norm_num)
  refine gap234_limit (u := fun n => invMoll n h) (D := fun _ => 3 * Mh) (Cg := C) hh hsm
    continuous_const (integrable_const _) (fun n x => ?_) (fun x => ?_) (fun x => ?_)
    (fun n x => ?_) (fun x => ?_) (fun n => ?_)
  · exact (inv_conv_bound n hh.continuous hM x)
  · exact (hM x).trans (by linarith)
  · exact inv_conv_tendsto hh.continuous x
  · rw [gap1_norm_grad]; exact gap234_moll_fderiv_bound hh hC n x
  · have := gap234_moll_fderiv_tendsto hh hC x
    unfold gradient
    exact ((InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.tendsto _).comp this
  · obtain ⟨M, hMsm⟩ := gap234_moll_sm hh hM hC n
    exact gap234_smooth_var hR hc hMsm

/-! ### Stage B: general `C^1` functions with bounded gradient in `L²` -/

theorem gap234_sin_sub (z : ℝ) (hz : |z| ≤ 1) : |Real.sin z - z| ≤ |z| ^ 3 := by
  have h := Real.sin_bound hz
  have h1 : |z| ^ 5 ≤ |z| ^ 3 := pow_le_pow_of_le_one (abs_nonneg _) hz (by norm_num)
  have h2 : |Real.sin z - z| ≤ |Real.sin z - (z - z ^ 3 / 6)| + |z ^ 3 / 6| := by
    have : Real.sin z - z = (Real.sin z - (z - z ^ 3 / 6)) + (-(z ^ 3 / 6)) := by ring
    rw [this]
    calc _ ≤ |Real.sin z - (z - z ^ 3 / 6)| + |-(z ^ 3 / 6)| := abs_add_le _ _
      _ = _ := by rw [abs_neg]
  have h3 : |z ^ 3 / 6| = |z| ^ 3 / 6 := by rw [abs_div, abs_pow]; norm_num
  have h0 : 0 ≤ |z| ^ 3 := by positivity
  linarith

theorem gap234_trunc_tendsto (a : ℝ) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) * Real.sin (a / ((n : ℝ) + 1))) atTop (𝓝 a) := by
  have hdiff : ∀ᶠ n : ℕ in atTop, |((n : ℝ) + 1) * Real.sin (a / ((n : ℝ) + 1)) - a| ≤
      |a| ^ 3 / ((n : ℝ) + 1) ^ 2 := by
    obtain ⟨N, hN⟩ := exists_nat_gt |a|
    filter_upwards [eventually_ge_atTop N] with n hn
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hle : |a| ≤ (n : ℝ) + 1 := by
      have : (N : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have hz : |a / ((n : ℝ) + 1)| ≤ 1 := by
      rw [abs_div, abs_of_pos hpos, div_le_one hpos]; exact hle
    have h1 := gap234_sin_sub _ hz
    have e : ((n : ℝ) + 1) * Real.sin (a / ((n : ℝ) + 1)) - a =
        ((n : ℝ) + 1) * (Real.sin (a / ((n : ℝ) + 1)) - a / ((n : ℝ) + 1)) := by
      field_simp
    rw [e, abs_mul, abs_of_pos hpos]
    calc ((n : ℝ) + 1) * |Real.sin (a / ((n : ℝ) + 1)) - a / ((n : ℝ) + 1)|
        ≤ ((n : ℝ) + 1) * |a / ((n : ℝ) + 1)| ^ 3 := mul_le_mul_of_nonneg_left h1 hpos.le
      _ = |a| ^ 3 / ((n : ℝ) + 1) ^ 2 := by
        rw [abs_div, abs_of_pos hpos]; field_simp
  have hzero : Tendsto (fun n : ℕ => |a| ^ 3 / ((n : ℝ) + 1) ^ 2) atTop (𝓝 0) := by
    refine tendsto_const_nhds.div_atTop ?_
    exact (tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have : Tendsto (fun n : ℕ => ((n : ℝ) + 1) * Real.sin (a / ((n : ℝ) + 1)) - a) atTop (𝓝 0) :=
    squeeze_zero_norm' (by simpa [Real.norm_eq_abs] using hdiff) hzero
  simpa using this.add_const a

theorem gap234_stageB {q : ℝ} {B : Euc d → Euc d} {ρ : Euc d → ℝ} (hR : GapRef d ρ q B) {c : ℝ}
    (hc : ∀ {f : Euc d → ℝ} {M : ℝ}, gap234_Sm M f → ∫ x, f x ∂(HRS.Whole.withDensityReal ρ) = 0 →
      c * ∫ x, f x ^ 2 ∂(HRS.Whole.withDensityReal ρ) ≤
        ∫ x, ‖gradient f x‖ ^ 2 ∂(HRS.Whole.withDensityReal ρ))
    {f : Euc d → ℝ} (hf : ContDiff ℝ 1 f) {Cf : ℝ} (hCf : ∀ x, ‖gradient f x‖ ≤ Cf)
    (hmem : MemLp f 2 (HRS.Whole.withDensityReal ρ)) :
    c * ProbabilityTheory.variance f (HRS.Whole.withDensityReal ρ) ≤
      ∫ x, ‖gradient f x‖ ^ 2 ∂(HRS.Whole.withDensityReal ρ) := by
  have : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) := gap1_isProb hR
  set u : ℕ → Euc d → ℝ := fun n x => ((n : ℝ) + 1) * Real.sin (f x / ((n : ℝ) + 1)) with hu
  have hpos : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  have hu1 : ∀ n, ContDiff ℝ 1 (u n) := fun n =>
    contDiff_const.mul (Real.contDiff_sin.comp (hf.div_const _))
  have hfd : ∀ n x, fderiv ℝ (u n) x = Real.cos (f x / ((n : ℝ) + 1)) • fderiv ℝ f x := by
    intro n x
    have h0 := (hf.differentiable one_ne_zero x).hasFDerivAt.const_mul (((n : ℝ) + 1)⁻¹)
    have h1 := h0.sin
    have h2 := h1.const_mul ((n : ℝ) + 1)
    have e : u n = fun y => ((n : ℝ) + 1) * Real.sin (((n : ℝ) + 1)⁻¹ * f y) := by
      funext y; simp [hu, div_eq_inv_mul]
    rw [e, h2.fderiv]
    have e2 : f x / ((n : ℝ) + 1) = ((n : ℝ) + 1)⁻¹ * f x := by rw [div_eq_inv_mul]
    rw [e2]
    rw [smul_smul, smul_smul]
    congr 1
    field_simp [(hpos n).ne']
  have hgr : ∀ n x, gradient (u n) x = Real.cos (f x / ((n : ℝ) + 1)) • gradient f x := by
    intro n x
    unfold gradient
    rw [hfd, map_smul]
  have hbdu : ∀ n x, |u n x| ≤ |f x| := by
    intro n x
    simp only [hu]
    rw [abs_mul, abs_of_pos (hpos n)]
    calc ((n : ℝ) + 1) * |Real.sin (f x / ((n : ℝ) + 1))|
        ≤ ((n : ℝ) + 1) * |f x / ((n : ℝ) + 1)| :=
          mul_le_mul_of_nonneg_left Real.abs_sin_le_abs (hpos n).le
      _ = |f x| := by rw [abs_div, abs_of_pos (hpos n)]; field_simp
  have hf2 : Integrable (fun x => |f x| ^ 2) (HRS.Whole.withDensityReal ρ) := by
    have := hmem.integrable_sq
    simpa [sq_abs] using this
  refine gap234_limit (u := u) (D := fun x => |f x|) (Cg := Cf) hf hu1 hf.continuous.abs hf2
    hbdu (fun x => le_rfl) (fun x => gap234_trunc_tendsto (f x)) (fun n x => ?_) (fun x => ?_)
    (fun n => ?_)
  · rw [hgr, norm_smul, Real.norm_eq_abs]
    calc |Real.cos _| * ‖gradient f x‖ ≤ 1 * ‖gradient f x‖ :=
          mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (norm_nonneg _)
      _ ≤ Cf := by rw [one_mul]; exact hCf x
  · have hz : Tendsto (fun n : ℕ => f x / ((n : ℝ) + 1)) atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (f x)
      simpa [div_eq_mul_inv] using this
    have hcos : Tendsto (fun n : ℕ => Real.cos (f x / ((n : ℝ) + 1))) atTop (𝓝 1) := by
      have := (Real.continuous_cos.tendsto 0).comp hz
      rw [Real.cos_zero] at this
      exact this
    simp_rw [hgr]
    simpa using hcos.smul_const (gradient f x)
  · have hb : ∀ t, |u n t| ≤ ((n : ℝ) + 1) := fun t => by
      simp only [hu]
      rw [abs_mul, abs_of_pos (hpos n)]
      calc ((n : ℝ) + 1) * |Real.sin _| ≤ ((n : ℝ) + 1) * 1 :=
            mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (hpos n).le
        _ = _ := mul_one _
    refine gap234_stageA hR hc (hu1 n) hb (C := Cf) (fun y => ?_)
    rw [← gap1_norm_grad, hgr, norm_smul, Real.norm_eq_abs]
    calc |Real.cos _| * ‖gradient f y‖ ≤ 1 * ‖gradient f y‖ :=
          mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (norm_nonneg _)
      _ ≤ Cf := by rw [one_mul]; exact hCf y

/-- **GAP-4: extension to `C^1`.**  For `GapRef d ρ q B`, `q > 0`, `B ∈ C_b^2` there is `c > 0` such that for all
`f ∈ C^1` with bounded gradient and `f ∈ L²(μ)`, `c Var_μ f ≤ ∫ ‖∇f‖² dμ`, `μ = ρ dx`. -/
theorem gap_ext {q Mb : ℝ} {B : Euc d → Euc d} {ρ : Euc d → ℝ} (hR : GapRef d ρ q B) (hq : 0 < q)
    (hB : HasCbBound 2 Mb B) :
    ∃ c : ℝ, 0 < c ∧ ∀ f : Euc d → ℝ, ContDiff ℝ 1 f → (∃ Cf, ∀ x, ‖gradient f x‖ ≤ Cf) →
      MemLp f 2 (HRS.Whole.withDensityReal ρ) →
      c * ProbabilityTheory.variance f (HRS.Whole.withDensityReal ρ) ≤
        ∫ x, ‖gradient f x‖ ^ 2 ∂(HRS.Whole.withDensityReal ρ) := by
  obtain ⟨c, hc0, hc⟩ := gap_smooth_const hR hq hB
  exact ⟨c, hc0, fun f hf ⟨Cf, hCf⟩ hmem => gap234_stageB hR (fun {f M} hf hcen => hc hf hcen) hf hCf hmem⟩

/-- **`reflection_gap_poincare`** (S4.9): the one-body Poincare inequality for the logarithmic thermal measure and
its compact relative perturbations, for `C^1` functions with bounded gradient in `L²(μ)`. -/
theorem reflection_gap_poincare_proof : type_of% @HRS.Whole.reflection_gap_poincare := by
  intro d hd a β ha hβ ψ ρ hρ
  obtain ⟨B, hR⟩ := gap_drift hd ha hβ hρ
  obtain ⟨Mb, hB⟩ := hR.cb 2
  obtain ⟨c, hc0, hc⟩ := gap_ext hR (mul_pos ha hβ) hB
  exact ⟨c, hc0, hc⟩

end HRS.MS.Gap

end