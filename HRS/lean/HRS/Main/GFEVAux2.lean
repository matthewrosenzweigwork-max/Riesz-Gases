import Mathlib
import HRS.PDE.LinearODE

/-!
# Packet GFEVG, part 2: the abstract Hilbert-space layer (FTC lemmas, derivatives of the evolution)

Pure functional analysis, no PDE content.  `H` is a real Hilbert space, `V t u` a family of bounded operators,
`D` a dense subspace, `A s : D → H`.  From the *mild identities*

* `mild_r` : `V t u x - V t u' x = ∫_u^{u'} V t s (A s x) ds`  (`x ∈ D`, `0 ≤ u ≤ u' ≤ t`),
* `mild_t` : `V t' r x - V t r x = ∫_t^{t'} V t' s (A s (V t r x)) ds`  (`x ∈ D`, `0 ≤ r ≤ t ≤ t'`),

strong continuity, invariance of `D`, and norm continuity of `s ↦ A s x`, `s ↦ A s (V s r x)`, we derive the
derivative identities `∂_r V(t,r) x = -V(t,r) A_r x` and `∂_t V(t,r) x = A_t V(t,r) x`, the quasi-dissipativity,
and (in `GFEVAux3`) the Galerkin conjunct of `EvolData.Dissipative`.
-/

noncomputable section

open MeasureTheory Set Filter Topology intervalIntegral

namespace HRS.GF

/-! ### FTC lemmas -/

section FTC

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A function with increments given by the integral of a continuous function is differentiable within `[a,b]`. -/
theorem gfev_hasDerivWithinAt_of_increments {x f : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b))
    (hx : ∀ u ∈ Icc a b, ∀ u' ∈ Icc a b, u ≤ u' → x u' - x u = ∫ s in u..u', f s)
    {s : ℝ} (hs : s ∈ Icc a b) : HasDerivWithinAt x (f s) (Icc a b) s := by
  set f' : ℝ → E := IccExtend hab (fun t : Icc a b => f t) with hf'
  have hcont : Continuous f' := hf.domRestrict.Icc_extend'
  have hff : ∀ t ∈ Icc a b, f' t = f t := fun t ht => IccExtend_of_mem hab _ ht
  have hxa : ∀ u ∈ Icc a b, x u = x a + ∫ t in a..u, f' t := by
    intro u hu
    have h1 := hx a ⟨le_rfl, hab⟩ u hu hu.1
    have h2 : ∫ t in a..u, f' t = ∫ t in a..u, f t :=
      intervalIntegral.integral_congr fun t ht => hff t (uIcc_subset_Icc ⟨le_rfl, hab⟩ hu ht)
    rw [h2, ← h1]; abel
  have h1 : HasDerivAt (fun u => ∫ t in a..u, f' t) (f' s) s :=
    (hcont.integral_hasStrictDerivAt a s).hasDerivAt
  have h2 := (h1.const_add (x a)).hasDerivWithinAt (s := Icc a b)
  rw [hff s hs] at h2
  exact h2.congr (fun u hu => hxa u hu) (hxa s hs)

/-- Right derivatives everywhere with a continuous derivative give the two-sided derivative within `[a,b]`. -/
theorem gfev_hasDerivWithinAt_Icc_of_right {f g : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hd : ∀ t ∈ Ico a b, HasDerivWithinAt f (g t) (Ioi t) t) :
    ∀ s ∈ Icc a b, HasDerivWithinAt f (g s) (Icc a b) s := by
  intro s hs
  refine gfev_hasDerivWithinAt_of_increments hab hg ?_ hs
  intro u hu u' hu' huu'
  rcases huu'.eq_or_lt with h | h
  · subst h; simp
  · have h1 : ∫ y in u..u', g y = f u' - f u := by
      refine intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le huu'
        (hf.mono (Icc_subset_Icc hu.1 hu'.2)) (fun y hy => hd y ⟨hu.1.trans hy.1.le, hy.2.trans_le hu'.2⟩) ?_
      exact (hg.mono (uIcc_subset_Icc hu hu')).intervalIntegrable
    exact h1.symm

end FTC

/-! ### Continuity of `x ↦ V x (w x)` -/

theorem gfev_continuousOn_clm_apply {X : Type*} [TopologicalSpace X] {S : Set X} {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Vf : X → E →L[ℝ] F} {w : X → E} (hV : ∀ y, ContinuousOn (fun x => Vf x y) S)
    (M : ℝ) (hb : ∀ x ∈ S, ‖Vf x‖ ≤ M) (hw : ContinuousOn w S) :
    ContinuousOn (fun x => Vf x (w x)) S := by
  intro x₀ hx₀
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  have h1 : Tendsto (fun x => ‖w x - w x₀‖) (𝓝[S] x₀) (𝓝 0) := by
    have := hw x₀ hx₀
    rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero] at this
    exact this
  have h2 : Tendsto (fun x => ‖Vf x (w x₀) - Vf x₀ (w x₀)‖) (𝓝[S] x₀) (𝓝 0) := by
    have := hV (w x₀) x₀ hx₀
    rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero] at this
    exact this
  have h3 : Tendsto (fun x => M * ‖w x - w x₀‖ + ‖Vf x (w x₀) - Vf x₀ (w x₀)‖) (𝓝[S] x₀) (𝓝 0) := by
    simpa using (h1.const_mul M).add h2
  refine squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _) ?_ h3
  filter_upwards [self_mem_nhdsWithin] with x hx
  calc ‖Vf x (w x) - Vf x₀ (w x₀)‖
      = ‖Vf x (w x - w x₀) + (Vf x (w x₀) - Vf x₀ (w x₀))‖ := by
        rw [map_sub]; congr 1; abel
    _ ≤ ‖Vf x (w x - w x₀)‖ + ‖Vf x (w x₀) - Vf x₀ (w x₀)‖ := norm_add_le _ _
    _ ≤ M * ‖w x - w x₀‖ + ‖Vf x (w x₀) - Vf x₀ (w x₀)‖ := by
        gcongr
        exact ((Vf x).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hb x hx) (norm_nonneg _))

/-! ### The right derivative from a mild identity -/

section Right

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem gfev_rightDeriv_of_mild {x : ℝ → E} {Φ : ℝ → ℝ → E} {t T' : ℝ} (htT : t < T')
    (hΦ : ContinuousOn (fun p : ℝ × ℝ => Φ p.1 p.2) {p | t ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T'})
    (hx : ∀ t' ∈ Icc t T', x t' - x t = ∫ s in t..t', Φ t' s) :
    HasDerivWithinAt x (Φ t t) (Ioi t) t := by
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hset : Ioi t \ {t} = Ioi t := by
    ext y; simp only [Set.mem_sdiff, mem_Ioi, mem_singleton_iff]
    exact ⟨fun h => h.1, fun h => ⟨h, ne_of_gt h⟩⟩
  rw [hset, Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have hc := hΦ (t, t) ⟨le_rfl, le_rfl, htT.le⟩
  rw [ContinuousWithinAt, Metric.tendsto_nhdsWithin_nhds] at hc
  obtain ⟨δ, hδ, hδ'⟩ := hc (ε / 2) (by positivity)
  refine ⟨min δ (T' - t), lt_min hδ (by linarith), fun t' ht' hdist => ?_⟩
  have htt' : t < t' := ht'
  have hd1 : t' - t < δ := by
    have := (lt_min_iff.1 (by rwa [Real.dist_eq, abs_of_pos (by linarith : 0 < t' - t)] at hdist)).1
    exact this
  have hd2 : t' - t < T' - t := by
    have := (lt_min_iff.1 (by rwa [Real.dist_eq, abs_of_pos (by linarith : 0 < t' - t)] at hdist)).2
    exact this
  have ht'T : t' ≤ T' := by linarith
  have hslope : slope x t t' = (t' - t)⁻¹ • ∫ s in t..t', Φ t' s := by
    rw [slope_def_module, hx t' ⟨htt'.le, ht'T⟩]
  -- pointwise closeness on the segment
  have hclose : ∀ s ∈ Icc t t', ‖Φ t' s - Φ t t‖ ≤ ε / 2 := by
    intro s hs
    have hmem : (t', s) ∈ {p : ℝ × ℝ | t ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T'} := ⟨hs.1, hs.2, ht'T⟩
    have := hδ' hmem (by
      rw [Prod.dist_eq]
      refine max_lt ?_ ?_
      · rw [Real.dist_eq, abs_of_pos (by linarith : 0 < t' - t)]; exact hd1
      · rw [Real.dist_eq, abs_of_nonneg (by linarith [hs.1, hs.2])]
        linarith [hs.2])
    rw [dist_eq_norm] at this
    exact this.le
  have hint : IntervalIntegrable (fun s => Φ t' s) volume t t' := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le htt'.le]
    have hcm : ContinuousOn (fun s : ℝ => ((t', s) : ℝ × ℝ)) (Icc t t') :=
      (continuous_const.prodMk continuous_id).continuousOn
    exact hΦ.comp hcm (fun s hs => ⟨hs.1, hs.2, ht'T⟩)
  have hconst : ∫ s in t..t', Φ t t = (t' - t) • Φ t t := by simp
  have hdiff : (t' - t)⁻¹ • (∫ s in t..t', Φ t' s) - Φ t t =
      (t' - t)⁻¹ • ∫ s in t..t', (Φ t' s - Φ t t) := by
    rw [intervalIntegral.integral_sub hint intervalIntegrable_const, hconst, smul_sub, smul_smul,
      inv_mul_cancel₀ (by linarith : t' - t ≠ 0), one_smul]
  rw [dist_eq_norm, hslope, hdiff, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < t' - t)]
  have hbound : ‖∫ s in t..t', (Φ t' s - Φ t t)‖ ≤ ε / 2 * |t' - t| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun s hs => ?_
    rw [uIoc_of_le htt'.le] at hs
    exact hclose s ⟨hs.1.le, hs.2⟩
  rw [abs_of_pos (by linarith : 0 < t' - t)] at hbound
  calc (t' - t)⁻¹ * ‖∫ s in t..t', (Φ t' s - Φ t t)‖ ≤ (t' - t)⁻¹ * (ε / 2 * (t' - t)) :=
        mul_le_mul_of_nonneg_left hbound (inv_nonneg.2 (by linarith))
    _ = ε / 2 := by
        have hne : t' - t ≠ 0 := (sub_pos.2 htt').ne'
        field_simp
    _ < ε := by linarith

end Right

/-! ### The abstract data -/

section Abs

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

open Classical in
/-- The total version of `A s`: `A s y` for `y ∈ D` and `0` otherwise. -/
def gfevAt (D : Submodule ℝ H) (A : ℝ → D →ₗ[ℝ] H) (s : ℝ) (y : H) : H :=
  if h : y ∈ D then A s ⟨y, h⟩ else 0

theorem gfevAt_of_mem {D : Submodule ℝ H} {A : ℝ → D →ₗ[ℝ] H} (s : ℝ) {y : H} (h : y ∈ D) :
    gfevAt D A s y = A s ⟨y, h⟩ := dif_pos h

theorem gfev_exp_le (C : ℝ) {x T : ℝ} (hx0 : 0 ≤ x) (hxT : x ≤ T) :
    Real.exp (C * x) ≤ Real.exp (|C| * T) :=
  Real.exp_le_exp.2 ((mul_le_mul_of_nonneg_right (le_abs_self C) hx0).trans
    (mul_le_mul_of_nonneg_left hxT (abs_nonneg C)))

/-- The hypotheses of the abstract layer. -/
structure GFAbs (V : ℝ → ℝ → H →L[ℝ] H) (D : Submodule ℝ H) (A : ℝ → D →ₗ[ℝ] H) (C : ℝ) : Prop where
  bound : ∀ u t : ℝ, 0 ≤ u → u ≤ t → ‖V t u‖ ≤ Real.exp (C * (t - u))
  self : ∀ t : ℝ, 0 ≤ t → V t t = 1
  comp : ∀ s r t : ℝ, 0 ≤ s → s ≤ r → r ≤ t → (V t r).comp (V r s) = V t s
  cont : ∀ (T : ℝ) (x : H),
    ContinuousOn (fun p : ℝ × ℝ => V p.1 p.2 x) {p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T}
  inv : ∀ u t : ℝ, 0 ≤ u → u ≤ t → ∀ x ∈ D, V t u x ∈ D
  contA : ∀ x ∈ D, Continuous (fun s => gfevAt D A s x)
  contAV : ∀ r : ℝ, 0 ≤ r → ∀ x ∈ D, ContinuousOn (fun s => gfevAt D A s (V s r x)) (Ici r)
  mild_r : ∀ t : ℝ, 0 ≤ t → ∀ u u' : ℝ, 0 ≤ u → u ≤ u' → u' ≤ t → ∀ x ∈ D,
    V t u x - V t u' x = ∫ s in u..u', V t s (gfevAt D A s x)
  mild_t : ∀ r t t' : ℝ, 0 ≤ r → r ≤ t → t ≤ t' → ∀ x ∈ D,
    V t' r x - V t r x = ∫ s in t..t', V t' s (gfevAt D A s (V t r x))

variable {V : ℝ → ℝ → H →L[ℝ] H} {D : Submodule ℝ H} {A : ℝ → D →ₗ[ℝ] H} {C : ℝ}

/-- `∂_r V(t,r) x = -V(t,r) A_r x`. -/
theorem GFAbs.deriv_r (h : GFAbs V D A C) {t : ℝ} (ht : 0 ≤ t) {x : H} (hx : x ∈ D) {r : ℝ}
    (hr : r ∈ Icc 0 t) :
    HasDerivWithinAt (fun r' => V t r' x) (-(V t r (gfevAt D A r x))) (Icc 0 t) r := by
  have hVc : ∀ y, ContinuousOn (fun s => V t s y) (Icc 0 t) := fun y =>
    (h.cont t y).comp (continuous_const.prodMk continuous_id).continuousOn
      (fun s hs => ⟨hs.1, hs.2, le_rfl⟩)
  have hb : ∀ s ∈ Icc 0 t, ‖V t s‖ ≤ Real.exp (|C| * t) := fun s hs =>
    (h.bound s t hs.1 hs.2).trans (gfev_exp_le C (by linarith [hs.2]) (by linarith [hs.1]))
  have hf : ContinuousOn (fun s => -(V t s (gfevAt D A s x))) (Icc 0 t) :=
    (gfev_continuousOn_clm_apply hVc _ hb (h.contA x hx).continuousOn).neg
  refine gfev_hasDerivWithinAt_of_increments ht hf ?_ hr
  intro u hu u' hu' huu'
  rw [intervalIntegral.integral_neg, ← h.mild_r t ht u u' hu.1 huu' hu'.2 x hx]
  abel

/-- The right derivative of `t ↦ V(t,r) x`. -/
theorem GFAbs.rightDeriv (h : GFAbs V D A C) {r t T' : ℝ} (hr : 0 ≤ r) (hrt : r ≤ t) (htT : t < T')
    {x : H} (hx : x ∈ D) :
    HasDerivWithinAt (fun t' => V t' r x) (gfevAt D A t (V t r x)) (Ioi t) t := by
  set y : H := V t r x with hy
  have hyD : y ∈ D := h.inv r t hr hrt x hx
  set S : Set (ℝ × ℝ) := {p | t ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T'} with hS
  have hSsub : S ⊆ {p : ℝ × ℝ | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T'} :=
    fun p hp => ⟨by linarith [hp.1], hp.2.1, hp.2.2⟩
  have hV : ∀ z, ContinuousOn (fun p : ℝ × ℝ => V p.1 p.2 z) S := fun z => (h.cont T' z).mono hSsub
  have hb : ∀ p ∈ S, ‖V p.1 p.2‖ ≤ Real.exp (|C| * T') := fun p hp =>
    (h.bound p.2 p.1 (by linarith [hp.1]) hp.2.1).trans
      (gfev_exp_le C (by linarith [hp.2.1, hp.1]) (by linarith [hp.2.2, hp.1, hr, hrt]))
  have hw : ContinuousOn (fun p : ℝ × ℝ => gfevAt D A p.2 y) S :=
    ((h.contA y hyD).comp continuous_snd).continuousOn
  have hΦ := gfev_continuousOn_clm_apply (Vf := fun p : ℝ × ℝ => V p.1 p.2) hV _ hb hw
  have := gfev_rightDeriv_of_mild (x := fun t' => V t' r x)
    (Φ := fun t' s => V t' s (gfevAt D A s y)) htT hΦ (fun t' ht' => h.mild_t r t t' hr hrt ht'.1 x hx)
  have e : V t t (gfevAt D A t y) = gfevAt D A t y := by
    rw [h.self t (hr.trans hrt)]; rfl
  rwa [e] at this

/-- The forward equation `∂_t V(t,r) x = A_t V(t,r) x`, two-sided within `[r, T']`. -/
theorem GFAbs.forward (h : GFAbs V D A C) {r T' : ℝ} (hr : 0 ≤ r) (hrT : r ≤ T') {x : H} (hx : x ∈ D) :
    ∀ t ∈ Icc r T', HasDerivWithinAt (fun t' => V t' r x) (gfevAt D A t (V t r x)) (Icc r T') t := by
  have hf : ContinuousOn (fun t' => V t' r x) (Icc r T') :=
    (h.cont T' x).comp (continuous_id.prodMk continuous_const).continuousOn
      (fun t' ht' => ⟨hr, ht'.1, ht'.2⟩)
  have hg : ContinuousOn (fun t => gfevAt D A t (V t r x)) (Icc r T') :=
    (h.contAV r hr x hx).mono Icc_subset_Ici_self
  exact gfev_hasDerivWithinAt_Icc_of_right hrT hf hg
    (fun t ht => h.rightDeriv hr ht.1 ht.2 hx)

/-- Quasi-dissipativity: `2 ⟨x, A_r x⟩ ≤ 2C ‖x‖²`. -/
theorem GFAbs.quasi (h : GFAbs V D A C) {r : ℝ} (hr : 0 ≤ r) {x : H} (hx : x ∈ D) :
    2 * inner ℝ x (gfevAt D A r x) ≤ 2 * C * ‖x‖ ^ 2 := by
  have hd := h.rightDeriv hr le_rfl (by linarith : r < r + 1) hx
  have hd2 := hd.norm_sq
  have hxx : V r r x = x := by rw [h.self r hr]; rfl
  rw [hxx] at hd2
  rw [hasDerivWithinAt_iff_tendsto_slope] at hd2
  have hset : Ioi r \ {r} = Ioi r := by
    ext y; simp only [Set.mem_sdiff, mem_Ioi, mem_singleton_iff]
    exact ⟨fun h => h.1, fun h => ⟨h, ne_of_gt h⟩⟩
  rw [hset] at hd2
  have hg : HasDerivAt (fun t : ℝ => Real.exp (2 * C * (t - r))) (2 * C) r := by
    have h1 : HasDerivAt (fun t : ℝ => 2 * C * (t - r)) (2 * C) r := by
      simpa using ((hasDerivAt_id r).sub_const r).const_mul (2 * C)
    have := h1.exp
    simpa using this
  have hg2 := hg.hasDerivWithinAt (s := Ioi r)
  rw [hasDerivWithinAt_iff_tendsto_slope, hset] at hg2
  have hlim1 : Tendsto (slope (fun t' => ‖V t' r x‖ ^ 2) r) (𝓝[>] r)
      (𝓝 (2 * inner ℝ x (gfevAt D A r x))) := hd2
  have hlim2 : Tendsto (fun t => ‖x‖ ^ 2 * slope (fun t : ℝ => Real.exp (2 * C * (t - r))) r t) (𝓝[>] r)
      (𝓝 (‖x‖ ^ 2 * (2 * C))) := hg2.const_mul _
  have hle : ∀ᶠ t in 𝓝[>] r, slope (fun t' => ‖V t' r x‖ ^ 2) r t ≤
      ‖x‖ ^ 2 * slope (fun t : ℝ => Real.exp (2 * C * (t - r))) r t := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htr : r < t := ht
    have hb := h.bound r t hr htr.le
    have hb2 : ‖V t r x‖ ^ 2 ≤ Real.exp (2 * C * (t - r)) * ‖x‖ ^ 2 := by
      have h1 : ‖V t r x‖ ≤ Real.exp (C * (t - r)) * ‖x‖ :=
        ((V t r).le_opNorm x).trans (mul_le_mul_of_nonneg_right hb (norm_nonneg _))
      calc ‖V t r x‖ ^ 2 ≤ (Real.exp (C * (t - r)) * ‖x‖) ^ 2 := by gcongr
        _ = Real.exp (2 * C * (t - r)) * ‖x‖ ^ 2 := by
          rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
    have hpos : 0 < t - r := sub_pos.2 htr
    rw [slope_def_field, slope_def_field]
    have e0 : Real.exp (2 * C * (r - r)) = 1 := by simp
    rw [e0, hxx]
    rw [mul_div_assoc', div_le_div_iff_of_pos_right hpos]
    nlinarith [hb2]
  have := le_of_tendsto_of_tendsto hlim1 hlim2 hle
  nlinarith [this]

end Abs

end HRS.GF
