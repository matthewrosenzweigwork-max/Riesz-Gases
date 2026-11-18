import HRS.MS.SA16PRiesz2

/-!
# SA16P, part 3: `ℓ(s h) = ∫ s G` for bounded measurable `s`

A dominated convergence theorem in `L^p`, and the identity `ℓ(s h) = ∫ s G` first for simple `s`
(`SimpleFunc.induction`, from the set identity of part 2) and then for bounded measurable `s` by
approximation by simple functions bounded by the same constant.
-/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set Function
open scoped ENNReal NNReal

namespace HRS.Whole.AppendixA.Phase2SA16P

section Dct
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- dominated convergence in `L^p`, `1 ≤ p < ∞` (real functions) -/
lemma sa16p_dct_Lp {p : ℝ} (hp : 1 ≤ p) {F : ℕ → α → ℝ} {f g : α → ℝ}
    (hF : ∀ n, AEStronglyMeasurable (F n) μ) (hf : AEStronglyMeasurable f μ)
    (hg : MemLp g (ENNReal.ofReal p) μ) (hbd : ∀ n, ∀ᵐ x ∂μ, |F n x| ≤ g x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (f x))) :
    Tendsto (fun n => eLpNorm (fun x => F n x - f x) (ENNReal.ofReal p) μ) atTop (𝓝 0) := by
  have hp0 : 0 < p := by linarith
  have hpe0 : ENNReal.ofReal p ≠ 0 := by simpa using hp0
  have hpetop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpr : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
  have hmeas : ∀ n, AEStronglyMeasurable (fun x => F n x - f x) μ := fun n => (hF n).sub hf
  have heq : ∀ n, eLpNorm (fun x => F n x - f x) (ENNReal.ofReal p) μ =
      (∫⁻ x, ‖F n x - f x‖ₑ ^ p ∂μ) ^ (1 / p) := fun n => by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpe0 hpetop (hmeas n), hpr]
  simp_rw [heq]
  have hfg : ∀ᵐ x ∂μ, |f x| ≤ g x := by
    have hb : ∀ᵐ x ∂μ, ∀ n, |F n x| ≤ g x := ae_all_iff.2 hbd
    filter_upwards [hb, hlim] with x hx hl
    exact le_of_tendsto (hl.abs) (Eventually.of_forall hx)
  have hgint : ∫⁻ x, ‖g x‖ₑ ^ p ∂μ < ⊤ := by
    have := hg.eLpNorm_lt_top
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpe0 hpetop hg.aestronglyMeasurable, hpr] at this
    have h2 : (∫⁻ x, ‖g x‖ₑ ^ p ∂μ) ^ (1 / p) < ⊤ := this
    by_contra hcon
    rw [not_lt, top_le_iff] at hcon
    rw [hcon, ENNReal.top_rpow_of_pos (by positivity)] at h2
    exact lt_irrefl _ h2
  have hlim' : Tendsto (fun n => ∫⁻ x, ‖F n x - f x‖ₑ ^ p ∂μ) atTop (𝓝 0) := by
    have := tendsto_lintegral_of_dominated_convergence' (μ := μ)
      (F := fun n x => ‖F n x - f x‖ₑ ^ p) (f := fun _ => 0)
      (bound := fun x => (2 : ℝ≥0∞) ^ p * ‖g x‖ₑ ^ p)
      (fun n => (hmeas n).enorm.pow_const _)
      (fun n => ?_)
      (by
        rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp0.le (by simp))]
        exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hp0.le (by simp)) hgint.ne)
      ?_
    · simpa using this
    · filter_upwards [hbd n, hfg] with x h1 h2
      show ‖F n x - f x‖ₑ ^ p ≤ 2 ^ p * ‖g x‖ₑ ^ p
      rw [← ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
      refine ENNReal.rpow_le_rpow ?_ hp0.le
      have h3 : ‖F n x - f x‖ ≤ 2 * ‖g x‖ := by
        have hg0 : 0 ≤ g x := (abs_nonneg _).trans h1
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hg0]
        calc |F n x - f x| ≤ |F n x| + |f x| := abs_sub _ _
          _ ≤ 2 * g x := by linarith
      calc ‖F n x - f x‖ₑ = ENNReal.ofReal ‖F n x - f x‖ := (ofReal_norm_eq_enorm _).symm
        _ ≤ ENNReal.ofReal (2 * ‖g x‖) := ENNReal.ofReal_le_ofReal h3
        _ = 2 * ‖g x‖ₑ := by
          rw [ENNReal.ofReal_mul (by norm_num), ofReal_norm_eq_enorm]; simp
    · filter_upwards [hlim] with x hx
      have h1 : Tendsto (fun n => F n x - f x) atTop (𝓝 0) := by
        simpa using hx.sub_const (f x)
      have h2 : Tendsto (fun n => ‖F n x - f x‖ₑ) atTop (𝓝 0) := by
        simpa using h1.enorm
      have h3 := ((ENNReal.continuous_rpow_const (y := p)).tendsto 0).comp h2
      rw [ENNReal.zero_rpow_of_pos hp0] at h3
      exact h3
  have h4 := ((ENNReal.continuous_rpow_const (y := 1 / p)).tendsto 0).comp hlim'
  rw [ENNReal.zero_rpow_of_pos (show 0 < 1 / p by positivity)] at h4
  exact h4

end Dct

section Bdd
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ]
variable {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] {h : α → ℝ} (hh : MemLp h (ENNReal.ofReal p) μ)
  (ℓ : Lp ℝ (ENNReal.ofReal p) μ →L[ℝ] ℝ)

include hh in
lemma sa16p_mulh_memLp {s : α → ℝ} (hs : AEStronglyMeasurable s μ) {K : ℝ}
    (hK : ∀ x, |s x| ≤ K) : MemLp (fun x => s x * h x) (ENNReal.ofReal p) μ := by
  refine hh.of_le_mul (c := K) (hs.mul hh.aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right (hK x) (abs_nonneg _)

lemma sa16p_ell_simple (hp : 1 < p) (s : SimpleFunc α ℝ)
    (hmem : MemLp (fun x => s x * h x) (ENNReal.ofReal p) μ) :
    ℓ (hmem.toLp _) = ∫ x, s x * sa16p_G hh ℓ hp x ∂μ := by
  have hGi := sa16p_G_integrable hh ℓ hp
  induction s using SimpleFunc.induction with
  | const c hA =>
    rename_i A
    have hA' := hA
    -- the function is `c • 1_A`
    have hfun : (fun x => (SimpleFunc.piecewise A hA (SimpleFunc.const α c) (SimpleFunc.const α 0)) x * h x)
        = fun x => c * A.indicator h x := by
      funext x
      by_cases hx : x ∈ A <;> simp [SimpleFunc.piecewise_apply, hx, Set.indicator_of_mem, Set.indicator_of_notMem]
    have hLp : hmem.toLp _ = c • sa16p_ind hh A hA := by
      apply Lp.ext
      filter_upwards [MemLp.coeFn_toLp hmem, Lp.coeFn_smul c (sa16p_ind hh A hA),
        sa16p_ind_coe hh A hA] with x h1 h2 h3
      rw [h1, h2, Pi.smul_apply, h3, smul_eq_mul]
      exact congrFun hfun x
    rw [hLp, map_smul, ← sa16p_G_setIntegral hh ℓ hp hA, smul_eq_mul]
    have : (fun x => (SimpleFunc.piecewise A hA (SimpleFunc.const α c) (SimpleFunc.const α 0)) x *
        sa16p_G hh ℓ hp x) = A.indicator (fun x => c * sa16p_G hh ℓ hp x) := by
      funext x
      by_cases hx : x ∈ A <;> simp [SimpleFunc.piecewise_apply, hx, Set.indicator_of_mem, Set.indicator_of_notMem]
    rw [this, integral_indicator hA, integral_const_mul]
  | add hd hf hg =>
    rename_i f g
    have hfm : MemLp (fun x => f x * h x) (ENNReal.ofReal p) μ := by
      obtain ⟨K, hK⟩ := f.exists_forall_norm_le
      exact sa16p_mulh_memLp hh f.aestronglyMeasurable (K := K) (fun x => by simpa using hK x)
    have hgm : MemLp (fun x => g x * h x) (ENNReal.ofReal p) μ := by
      obtain ⟨K, hK⟩ := g.exists_forall_norm_le
      exact sa16p_mulh_memLp hh g.aestronglyMeasurable (K := K) (fun x => by simpa using hK x)
    have hLp : hmem.toLp _ = hfm.toLp _ + hgm.toLp _ := by
      rw [← MemLp.toLp_add]
      congr 1
      funext x
      simp [add_mul]
    rw [hLp, map_add, hf hfm, hg hgm, ← integral_add]
    · congr 1; funext x; simp [add_mul]
    · obtain ⟨K, hK⟩ := f.exists_forall_norm_le
      exact hGi.bdd_mul (c := K) f.aestronglyMeasurable (Eventually.of_forall fun x => by simpa using hK x)
    · obtain ⟨K, hK⟩ := g.exists_forall_norm_le
      exact hGi.bdd_mul (c := K) g.aestronglyMeasurable (Eventually.of_forall fun x => by simpa using hK x)

lemma sa16p_ell_bdd (hp : 1 < p) {s : α → ℝ} (hs : Measurable s) {K : ℝ} (hK : ∀ x, |s x| ≤ K)
    (hmem : MemLp (fun x => s x * h x) (ENNReal.ofReal p) μ) :
    ℓ (hmem.toLp _) = ∫ x, s x * sa16p_G hh ℓ hp x ∂μ := by
  have hGi := sa16p_G_integrable hh ℓ hp
  set K' : ℝ := max K 0 with hK'
  have hK0 : (0 : ℝ) ≤ K' := le_max_right _ _
  have hsK : ∀ x, |s x| ≤ K' := fun x => (hK x).trans (le_max_left _ _)
  have h0 : (0 : ℝ) ∈ Metric.closedBall (0 : ℝ) K' := Metric.mem_closedBall_self hK0
  set sn : ℕ → SimpleFunc α ℝ := fun n =>
    SimpleFunc.approxOn s hs (Metric.closedBall (0 : ℝ) K') 0 h0 n with hsn
  have hsn_b : ∀ n x, |sn n x| ≤ K' := fun n x => by
    have := SimpleFunc.approxOn_mem hs h0 n x
    simpa [Real.dist_eq] using this
  have hsn_lim : ∀ x, Tendsto (fun n => sn n x) atTop (𝓝 (s x)) := fun x => by
    refine SimpleFunc.tendsto_approxOn hs h0 ?_
    rw [(Metric.isClosed_closedBall).closure_eq]
    simpa [Real.dist_eq] using hsK x
  have hm : ∀ n, MemLp (fun x => sn n x * h x) (ENNReal.ofReal p) μ := fun n =>
    sa16p_mulh_memLp hh (sn n).aestronglyMeasurable (hsn_b n)
  have hell : ∀ n, ℓ ((hm n).toLp _) = ∫ x, sn n x * sa16p_G hh ℓ hp x ∂μ := fun n =>
    sa16p_ell_simple hh ℓ hp (sn n) (hm n)
  have hp1 : (1 : ℝ) ≤ p := hp.le
  have hLp : Tendsto (fun n => (hm n).toLp _) atTop (𝓝 (hmem.toLp _)) := by
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun n x => sn n x * h x) hm (fun x => s x * h x) hmem]
    refine sa16p_dct_Lp hp1 (g := fun x => K' * ‖h x‖) (fun n => (hm n).aestronglyMeasurable)
      hmem.aestronglyMeasurable (hh.norm.const_mul K') (fun n => Eventually.of_forall fun x => ?_)
      (Eventually.of_forall fun x => (hsn_lim x).mul_const (h x))
    rw [abs_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hsn_b n x) (abs_nonneg _)
  have h1 := (ℓ.continuous.tendsto _).comp hLp
  have h2 : Tendsto (fun n => ∫ x, sn n x * sa16p_G hh ℓ hp x ∂μ) atTop
      (𝓝 (∫ x, s x * sa16p_G hh ℓ hp x ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => K' * ‖sa16p_G hh ℓ hp x‖)
      (fun n => ((sn n).aestronglyMeasurable).mul hGi.aestronglyMeasurable)
      (hGi.norm.const_mul K') (fun n => Eventually.of_forall fun x => ?_)
      (Eventually.of_forall fun x => (hsn_lim x).mul_const _)
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hsn_b n x) (norm_nonneg _)
  have h3 : (fun n => ℓ ((hm n).toLp _)) = fun n => ∫ x, sn n x * sa16p_G hh ℓ hp x ∂μ :=
    funext hell
  have h1' : Tendsto (fun n => ℓ ((hm n).toLp _)) atTop (𝓝 (ℓ (hmem.toLp _))) := h1
  rw [h3] at h1'
  exact tendsto_nhds_unique h1' h2

end Bdd

end HRS.Whole.AppendixA.Phase2SA16P
