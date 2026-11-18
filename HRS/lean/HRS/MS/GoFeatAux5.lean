import HRS.MS.GoFeatAux4

/-!
# S5.5 features: smoothness of `ℓ²`-valued and `L²_t(ℓ²)`-valued families (infrastructure)

* `s55f_ell_contDiff`: a family `g_α : E → ℝ` of `C^k` functions with `ℓ¹`-summable derivative bounds
  `‖D^j g_α(x)‖ ≤ c_α` (`j ≤ k`) defines the `C^k` map `x ↦ ellVec m (g_α(x))_α ∈ ℓ²`, with
  `‖D^j‖ ≤ ∑ c_α`.
* `s55f_aesm_fderiv`: the directional derivative of a family `F t` of differentiable functions, measurable in `t`
  at every point, is measurable in `t`.
* `s55f_L2_contDiff`: a family `F : ℝ → ℝ^d → G` (`G` Banach), with `F t` of class `C^k`, all derivatives of order
  `≤ k` bounded by `B` uniformly in `t`, and `t ↦ F t x` strongly measurable for each `x` (and a finite measure `μ` on
  the time axis) defines the `C^k` map `x ↦ [t ↦ F t x] ∈ L²(μ; G)`, with `‖D^j‖ ≤ d^j B μ(univ)^{1/2}`.  Only `C^k`
  regularity of each slice `F t` is assumed (no `(k+1)`-st derivative): the last derivative is handled by dominated
  convergence.

Helper names carry the prefix `s55f_`; namespace `HRS.MS.Go`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

namespace HRS.MS.Go
open HRS HRS.Whole

variable {d : ℕ}

/-! ### `ℓ²`-valued smoothness from `ℓ¹` bounds -/

lemma s55f_memℓp_of_summable {c : MultiIndex d → ℝ} (hc : Summable fun α => |c α|) :
    Memℓp c 2 := by
  have h1 : Memℓp c 1 := by
    rw [memℓp_gen_iff (by norm_num)]
    simpa using hc
  exact h1.of_exponent_ge (by norm_num)

lemma s55f_ellVec_eq {m : ℝ} {c : MultiIndex d → ℝ} (h : Memℓp c 2) :
    (ellVec (d := d) m c : lp (fun _ : MultiIndex d => ℝ) 2) =
      (⟨c, h⟩ : lp (fun _ : MultiIndex d => ℝ) 2) := by
  unfold ellVec
  exact dif_pos h

lemma s55f_hasSum_ellVec {m : ℝ} {c : MultiIndex d → ℝ} (hc : Summable fun α => |c α|) :
    HasSum (fun α => (lp.single 2 α (c α) : lp (fun _ : MultiIndex d => ℝ) 2))
      (ellVec (d := d) m c : lp (fun _ : MultiIndex d => ℝ) 2) := by
  have h := s55f_memℓp_of_summable hc
  rw [s55f_ellVec_eq h]
  exact lp.hasSum_single (by norm_num) ⟨c, h⟩

lemma s55f_single_norm_le (α : MultiIndex d) :
    ‖(lp.singleContinuousLinearMap (𝕜 := ℝ) (E := fun _ : MultiIndex d => ℝ) 2 α)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun a => ?_
  rw [lp.singleContinuousLinearMap_apply, lp.norm_single (by norm_num)]
  simp

theorem s55f_ell_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {m : ℝ} {k : ℕ}
    (g : MultiIndex d → E → ℝ) (hg : ∀ α, ContDiff ℝ k (g α)) (c : MultiIndex d → ℝ)
    (hc : Summable c) (hb : ∀ α, ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j (g α) x‖ ≤ c α) :
    ContDiff ℝ k (fun x => ellVec (d := d) m (fun α => g α x)) ∧
    ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j (fun x => ellVec (d := d) m (fun α => g α x)) x‖ ≤ ∑' α, c α := by
  set ι : ∀ α : MultiIndex d, ℝ →L[ℝ] OscDual d m := fun α =>
    lp.singleContinuousLinearMap (𝕜 := ℝ) (E := fun _ : MultiIndex d => ℝ) 2 α with hι
  have hι1 : ∀ α, ‖ι α‖ ≤ 1 := fun α => s55f_single_norm_le α
  set f : MultiIndex d → E → OscDual d m := fun α x => ι α (g α x) with hf
  have hfc : ∀ α, ContDiff ℝ k (f α) := fun α => (ι α).contDiff.comp (hg α)
  have hfb : ∀ (j : ℕ) (α : MultiIndex d) (x : E), (j : ℕ∞) ≤ (k : ℕ∞) → ‖iteratedFDeriv ℝ j (f α) x‖ ≤ c α := by
    intro j α x hj
    have hjk : j ≤ k := by exact_mod_cast hj
    have h1 := (ι α).norm_iteratedFDeriv_comp_left (hg α).contDiffAt (x := x) (n := j)
      (by exact_mod_cast hjk)
    exact h1.trans ((mul_le_of_le_one_left (norm_nonneg _) (hι1 α)).trans (hb α j hjk x))
  have hsum_bd : ∀ x, Summable fun α => |g α x| := by
    intro x
    refine Summable.of_norm_bounded hc fun α => ?_
    have := hb α 0 (Nat.zero_le _) x
    rw [norm_iteratedFDeriv_zero] at this
    simpa [Real.norm_eq_abs] using this
  have hGs : ∀ x, ∑' α, f α x = ellVec (d := d) m (fun α => g α x) := fun x =>
    (s55f_hasSum_ellVec (m := m) (hsum_bd x)).tsum_eq
  have hcd : ContDiff ℝ k (fun x => ∑' α, f α x) :=
    contDiff_tsum (N := (k : ℕ∞)) hfc (fun _ _ => hc) (fun j α x hj => hfb j α x hj)
  have hfun : (fun x => ellVec (d := d) m (fun α => g α x)) = fun x => ∑' α, f α x :=
    funext fun x => (hGs x).symm
  rw [hfun]
  refine ⟨hcd, fun j hj x => ?_⟩
  have hj' : (j : ℕ∞) ≤ (k : ℕ∞) := by exact_mod_cast hj
  rw [iteratedFDeriv_tsum_apply (N := (k : ℕ∞)) hfc (fun _ _ => hc) (fun j α x hj => hfb j α x hj) hj' x]
  exact tsum_of_norm_bounded hc.hasSum fun α => hfb j α x hj'

/-! ### Measurability of directional derivatives -/

lemma s55f_aesm_fderiv {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {μ : Measure ℝ} (F : ℝ → E → G)
    (hdiff : ∀ t, Differentiable ℝ (F t))
    (hm : ∀ x, AEStronglyMeasurable (fun t => F t x) μ) (x e : E) :
    AEStronglyMeasurable (fun t => fderiv ℝ (F t) x e) μ := by
  set u : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hu
  have hu0 : Tendsto u atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hune : ∀ n, u n ≠ 0 := fun n => by simp [hu]; positivity
  refine aestronglyMeasurable_of_tendsto_ae (atTop : Filter ℕ)
    (f := fun (n : ℕ) (t : ℝ) => ((n : ℝ) + 1) • (F t (x + u n • e) - F t x)) ?_ ?_
  · intro n
    exact ((hm _).sub (hm x)).const_smul _
  · refine Eventually.of_forall fun t => ?_
    have h1 : HasDerivAt (fun s : ℝ => F t (x + s • e)) (fderiv ℝ (F t) x e) 0 := by
      have h2 : HasDerivAt (fun s : ℝ => x + s • e) e 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add x
      have h3 : HasFDerivAt (F t) (fderiv ℝ (F t) x) (x + (0 : ℝ) • e) := by
        simpa using (hdiff t x).hasFDerivAt
      exact h3.comp_hasDerivAt (0 : ℝ) h2
    rw [hasDerivAt_iff_tendsto_slope_zero] at h1
    have h4 : Tendsto u atTop (𝓝[≠] 0) := tendsto_nhdsWithin_iff.2 ⟨hu0, Eventually.of_forall hune⟩
    refine (h1.comp h4).congr fun n => ?_
    simp only [Function.comp, hu, zero_add, zero_smul, add_zero]
    congr 1
    simp

/-! ### Dominated convergence in `L²` -/

lemma s55f_eLpNorm_tendsto_zero {μ : Measure ℝ} [IsFiniteMeasure μ] {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] {G : Type*} [NormedAddCommGroup G] (f : ι → ℝ → G)
    (hm : ∀ i, AEStronglyMeasurable (f i) μ) (B : ℝ) (hb : ∀ i t, ‖f i t‖ ≤ B)
    (hlim : ∀ t, Tendsto (fun i => f i t) l (𝓝 0)) :
    Tendsto (fun i => eLpNorm (f i) 2 μ) l (𝓝 0) := by
  have h2 : ∀ i, eLpNorm (f i) 2 μ = (∫⁻ t, ‖f i t‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := by
    intro i
    rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num) (hm i)]
    simp
  have hint : Tendsto (fun i => ∫⁻ t, ‖f i t‖ₑ ^ (2 : ℝ) ∂μ) l (𝓝 0) := by
    have := tendsto_lintegral_filter_of_dominated_convergence' (μ := μ) (l := l)
      (F := fun i t => ‖f i t‖ₑ ^ (2 : ℝ)) (f := fun _ => (0 : ℝ≥0∞))
      (fun _ => ENNReal.ofReal B ^ (2 : ℝ))
      (Eventually.of_forall fun i => ((hm i).enorm.pow_const _)) ?_ ?_ ?_
    · simpa using this
    · refine Eventually.of_forall fun i => Eventually.of_forall fun t => ?_
      refine ENNReal.rpow_le_rpow ?_ (by norm_num)
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hb i t)
    · rw [lintegral_const]
      exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
        (measure_ne_top _ _)
    · refine Eventually.of_forall fun t => ?_
      have h1 : Tendsto (fun i => ‖f i t‖ₑ) l (𝓝 0) := by
        have := (continuous_enorm.tendsto (0 : G)).comp (hlim t)
        simp only [enorm_zero] at this
        exact this
      have h3 := (ENNReal.continuous_rpow_const (y := (2 : ℝ))).tendsto 0
      rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h3
      exact h3.comp h1
  have h3 := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0
  rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h3
  have h4 := h3.comp hint
  simp only [h2]
  exact h4

/-! ### The `L²`-valued map `x ↦ [t ↦ F t x]` -/

section L2

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
  (μ : Measure ℝ) [IsFiniteMeasure μ]

lemma s55f_memLp_of_bound {f : ℝ → G} (hm : AEStronglyMeasurable f μ) {B : ℝ}
    (hb : ∀ t, ‖f t‖ ≤ B) : MemLp f 2 μ :=
  MemLp.of_bound hm B (Eventually.of_forall hb)

lemma s55f_norm_toLp_le {f : ℝ → G} (hf : MemLp f 2 μ) {B : ℝ} (hb : ∀ t, ‖f t‖ ≤ B) :
    ‖hf.toLp f‖ ≤ B * (μ Set.univ).toReal ^ (1 / 2 : ℝ) := by
  rw [Lp.norm_toLp]
  have h1 := eLpNorm_le_of_ae_bound (μ := μ) (p := 2) (f := f) hf.aestronglyMeasurable
    (Eventually.of_forall hb)
  have hB : 0 ≤ B := (norm_nonneg _).trans (hb 0)
  have h2 : eLpNorm f 2 μ ≠ ⊤ := hf.eLpNorm_ne_top
  calc (eLpNorm f 2 μ).toReal ≤ (μ Set.univ ^ (2 : ℝ≥0∞).toReal⁻¹ * ENNReal.ofReal B).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
          (measure_ne_top _ _)) ENNReal.ofReal_ne_top) h1
    _ = B * (μ Set.univ).toReal ^ (1 / 2 : ℝ) := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hB, ENNReal.toReal_rpow]
        simp [mul_comm]

lemma s55f_W_continuous {B : ℝ} (F : ℝ → Euc d → G) (hcont : ∀ t, Continuous (F t))
    (hb : ∀ t x, ‖F t x‖ ≤ B) (hm : ∀ x, AEStronglyMeasurable (fun t => F t x) μ)
    (hmem : ∀ x, MemLp (fun t => F t x) 2 μ) :
    Continuous (fun x => (hmem x).toLp (fun t => F t x)) := by
  rw [continuous_iff_continuousAt]
  intro x
  show Tendsto (fun x' => (hmem x').toLp (fun t => F t x')) (𝓝 x) (𝓝 ((hmem x).toLp (fun t => F t x)))
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fi := 𝓝 x) (fun x' t => F t x') hmem
    (fun t => F t x) (hmem x)]
  refine s55f_eLpNorm_tendsto_zero (μ := μ) (l := 𝓝 x) (f := fun x' t => F t x' - F t x)
    (fun x' => (hm x').sub (hm x)) (2 * B) (fun x' t => ?_) (fun t => ?_)
  · calc ‖F t x' - F t x‖ ≤ ‖F t x'‖ + ‖F t x‖ := norm_sub_le _ _
      _ ≤ 2 * B := by linarith [hb t x', hb t x]
  · have := ((hcont t).tendsto x).sub_const (F t x)
    simpa using this

lemma s55f_W_hasFDerivAt {B : ℝ} (F : ℝ → Euc d → G) (hF1 : ∀ t, ContDiff ℝ 1 (F t))
    (hb0 : ∀ t x, ‖F t x‖ ≤ B) (hb1 : ∀ t x, ‖fderiv ℝ (F t) x‖ ≤ B)
    (hm : ∀ x, AEStronglyMeasurable (fun t => F t x) μ)
    (hmem : ∀ x, MemLp (fun t => F t x) 2 μ)
    (hmemD : ∀ x h, MemLp (fun t => fderiv ℝ (F t) x h) 2 μ) (x : Euc d)
    (Θ : Euc d →L[ℝ] Lp G 2 μ)
    (hΘ : ∀ h, Θ h = (hmemD x h).toLp (fun t => fderiv ℝ (F t) x h)) :
    HasFDerivAt (fun x => (hmem x).toLp (fun t => F t x)) Θ x := by
  have hdiff : ∀ t, Differentiable ℝ (F t) := fun t => (hF1 t).differentiable one_ne_zero
  have hmD : ∀ x' h, AEStronglyMeasurable (fun t => fderiv ℝ (F t) x' h) μ := fun x' h =>
    s55f_aesm_fderiv F hdiff hm x' h
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hb0 0 0)
  rw [hasFDerivAt_iff_tendsto]
  set R : Euc d → ℝ → G := fun x' t => F t x' - F t x - fderiv ℝ (F t) x (x' - x) with hR
  have hmR : ∀ x', AEStronglyMeasurable (R x') μ := fun x' =>
    ((hm x').sub (hm x)).sub (hmD x (x' - x))
  have hbR : ∀ x' t, ‖R x' t‖ ≤ 2 * B * ‖x' - x‖ := by
    intro x' t
    have h1 : ‖F t x' - F t x‖ ≤ B * ‖x' - x‖ :=
      Convex.norm_image_sub_le_of_norm_fderiv_le (fun y _ => hdiff t y) (fun y _ => hb1 t y)
        convex_univ (Set.mem_univ x) (Set.mem_univ x')
    have h2 : ‖fderiv ℝ (F t) x (x' - x)‖ ≤ B * ‖x' - x‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (hb1 t x) (norm_nonneg _))
    calc ‖R x' t‖ ≤ ‖F t x' - F t x‖ + ‖fderiv ℝ (F t) x (x' - x)‖ := norm_sub_le _ _
      _ ≤ 2 * B * ‖x' - x‖ := by linarith
  have hmemR : ∀ x', MemLp (R x') 2 μ := fun x' =>
    s55f_memLp_of_bound μ (hmR x') (B := 2 * B * ‖x' - x‖) (hbR x')
  set r : Euc d → ℝ → G := fun x' t => ‖x' - x‖⁻¹ • R x' t with hr
  have hmr : ∀ x', AEStronglyMeasurable (r x') μ := fun x' => (hmR x').const_smul _
  have hbr : ∀ x' t, ‖r x' t‖ ≤ 2 * B := by
    intro x' t
    rcases eq_or_ne x' x with rfl | hne
    · simp [hr, hR]; positivity
    · have hpos : 0 < ‖x' - x‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
      simp only [hr]
      rw [norm_smul, norm_inv, norm_norm, inv_mul_le_iff₀ hpos]
      have := hbR x' t
      linarith
  have hlim : ∀ t, Tendsto (fun x' => r x' t) (𝓝 x) (𝓝 0) := by
    intro t
    have := hasFDerivAt_iff_tendsto.1 (hdiff t x).hasFDerivAt
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine this.congr fun x' => ?_
    simp [hr, hR, norm_smul]
  have h0 := s55f_eLpNorm_tendsto_zero (μ := μ) (l := 𝓝 x) r hmr (2 * B) hbr hlim
  have h1 : Tendsto (fun x' => (eLpNorm (r x') 2 μ).toReal) (𝓝 x) (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h0
    rw [ENNReal.toReal_zero] at this
    exact this
  refine h1.congr fun x' => ?_
  have e : (hmemR x').toLp (R x') =
      (hmem x').toLp (fun t => F t x') - (hmem x).toLp (fun t => F t x) - Θ (x' - x) := by
    rw [hΘ]
    apply Lp.ext
    filter_upwards [(hmemR x').coeFn_toLp, (hmem x').coeFn_toLp, (hmem x).coeFn_toLp,
      (hmemD x (x' - x)).coeFn_toLp,
      Lp.coeFn_sub ((hmem x').toLp (fun t => F t x') - (hmem x).toLp (fun t => F t x))
        ((hmemD x (x' - x)).toLp (fun t => fderiv ℝ (F t) x (x' - x))),
      Lp.coeFn_sub ((hmem x').toLp (fun t => F t x')) ((hmem x).toLp (fun t => F t x))]
      with t h1 h2 h3 h4 h5 h6
    rw [h1, h5]
    simp only [Pi.sub_apply] at h5 h6 ⊢
    rw [h6, h2, h3, h4]
  have hnorm : ‖(hmemR x').toLp (R x')‖ = (eLpNorm (R x') 2 μ).toReal := Lp.norm_toLp _ _
  rw [← e, hnorm]
  have : eLpNorm (r x') 2 μ = ENNReal.ofReal ‖x' - x‖⁻¹ * eLpNorm (R x') 2 μ := by
    have := eLpNorm_const_smul (μ := μ) (p := 2) (‖x' - x‖⁻¹) (R x')
    rw [show r x' = ‖x' - x‖⁻¹ • R x' from rfl, this]
    congr 1
    rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [this, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]

theorem s55f_L2_contDiff (hd : 1 ≤ d) (k : ℕ) : ∀ (F : ℝ → Euc d → G) (B : ℝ),
    (∀ t, ContDiff ℝ k (F t)) → (∀ t, ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j (F t) x‖ ≤ B) →
    (∀ x, AEStronglyMeasurable (fun t => F t x) μ) → ∀ (hmem : ∀ x, MemLp (fun t => F t x) 2 μ),
    ContDiff ℝ k (fun x => (hmem x).toLp (fun t => F t x)) ∧
    ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j (fun x => (hmem x).toLp (fun t => F t x)) x‖ ≤
      (d : ℝ) ^ j * (B * (μ Set.univ).toReal ^ (1 / 2 : ℝ)) := by
  induction k with
  | zero =>
    intro F B hF hb hm hmem
    have hb0 : ∀ t x, ‖F t x‖ ≤ B := fun t x => by simpa using hb t 0 le_rfl x
    refine ⟨contDiff_zero.2 (s55f_W_continuous μ F (fun t => (hF t).continuous) hb0 hm hmem),
      fun j hj x => ?_⟩
    have : j = 0 := by omega
    subst this
    simp only [norm_iteratedFDeriv_zero, pow_zero, one_mul]
    exact s55f_norm_toLp_le μ (hmem x) (fun t => hb0 t x)
  | succ k ih =>
    intro F B hF hb hm hmem
    have hF1 : ∀ t, ContDiff ℝ 1 (F t) := fun t => (hF t).of_le (by exact_mod_cast Nat.le_add_left 1 k)
    have hdiff : ∀ t, Differentiable ℝ (F t) := fun t => (hF1 t).differentiable one_ne_zero
    have hb0 : ∀ t x, ‖F t x‖ ≤ B := fun t x => by simpa using hb t 0 (Nat.zero_le _) x
    have hb1 : ∀ t x, ‖fderiv ℝ (F t) x‖ ≤ B := fun t x => by
      have := hb t 1 (by omega) x
      rwa [norm_iteratedFDeriv_one] at this
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hb0 0 0)
    have hmD : ∀ x h, AEStronglyMeasurable (fun t => fderiv ℝ (F t) x h) μ := fun x h =>
      s55f_aesm_fderiv F hdiff hm x h
    have hmemD : ∀ x h, MemLp (fun t => fderiv ℝ (F t) x h) 2 μ := fun x h =>
      s55f_memLp_of_bound μ (hmD x h) (B := B * ‖h‖) (fun t =>
        (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (hb1 t x) (norm_nonneg _)))
    -- the candidate derivative
    let Θl : Euc d → (Euc d →ₗ[ℝ] Lp G 2 μ) := fun x =>
      { toFun := fun h => (hmemD x h).toLp (fun t => fderiv ℝ (F t) x h)
        map_add' := fun h₁ h₂ => by
          rw [← MemLp.toLp_add]
          exact MemLp.toLp_congr _ _ (Eventually.of_forall fun t => by simp)
        map_smul' := fun c h => by
          rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
          exact MemLp.toLp_congr _ _ (Eventually.of_forall fun t => by simp) }
    let Θ : Euc d → (Euc d →L[ℝ] Lp G 2 μ) := fun x => LinearMap.toContinuousLinearMap (Θl x)
    have hΘ : ∀ x h, Θ x h = (hmemD x h).toLp (fun t => fderiv ℝ (F t) x h) := fun x h => rfl
    have hder : ∀ x, HasFDerivAt (fun x => (hmem x).toLp (fun t => F t x)) (Θ x) x := fun x =>
      s55f_W_hasFDerivAt μ F hF1 hb0 hb1 hm hmem hmemD x (Θ x) (hΘ x)
    -- the slices of the derivative
    have hslice : ∀ h : Euc d, ContDiff ℝ k (fun x => Θ x h) ∧
        ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j (fun x => Θ x h) x‖ ≤
          (d : ℝ) ^ j * ((B * ‖h‖) * (μ Set.univ).toReal ^ (1 / 2 : ℝ)) := by
      intro h
      have hFh : ∀ t, ContDiff ℝ k (fun x => fderiv ℝ (F t) x h) := fun t =>
        ((hF t).fderiv_right (m := k) (by push_cast; exact le_rfl)).clm_apply contDiff_const
      have hbh : ∀ t, ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j (fun x => fderiv ℝ (F t) x h) x‖ ≤ B * ‖h‖ := by
        intro t j hj x
        have h1 := norm_iteratedFDeriv_clm_apply_const (𝕜 := ℝ) (f := fderiv ℝ (F t)) (c := h) (x := x)
          (N := (k : WithTop ℕ∞)) (n := j)
          (((hF t).fderiv_right (m := k) (by push_cast; exact le_rfl)).contDiffAt) (by exact_mod_cast hj)
        rw [norm_iteratedFDeriv_fderiv] at h1
        calc _ ≤ ‖h‖ * ‖iteratedFDeriv ℝ (j + 1) (F t) x‖ := h1
          _ ≤ ‖h‖ * B := mul_le_mul_of_nonneg_left (hb t (j + 1) (by omega) x) (norm_nonneg _)
          _ = B * ‖h‖ := mul_comm _ _
      exact ih (fun t x => fderiv ℝ (F t) x h) (B * ‖h‖) hFh hbh (fun x => hmD x h) (fun x => hmemD x h)
    have hΘcd : ContDiff ℝ k Θ := contDiff_clm_apply_iff.2 fun h => (hslice h).1
    refine ⟨?_, fun j hj x => ?_⟩
    · rw [show ((k + 1 : ℕ) : WithTop ℕ∞) = (k : WithTop ℕ∞) + 1 by push_cast; rfl]
      exact contDiff_succ_iff_hasFDerivAt.2 ⟨Θ, hΘcd, hder⟩
    · rcases j with _ | j
      · simp only [norm_iteratedFDeriv_zero, pow_zero, one_mul]
        exact s55f_norm_toLp_le μ (hmem x) (fun t => hb0 t x)
      · have hfd : fderiv ℝ (fun x => (hmem x).toLp (fun t => F t x)) = Θ :=
          funext fun y => (hder y).fderiv
        rw [← norm_iteratedFDeriv_fderiv, hfd]
        have hjk : j ≤ k := by omega
        have hbd : ‖iteratedFDeriv ℝ j Θ x‖ ≤ (d : ℝ) ^ j * (B * (μ Set.univ).toReal ^ (1 / 2 : ℝ)) := by
          refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m => ?_
          refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
          have hcomp := (ContinuousLinearMap.apply ℝ (Lp G 2 μ) h).iteratedFDeriv_comp_left
            (hΘcd.contDiffAt (x := x)) (i := j) (by exact_mod_cast hjk)
          have e1 : (ContinuousLinearMap.apply ℝ (Lp G 2 μ) h ∘ Θ) = fun y => Θ y h := rfl
          rw [e1] at hcomp
          have e2 : (iteratedFDeriv ℝ j Θ x m) h = iteratedFDeriv ℝ j (fun y => Θ y h) x m := by
            rw [hcomp]; rfl
          rw [e2]
          have h3 := (iteratedFDeriv ℝ j (fun y => Θ y h) x).le_opNorm m
          have h4 := (hslice h).2 j hjk x
          calc ‖iteratedFDeriv ℝ j (fun y => Θ y h) x m‖
              ≤ ‖iteratedFDeriv ℝ j (fun y => Θ y h) x‖ * ∏ i, ‖m i‖ := h3
            _ ≤ (d : ℝ) ^ j * ((B * ‖h‖) * (μ Set.univ).toReal ^ (1 / 2 : ℝ)) * ∏ i, ‖m i‖ :=
                mul_le_mul_of_nonneg_right h4 (by positivity)
            _ = ((d : ℝ) ^ j * (B * (μ Set.univ).toReal ^ (1 / 2 : ℝ)) * ∏ i, ‖m i‖) * ‖h‖ := by ring
        have hdd : (d : ℝ) ^ j ≤ (d : ℝ) ^ (j + 1) :=
          pow_le_pow_right₀ (by exact_mod_cast hd) (Nat.le_succ j)
        exact hbd.trans (mul_le_mul_of_nonneg_right hdd (by positivity))

end L2

end HRS.MS.Go
