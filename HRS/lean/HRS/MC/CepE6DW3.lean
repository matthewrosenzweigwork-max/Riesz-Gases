import HRS.MC.CepE6DW2

/-!
# Packet CEPE6D, part 3c: the weak-limit lemma W (statement and proof)

**Theorem (3), `cepe6d_weak_limit`.**  Let `b_n : ℝ → ℝ^N` be continuous, `a_n(t) = ∫_0^t b_n` (so `a_n(0) = 0`, `a_n ∈ C¹`,
`TV(a_n) = ∫_0^T ‖b_n‖`), `a_n → A` uniformly on `[0,T]` and `∫_0^T ‖b_n‖ ≤ K` eventually.  Then there is a bounded linear
functional `Λ` on `C([0,T]; ℝ^N)`, `|Λ f| ≤ K ‖f‖_∞`, with
* `Λ f = ⟨f(T), A(T)⟩ - ∫_0^T ⟨f', A⟩` for `C¹` `f` (so `Λ` depends only on `A`: `Λ f = ∫ f · dA`);
* `∫_0^T ⟨f_n, b_n⟩ ds → Λ f` whenever `f_n → f` uniformly on `[0,T]` (all continuous);
* `TV(A; [0,T]) ≤ K` (`eVariationOn`, Euclidean distance).
-/

open Set Filter Topology
open scoped RealInnerProductSpace ContDiff

noncomputable section

namespace HRS.MC.CepE6D

variable {N : ℕ}

theorem cepe6d_weak_limit {T : ℝ} (hT : 0 ≤ T) {b : ℕ → ℝ → Ch6D N} (hb : ∀ n, Continuous (b n))
    {A : ℝ → Ch6D N}
    (hA : TendstoUniformlyOn (fun n t => ∫ s in (0 : ℝ)..t, b n s) A atTop (Icc 0 T))
    {K : ℝ} (hK : ∀ᶠ n in atTop, ∫ s in (0 : ℝ)..T, ‖b n s‖ ≤ K) :
    ∃ Λ : C(Icc (0 : ℝ) T, Ch6D N) →L[ℝ] ℝ,
      (∀ f, |Λ f| ≤ K * ‖f‖) ∧
      (∀ (f : ℝ → Ch6D N) (hf : ContDiff ℝ 1 f),
        Λ (ofFun f hf.continuous.continuousOn) = ⟪f T, A T⟫ - ∫ s in (0 : ℝ)..T, ⟪deriv f s, A s⟫) ∧
      (∀ (fn : ℕ → ℝ → Ch6D N) (f : ℝ → Ch6D N) (_ : ∀ n, ContinuousOn (fn n) (Icc 0 T))
        (hf : ContinuousOn f (Icc 0 T)), TendstoUniformlyOn fn f atTop (Icc 0 T) →
        Tendsto (fun n => ∫ s in (0 : ℝ)..T, ⟪fn n s, b n s⟫) atTop (𝓝 (Λ (ofFun f hf)))) ∧
      eVariationOn A (Icc 0 T) ≤ ENNReal.ofReal K := by
  have hA' : TendstoUniformlyOn (fun n => prim (b n)) A atTop (Icc 0 T) := hA
  have hc : ∀ f : C(Icc (0 : ℝ) T, Ch6D N), ContinuousOn (extFun hT f) (Icc 0 T) :=
    fun f => (extFun_continuous hT f).continuousOn
  have hbd : ∀ f : C(Icc (0 : ℝ) T, Ch6D N), |LimL T b (extFun hT f)| ≤ K * ‖f‖ := by
    intro f
    have := abs_LimL_le hT hb hA' hK (hc f) (M := ‖f‖) fun s hs => norm_extFun_le hT f hs
    linarith
  let ℓ : C(Icc (0 : ℝ) T, Ch6D N) →ₗ[ℝ] ℝ :=
    { toFun := fun f => LimL T b (extFun hT f)
      map_add' := fun f g => by
        have h1 := tendsto_LimL hT hb hA' hK (hc (f + g))
        have h2 := (tendsto_LimL hT hb hA' hK (hc f)).add (tendsto_LimL hT hb hA' hK (hc g))
        have e : (fun n => Lfun T (b n) (extFun hT (f + g))) =
            fun n => Lfun T (b n) (extFun hT f) + Lfun T (b n) (extFun hT g) := by
          funext n
          have : extFun hT (f + g) = fun s => extFun hT f s + extFun hT g s :=
            funext (extFun_add hT f g)
          rw [this]; exact Lfun_add hT (hb n).continuousOn (hc f) (hc g)
        rw [e] at h1
        exact tendsto_nhds_unique h1 h2
      map_smul' := fun c f => by
        have h1 := tendsto_LimL hT hb hA' hK (hc (c • f))
        have h2 := (tendsto_LimL hT hb hA' hK (hc f)).const_mul c
        have e : (fun n => Lfun T (b n) (extFun hT (c • f))) =
            fun n => c * Lfun T (b n) (extFun hT f) := by
          funext n
          have : extFun hT (c • f) = fun s => c • extFun hT f s := funext (extFun_smul hT c f)
          rw [this]; exact Lfun_smul c (b n) _
        rw [e] at h1
        simpa using tendsto_nhds_unique h1 h2 }
  have hℓ : ∀ f, ‖ℓ f‖ ≤ K * ‖f‖ := fun f => by
    rw [Real.norm_eq_abs]; exact hbd f
  let Λ : C(Icc (0 : ℝ) T, Ch6D N) →L[ℝ] ℝ := ℓ.mkContinuous K hℓ
  have hΛ : ∀ f, Λ f = LimL T b (extFun hT f) := fun f => rfl
  have hΛof : ∀ (f : ℝ → Ch6D N) (hf : ContinuousOn f (Icc 0 T)), Λ (ofFun f hf) = LimL T b f := by
    intro f hf
    rw [hΛ]
    exact LimL_congr hT fun s hs => extFun_ofFun hT f hf hs
  refine ⟨Λ, fun f => by have h := hℓ f; rw [Real.norm_eq_abs] at h; exact h, ?_, ?_, eVariation_le hT hb hA' hK⟩
  · intro f hf
    rw [hΛof]
    exact tendsto_nhds_unique (tendsto_LimL hT hb hA' hK hf.continuous.continuousOn)
      (tendsto_Lfun_C1 hT hb hA' hf)
  · intro fn f hfn hf hu
    rw [hΛof f hf]
    obtain ⟨n0, hn0⟩ := hK.exists
    have hK0 : 0 ≤ K := (integral_norm_nonneg hT (b n0)).trans hn0
    have hlim := tendsto_LimL hT hb hA' hK hf
    rw [Metric.tendsto_nhds]
    intro ε hε
    set η : ℝ := ε / (2 * (K + 1)) with hη
    have hηpos : 0 < η := by positivity
    have hηK : η * K ≤ ε / 2 := by
      rw [hη, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    filter_upwards [hK, Metric.tendsto_nhds.1 hlim (ε / 2) (by positivity),
      Metric.tendstoUniformlyOn_iff.1 hu η hηpos] with n hn hn2 hn3
    have hd : |Lfun T (b n) (fn n) - Lfun T (b n) f| ≤ ε / 2 := by
      rw [← Lfun_sub hT (hb n).continuousOn (hfn n) hf]
      refine (abs_Lfun_le hT (hb n).continuousOn (M := η) fun s hs => ?_).trans ?_
      · have := hn3 s hs
        rw [dist_comm, dist_eq_norm] at this
        exact this.le
      · calc η * ∫ s in (0 : ℝ)..T, ‖b n s‖ ≤ η * K := mul_le_mul_of_nonneg_left hn hηpos.le
          _ ≤ ε / 2 := hηK
    rw [Real.dist_eq] at hn2 ⊢
    calc |Lfun T (b n) (fn n) - LimL T b f|
        = |(Lfun T (b n) (fn n) - Lfun T (b n) f) + (Lfun T (b n) f - LimL T b f)| := by ring_nf
      _ ≤ |Lfun T (b n) (fn n) - Lfun T (b n) f| + |Lfun T (b n) f - LimL T b f| := abs_add_le _ _
      _ < ε := by linarith

/-- The same with `b_n` only continuous on `[0,T]` (reduces to `cepe6d_weak_limit` by clamping). -/
theorem cepe6d_weak_limit_on {T : ℝ} (hT : 0 ≤ T) {b : ℕ → ℝ → Ch6D N}
    (hb : ∀ n, ContinuousOn (b n) (Icc 0 T)) {A : ℝ → Ch6D N}
    (hA : TendstoUniformlyOn (fun n t => ∫ s in (0 : ℝ)..t, b n s) A atTop (Icc 0 T))
    {K : ℝ} (hK : ∀ᶠ n in atTop, ∫ s in (0 : ℝ)..T, ‖b n s‖ ≤ K) :
    ∃ Λ : C(Icc (0 : ℝ) T, Ch6D N) →L[ℝ] ℝ,
      (∀ f, |Λ f| ≤ K * ‖f‖) ∧
      (∀ (f : ℝ → Ch6D N) (hf : ContDiff ℝ 1 f),
        Λ (ofFun f hf.continuous.continuousOn) = ⟪f T, A T⟫ - ∫ s in (0 : ℝ)..T, ⟪deriv f s, A s⟫) ∧
      (∀ (fn : ℕ → ℝ → Ch6D N) (f : ℝ → Ch6D N) (_ : ∀ n, ContinuousOn (fn n) (Icc 0 T))
        (hf : ContinuousOn f (Icc 0 T)), TendstoUniformlyOn fn f atTop (Icc 0 T) →
        Tendsto (fun n => ∫ s in (0 : ℝ)..T, ⟪fn n s, b n s⟫) atTop (𝓝 (Λ (ofFun f hf)))) ∧
      eVariationOn A (Icc 0 T) ≤ ENNReal.ofReal K := by
  let bb : ℕ → ℝ → Ch6D N := fun n s => b n (max 0 (min s T))
  have hmem : ∀ s : ℝ, max 0 (min s T) ∈ Icc (0 : ℝ) T := fun s =>
    ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩
  have hbbc : ∀ n, Continuous (bb n) := fun n =>
    (hb n).comp_continuous (continuous_const.max (continuous_id.min continuous_const)) hmem
  have hbbeq : ∀ n, ∀ s ∈ Icc (0 : ℝ) T, bb n s = b n s := by
    intro n s hs
    simp only [bb]
    rw [min_eq_left hs.2, max_eq_right hs.1]
  have hint : ∀ n, ∀ t ∈ Icc (0 : ℝ) T, ∫ s in (0 : ℝ)..t, bb n s = ∫ s in (0 : ℝ)..t, b n s := by
    intro n t ht
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le ht.1] at hs
    exact hbbeq n s ⟨hs.1, hs.2.trans ht.2⟩
  have hA2 : TendstoUniformlyOn (fun n t => ∫ s in (0 : ℝ)..t, bb n s) A atTop (Icc 0 T) :=
    hA.congr (Filter.Eventually.of_forall fun n t ht => (hint n t ht).symm)
  have hnorm : ∀ n, ∫ s in (0 : ℝ)..T, ‖bb n s‖ = ∫ s in (0 : ℝ)..T, ‖b n s‖ := by
    intro n
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le hT] at hs
    simp only [hbbeq n s hs]
  have hK2 : ∀ᶠ n in atTop, ∫ s in (0 : ℝ)..T, ‖bb n s‖ ≤ K := by
    filter_upwards [hK] with n hn
    rwa [hnorm n]
  obtain ⟨Λ, h1, h2, h3, h4⟩ := cepe6d_weak_limit hT hbbc hA2 hK2
  refine ⟨Λ, h1, h2, ?_, h4⟩
  intro fn f hfn hf hu
  have := h3 fn f hfn hf hu
  refine this.congr fun n => ?_
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le hT] at hs
  simp only [hbbeq n s hs]

end HRS.MC.CepE6D
