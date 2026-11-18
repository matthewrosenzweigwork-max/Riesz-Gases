import Mathlib

/-!
# S8.2 T8A.S02a: strong measurability of the `Lp`-valued section map of a jointly measurable function (generic)

Let `ν` be a finite measure on `β` and `F : α → β → E` jointly measurable.  If `V t ∈ Lp E 2 ν` represents
the section `F t` for every `t`, then `V` is strongly measurable.  No separability of `Lp E 2 ν` is used:
the proof is a monotone-class argument on indicators of product-measurable sets, then simple functions,
then `approxOn`.  The a.e. version (`r26t8a_s02a_sections`) takes a jointly a.e.-strongly measurable `F` and
sections identified only for almost every `t`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal
namespace HRS.MS.R26T8A

section
variable {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem r26t8a_s02a_icl_congr {ν : Measure β} {s t : Set β} (h : s = t) (hs : MeasurableSet s)
    (ht : MeasurableSet t) (hs' : ν s ≠ ∞) (ht' : ν t ≠ ∞) (c : E) :
    indicatorConstLp 2 hs hs' c = indicatorConstLp 2 ht ht' c := by
  subst h; rfl

/-- indicators of product-measurable sets -/
theorem r26t8a_s02a_set (ν : Measure β) [IsFiniteMeasure ν] (c : E) (A : Set (α × β))
    (hA : MeasurableSet A) :
    ∀ W : α → Lp E 2 ν, (∀ t, ⇑(W t) =ᵐ[ν] fun ω => A.indicator (fun _ => c) (t, ω)) →
      StronglyMeasurable W := by
  classical
  refine MeasurableSpace.induction_on_inter
    (C := fun A _ => ∀ W : α → Lp E 2 ν,
      (∀ t, ⇑(W t) =ᵐ[ν] fun ω => A.indicator (fun _ => c) (t, ω)) → StronglyMeasurable W)
    generateFrom_prod.symm isPiSystem_prod ?_ ?_ ?_ ?_ A hA
  · intro W hW
    have : W = fun _ => 0 := by
      funext t
      refine Lp.ext ?_
      filter_upwards [hW t, Lp.coeFn_zero E 2 ν] with ω h1 h2
      rw [h1, h2]
      simp
    rw [this]
    exact stronglyMeasurable_const
  · intro A hA W hW
    obtain ⟨S, hS, T, hT, rfl⟩ := hA
    have hS' : MeasurableSet S := hS
    have hT' : MeasurableSet T := hT
    let w : Lp E 2 ν := indicatorConstLp 2 hT' (measure_ne_top ν T) c
    have : W = fun t => S.indicator (fun _ => w) t := by
      funext t
      by_cases ht : t ∈ S
      · rw [indicator_of_mem ht]
        refine Lp.ext ?_
        filter_upwards [hW t, indicatorConstLp_coeFn (p := 2) (μ := ν) (hs := hT')
          (hμs := measure_ne_top ν T) (c := c)] with ω h1 h2
        rw [h1]
        refine Eq.trans ?_ h2.symm
        simp [Set.indicator_apply, ht]
      · rw [indicator_of_notMem ht]
        refine Lp.ext ?_
        filter_upwards [hW t, Lp.coeFn_zero E 2 ν] with ω h1 h2
        rw [h1, h2]
        simp [Set.indicator_apply, ht]
    rw [this]
    exact stronglyMeasurable_const.indicator hS'
  · intro A hA ih W hW
    obtain ⟨K, hK⟩ : ∃ K : Lp E 2 ν, ⇑K =ᵐ[ν] fun _ => c := by
      refine ⟨indicatorConstLp 2 MeasurableSet.univ (measure_ne_top ν univ) c, ?_⟩
      filter_upwards [indicatorConstLp_coeFn (p := 2) (μ := ν) (hs := MeasurableSet.univ)
        (hμs := measure_ne_top ν univ) (c := c)] with ω h
      exact h.trans (by simp)
    have hW' : StronglyMeasurable (fun t => K - W t) := by
      refine ih (fun t => K - W t) fun t => ?_
      filter_upwards [Lp.coeFn_sub K (W t), hW t, hK] with ω h1 h2 h3
      rw [h1, Pi.sub_apply, h2, h3]
      by_cases hx : (t, ω) ∈ A
      · simp [hx]
      · simp [hx]
    have : W = fun t => K - (K - W t) := by
      funext t; exact (sub_sub_cancel K (W t)).symm
    rw [this]
    exact stronglyMeasurable_const.sub hW'
  · intro f hdisj hfm ih W hW
    have hsec : ∀ (n : ℕ) (t : α), MeasurableSet (Prod.mk t ⁻¹' f n) := fun n t =>
      measurable_prodMk_left (hfm n)
    let Wn : ℕ → α → Lp E 2 ν := fun n t =>
      indicatorConstLp 2 (hsec n t) (measure_ne_top ν _) c
    have hWn : ∀ n, StronglyMeasurable (Wn n) := fun n => by
      refine ih n (Wn n) fun t => ?_
      filter_upwards [indicatorConstLp_coeFn (p := 2) (μ := ν) (hs := hsec n t)
        (hμs := measure_ne_top ν _) (c := c)] with ω h
      exact h.trans (by simp [Set.indicator_apply])
    have hSM : ∀ N : ℕ, StronglyMeasurable (fun t => ∑ n ∈ Finset.range N, Wn n t) := fun N =>
      Finset.stronglyMeasurable_fun_sum _ fun n _ => hWn n
    have hBm : ∀ (N : ℕ) (t : α), MeasurableSet (⋃ n, ⋃ (_ : n < N), Prod.mk t ⁻¹' f n) :=
      fun N t => MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun _ => hsec n t
    have hS : ∀ (N : ℕ) (t : α), ∑ n ∈ Finset.range N, Wn n t =
        indicatorConstLp 2 (hBm N t) (measure_ne_top ν _) c := by
      intro N t
      induction N with
      | zero =>
        simp only [Finset.range_zero, Finset.sum_empty]
        rw [← indicatorConstLp_empty (p := 2) (μ := ν) (c := c)]
        exact r26t8a_s02a_icl_congr (by ext; simp) _ _ _ _ c
      | succ N ih' =>
        rw [Finset.sum_range_succ, ih']
        have hd : Disjoint (⋃ n, ⋃ (_ : n < N), Prod.mk t ⁻¹' f n) (Prod.mk t ⁻¹' f N) := by
          rw [Set.disjoint_iUnion_left]
          intro n
          rw [Set.disjoint_iUnion_left]
          intro hn
          exact (hdisj (by omega : n ≠ N)).preimage _
        have := indicatorConstLp_disjoint_union (p := 2) (μ := ν) (hBm N t) (hsec N t)
          (measure_ne_top ν _) (measure_ne_top ν _) hd c
        refine this.symm ▸ ?_
        refine r26t8a_s02a_icl_congr ?_ _ _ _ _ c
        ext ω
        simp only [mem_union, mem_iUnion, exists_prop, mem_preimage]
        constructor
        · rintro (⟨n, hn, h⟩ | h)
          · exact ⟨n, by omega, h⟩
          · exact ⟨N, by omega, h⟩
        · rintro ⟨n, hn, h⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 hn with hn | rfl
          · exact Or.inl ⟨n, hn, h⟩
          · exact Or.inr h
    have hconv : ∀ t, Tendsto (fun N => ∑ n ∈ Finset.range N, Wn n t) atTop (𝓝 (W t)) := by
      intro t
      have hUm : MeasurableSet (⋃ n, Prod.mk t ⁻¹' f n) := MeasurableSet.iUnion fun n => hsec n t
      have hWt : W t = indicatorConstLp 2 hUm (measure_ne_top ν _) c := by
        refine Lp.ext ?_
        filter_upwards [hW t, indicatorConstLp_coeFn (p := 2) (μ := ν) (hs := hUm)
          (hμs := measure_ne_top ν _) (c := c)] with ω h1 h2
        rw [h1, h2]
        simp [Set.indicator_apply]
      rw [hWt]
      simp_rw [hS]
      refine tendsto_indicatorConstLp_set (by norm_num) ?_
      have hdis : Pairwise fun n m => Disjoint (Prod.mk t ⁻¹' f n) (Prod.mk t ⁻¹' f m) :=
        fun n m hnm => (hdisj hnm).preimage _
      have h0 := tendsto_measure_biUnion_Ici_zero_of_pairwise_disjoint (μ := ν)
        (fun i => (hsec i t).nullMeasurableSet) hdis
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0
        (fun _ => zero_le) fun N => ?_
      refine measure_mono ?_
      intro ω hω
      have hsub : (⋃ n, ⋃ (_ : n < N), Prod.mk t ⁻¹' f n) ⊆ ⋃ n, Prod.mk t ⁻¹' f n := by
        intro x hx
        simp only [mem_iUnion, exists_prop] at hx ⊢
        obtain ⟨n, -, h⟩ := hx
        exact ⟨n, h⟩
      rw [symmDiff_of_le hsub] at hω
      obtain ⟨hω1, hω2⟩ := hω
      simp only [mem_iUnion, exists_prop, mem_preimage] at hω1 hω2 ⊢
      obtain ⟨n, hn⟩ := hω1
      refine ⟨n, ?_, hn⟩
      by_contra hlt
      exact hω2 ⟨n, by omega, hn⟩
    exact stronglyMeasurable_of_tendsto atTop hSM (tendsto_pi_nhds.2 hconv)

/-- simple functions on the product -/
theorem r26t8a_s02a_simple (ν : Measure β) [IsFiniteMeasure ν] (Φ : SimpleFunc (α × β) E) :
    ∀ W : α → Lp E 2 ν, (∀ t, ⇑(W t) =ᵐ[ν] fun ω => Φ (t, ω)) → StronglyMeasurable W := by
  classical
  induction Φ using SimpleFunc.induction with
  | const c hs =>
    rename_i s
    intro W hW
    refine r26t8a_s02a_set ν c s hs W fun t => ?_
    filter_upwards [hW t] with ω h
    rw [h]
    simp [SimpleFunc.piecewise_apply, Set.indicator_apply]
  | add hd h1 h2 =>
    rename_i f g
    intro W hW
    have hm : ∀ (φ : SimpleFunc (α × β) E) (t : α), MemLp (fun ω => φ (t, ω)) 2 ν := fun φ t =>
      (φ.comp (Prod.mk t) measurable_prodMk_left).memLp_of_isFiniteMeasure 2 ν
    let W1 : α → Lp E 2 ν := fun t => (hm f t).toLp _
    let W2 : α → Lp E 2 ν := fun t => (hm g t).toLp _
    have hW1 : StronglyMeasurable W1 := h1 W1 fun t => (hm f t).coeFn_toLp
    have hW2 : StronglyMeasurable W2 := h2 W2 fun t => (hm g t).coeFn_toLp
    have : W = fun t => W1 t + W2 t := by
      funext t
      refine Lp.ext ?_
      filter_upwards [hW t, Lp.coeFn_add (W1 t) (W2 t), (hm f t).coeFn_toLp,
        (hm g t).coeFn_toLp] with ω a b c d
      rw [a, b]
      simp [W1, W2, c, d]
    rw [this]
    exact hW1.add hW2

/-- core: jointly measurable `F`, sections identified for all `t` -/
theorem r26t8a_s02a_core [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (ν : Measure β) [IsFiniteMeasure ν] (F : α × β → E) (hF : Measurable F) (V : α → Lp E 2 ν)
    (hV : ∀ t, ⇑(V t) =ᵐ[ν] fun ω => F (t, ω)) : StronglyMeasurable V := by
  let s : Set E := range F ∪ {0}
  have h0 : (0 : E) ∈ s := by simp [s]
  let Φ : ℕ → SimpleFunc (α × β) E := fun n => SimpleFunc.approxOn F hF s 0 h0 n
  have hm : ∀ (n : ℕ) (t : α), MemLp (fun ω => Φ n (t, ω)) 2 ν := fun n t =>
    ((Φ n).comp (Prod.mk t) measurable_prodMk_left).memLp_of_isFiniteMeasure 2 ν
  let W : ℕ → α → Lp E 2 ν := fun n t => (hm n t).toLp _
  have hW : ∀ n, StronglyMeasurable (W n) := fun n =>
    r26t8a_s02a_simple ν (Φ n) (W n) fun t => (hm n t).coeFn_toLp
  have hconv : ∀ t, Tendsto (fun n => W n t) atTop (𝓝 (V t)) := by
    intro t
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
    have hFt : Measurable (F ∘ Prod.mk t) := hF.comp measurable_prodMk_left
    have hfin : eLpNorm (fun ω => (F ∘ Prod.mk t) ω - 0) 2 ν < ∞ := by
      have := (Lp.memLp (V t)).eLpNorm_lt_top
      rw [eLpNorm_congr_ae (hV t)] at this
      simpa using this
    have key := SimpleFunc.tendsto_approxOn_Lp_eLpNorm (E := E) (p := 2) hFt h0
      (by norm_num) (μ := ν) (Eventually.of_forall fun ω => subset_closure (Or.inl ⟨(t, ω), rfl⟩))
      hfin
    refine key.congr fun n => ?_
    refine eLpNorm_congr_ae ?_
    filter_upwards [(hm n t).coeFn_toLp, hV t] with ω h1 h2
    have h1' : ⇑(W n t) ω = Φ n (t, ω) := h1
    have e : (SimpleFunc.approxOn (F ∘ Prod.mk t) hFt s 0 h0 n) ω = Φ n (t, ω) := rfl
    simp only [Pi.sub_apply, Function.comp_apply]
    rw [e, h1', h2]
  exact stronglyMeasurable_of_tendsto atTop hW (tendsto_pi_nhds.2 hconv)

/-- a.e. version -/
theorem r26t8a_s02a_sections [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : Measure α) [SFinite μ] (ν : Measure β) [IsFiniteMeasure ν] (F : α → β → E)
    (hF : AEStronglyMeasurable (Function.uncurry F) (μ.prod ν)) (V : α → Lp E 2 ν)
    (hV : ∀ᵐ t ∂μ, ⇑(V t) =ᵐ[ν] F t) : AEStronglyMeasurable V μ := by
  classical
  let Fm : α × β → E := AEStronglyMeasurable.mk (Function.uncurry F) hF
  have hF'm : Measurable Fm := hF.stronglyMeasurable_mk.measurable
  have hae1 : ∀ᵐ t ∂μ, ∀ᵐ ω ∂ν, F t ω = Fm (t, ω) :=
    Measure.ae_ae_of_ae_prod (hF.ae_eq_mk)
  have hgood : ∀ᵐ t ∂μ, ⇑(V t) =ᵐ[ν] fun ω => Fm (t, ω) := by
    filter_upwards [hV, hae1] with t h1 h2
    exact h1.trans h2
  set N : Set α := toMeasurable μ {t | ¬ (⇑(V t) =ᵐ[ν] fun ω => Fm (t, ω))} with hNdef
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  have hN0 : μ N = 0 := by
    rw [hNdef, measure_toMeasurable]
    exact ae_iff.1 hgood
  have hsub : {t | ¬ (⇑(V t) =ᵐ[ν] fun ω => Fm (t, ω))} ⊆ N := subset_toMeasurable _ _
  let F'' : α × β → E := fun p => if p.1 ∈ N then 0 else Fm p
  have hF'' : Measurable F'' := Measurable.ite (measurable_fst hNm) measurable_const hF'm
  let V'' : α → Lp E 2 ν := fun t => if t ∈ N then 0 else V t
  have hV'' : ∀ t, ⇑(V'' t) =ᵐ[ν] fun ω => F'' (t, ω) := by
    intro t
    by_cases ht : t ∈ N
    · simp only [V'', F'', if_pos ht]
      exact Lp.coeFn_zero E 2 ν
    · simp only [V'', F'', if_neg ht]
      by_contra h
      exact ht (hsub h)
  have hSM := r26t8a_s02a_core ν F'' hF'' V'' hV''
  refine hSM.aestronglyMeasurable.congr ?_
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with t ht
  simp [V'', ht]

end

end HRS.MS.R26T8A

end
