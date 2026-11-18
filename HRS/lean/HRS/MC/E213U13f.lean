import HRS.MC.E213U13d

/-!
# Packet e213u13, file f: a countable-generation lemma for Gaussian families

A family `Y : κ → Ω → ℝ` of centred, jointly Gaussian random variables whose `L²`-classes form a separable,
infinite-dimensional set is the `L²`-span of an i.i.d. standard Gaussian sequence `ξ`:  every `Y i ∈ Q₁(ξ)`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace HRS.MC.E213U13

section Family

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {κ : Type*}

/-- A centred jointly Gaussian family. -/
structure GaussFam (P : Measure Ω) (Y : κ → Ω → ℝ) : Prop where
  meas : ∀ i, Measurable (Y i)
  fdd : ∀ (p : ℕ) (f : Fin p → κ), HasGaussianLaw (fun ω (a : Fin p) => Y (f a) ω) P
  mean : ∀ i, ∫ ω, Y i ω ∂P = 0

theorem GaussFam.memLp {Y : κ → Ω → ℝ} (h : GaussFam P Y) (i : κ) : MemLp (Y i) 2 P :=
  ((h.fdd 1 (fun _ => i)).eval (0 : Fin 1)).memLp_two

/-- The `L²`-class of `Y i`. -/
def GaussFam.cls {Y : κ → Ω → ℝ} (h : GaussFam P Y) (i : κ) : Lp ℝ 2 P := (h.memLp i).toLp (Y i)

theorem GaussFam.combo {Y : κ → Ω → ℝ} (h : GaussFam P Y) (s : Finset κ) (a : κ → ℝ) :
    ∃ v : ℝ≥0, P.map (fun ω => ∑ i ∈ s, a i * Y i ω) = gaussianReal 0 v := by
  classical
  set p := s.card with hp
  set f : Fin p → κ := fun j => (s.equivFin.symm j).1 with hf
  have hX := h.fdd p f
  set L : (Fin p → ℝ) →L[ℝ] ℝ := ∑ j : Fin p, a (f j) • (ContinuousLinearMap.proj j : (Fin p → ℝ) →L[ℝ] ℝ) with hL
  have hLX : ∀ ω, L (fun j => Y (f j) ω) = ∑ i ∈ s, a i * Y i ω := by
    intro ω
    simp only [hL, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul]
    rw [← Finset.sum_coe_sort s (fun i => a i * Y i ω)]
    exact (Equiv.sum_comp s.equivFin.symm (fun i : s => a i * Y i ω))
  have hG := hX.map L
  have hfun : (L ∘ fun ω (j : Fin p) => Y (f j) ω) = fun ω => ∑ i ∈ s, a i * Y i ω := by
    funext ω; exact hLX ω
  rw [hfun] at hG
  have hmean : ∫ ω, ∑ i ∈ s, a i * Y i ω ∂P = 0 := by
    rw [integral_finset_sum]
    · simp [integral_const_mul, h.mean]
    · intro i _
      exact ((h.memLp i).integrable (by norm_num)).const_mul _
  refine ⟨(Var[fun ω => ∑ i ∈ s, a i * Y i ω; P]).toNNReal, ?_⟩
  rw [hG.map_eq_gaussianReal, hmean]

theorem GaussFam.span {Y : κ → Ω → ℝ} (h : GaussFam P Y) :
    ∀ z ∈ Submodule.span ℝ (Set.range h.cls), ∃ v : ℝ≥0, P.map (z : Ω → ℝ) = gaussianReal 0 v := by
  classical
  intro z hz
  rw [Finsupp.mem_span_range_iff_exists_finsupp] at hz
  obtain ⟨c, rfl⟩ := hz
  obtain ⟨v, hv⟩ := h.combo c.support (fun i => c i)
  refine ⟨v, ?_⟩
  rw [← hv]
  refine Measure.map_congr ?_
  have h1 : ((c.sum fun i a => a • h.cls i : Lp ℝ 2 P) : Ω → ℝ) =ᵐ[P]
      fun ω => ∑ i ∈ c.support, c i * Y i ω := by
    rw [Finsupp.sum]
    have h2 := Lp.coeFn_fun_finsetSum c.support (fun i => c i • h.cls i)
    have h3 : ∀ i, (⇑(c i • h.cls i) : Ω → ℝ) =ᵐ[P] fun ω => c i * Y i ω := fun i => by
      filter_upwards [Lp.coeFn_smul (c i) (h.cls i), MemLp.coeFn_toLp (h.memLp i)] with ω h1 h2
      rw [h1, Pi.smul_apply, smul_eq_mul]
      have : (⇑(h.cls i) : Ω → ℝ) ω = Y i ω := h2
      rw [this]
    have h4 : ∀ᵐ ω ∂P, ∀ i ∈ c.support, (⇑(c i • h.cls i) : Ω → ℝ) ω = c i * Y i ω :=
      (ae_ball_iff c.support.countable_toSet).2 (fun i _ => h3 i)
    filter_upwards [h2, h4] with ω a b
    rw [a]
    exact Finset.sum_congr rfl fun i hi => b i hi
  exact h1

theorem GaussFam.sub_gauss {Y : κ → Ω → ℝ} (h : GaussFam P Y) (a b : κ) :
    ∃ v : ℝ≥0, P.map (fun ω => Y a ω - Y b ω) = gaussianReal 0 v := by
  have hX := h.fdd 2 ![a, b]
  set L : (Fin 2 → ℝ) →L[ℝ] ℝ := (ContinuousLinearMap.proj 0 : (Fin 2 → ℝ) →L[ℝ] ℝ) -
    (ContinuousLinearMap.proj 1 : (Fin 2 → ℝ) →L[ℝ] ℝ) with hL
  have hG := hX.map L
  have hfun : (L ∘ fun ω (j : Fin 2) => Y (![a, b] j) ω) = fun ω => Y a ω - Y b ω := by
    funext ω; simp [hL]
  rw [hfun] at hG
  have hmean : ∫ ω, (Y a ω - Y b ω) ∂P = 0 := by
    rw [integral_sub ((h.memLp a).integrable (by norm_num)) ((h.memLp b).integrable (by norm_num)),
      h.mean, h.mean, sub_zero]
  refine ⟨(Var[fun ω => Y a ω - Y b ω; P]).toNNReal, ?_⟩
  rw [hG.map_eq_gaussianReal, hmean]

theorem InQ1_congr {ξ : ℕ → Ω → ℝ} {hξ : IsStdGaussianSeq P ξ} {hm : ∀ i, Measurable (ξ i)} {Y Y' : Ω → ℝ}
    (h : Y =ᵐ[P] Y') (hY : InQ1 hξ hm Y) : InQ1 hξ hm Y' := by
  obtain ⟨h1, h2⟩ := hY
  have h1' : MemLp Y' 2 P := h1.ae_eq h
  refine ⟨h1', ?_⟩
  rwa [← MemLp.toLp_congr h1 h1' h]

theorem InQ2_congr {ξ : ℕ → Ω → ℝ} {hξ : IsStdGaussianSeq P ξ} {Y Y' : Ω → ℝ}
    (h : Y =ᵐ[P] Y') (hY : InQ2 hξ Y) : InQ2 hξ Y' := by
  obtain ⟨h1, h2⟩ := hY
  have h1' : MemLp Y' 2 P := h1.ae_eq h
  refine ⟨h1', ?_⟩
  rwa [← MemLp.toLp_congr h1 h1' h]


theorem GaussFam.exists_xi {Y : κ → Ω → ℝ} (h : GaussFam P Y)
    (hsep : TopologicalSpace.IsSeparable (Set.range h.cls))
    (hinf : ¬ FiniteDimensional ℝ (Submodule.span ℝ (Set.range h.cls))) :
    ∃ (ξ : ℕ → Ω → ℝ) (hm : ∀ i, Measurable (ξ i)) (hξ : IsStdGaussianSeq P ξ),
      ∀ i, InQ1 hξ hm (Y i) := by
  classical
  haveI : TopologicalSpace.SeparableSpace (Set.range h.cls) := hsep.separableSpace
  obtain ⟨c, hcc, hcs, hcl⟩ := TopologicalSpace.exists_countable_dense_subset (Set.range h.cls)
  have hne : c.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    apply hinf
    have hr : Set.range h.cls = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro y hy
      have := hcl hy
      rw [hne, closure_empty] at this
      exact this
    rw [hr, Submodule.span_empty]
    infer_instance
  obtain ⟨x, hx⟩ := hcc.exists_eq_range hne
  have hxsub : ∀ n, x n ∈ Set.range h.cls := fun n => hcs (hx ▸ ⟨n, rfl⟩)
  have hG : ∀ z ∈ Submodule.span ℝ (Set.range x), ∃ v : ℝ≥0, P.map (z : Ω → ℝ) = gaussianReal 0 v :=
    fun z hz => h.span z (Submodule.span_mono (by rintro _ ⟨n, rfl⟩; exact hxsub n) hz)
  have hinf' : ¬ FiniteDimensional ℝ (Submodule.span ℝ (Set.range x)) := by
    intro hfin
    apply hinf
    have hle : Submodule.span ℝ (Set.range h.cls) ≤ Submodule.span ℝ (Set.range x) := by
      refine Submodule.span_le.2 fun y hy => ?_
      have h1 := hcl hy
      rw [hx] at h1
      have hcl' : IsClosed ((Submodule.span ℝ (Set.range x) : Submodule ℝ (Lp ℝ 2 P)) : Set (Lp ℝ 2 P)) :=
        Submodule.closed_of_finiteDimensional _
      exact hcl'.closure_subset_iff.2 Submodule.subset_span h1
    exact Submodule.finiteDimensional_of_le hle
  obtain ⟨ξ, hm, hξ, hall⟩ := exists_stdGaussianSeq x hG hinf'
  refine ⟨ξ, hm, hξ, fun i => ?_⟩
  have hmem : h.cls i ∈ (Submodule.span ℝ (Set.range x)).topologicalClosure := by
    have h1 := hcl ⟨i, rfl⟩
    rw [hx] at h1
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
    exact closure_mono Submodule.subset_span h1
  exact InQ1_congr (MemLp.coeFn_toLp (h.memLp i)) (hall _ hmem)

end Family
end HRS.MC.E213U13
