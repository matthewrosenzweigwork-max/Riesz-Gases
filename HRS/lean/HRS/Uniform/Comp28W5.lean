import HRS.Uniform.Comp28W4

/-!
# COMP-28, Wasserstein part, W5: the law of a continuous `H`-valued process is determined by finite-dimensional laws
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.Uniform.Comp28

open HRS HRS.Uniform HRS.Uniform.Q45

section Embed

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

/-- A finite measure on a countable product of `H` is determined by its finite-dimensional marginals. -/
theorem measure_ext_of_restrict_H {ι : Type*} {μ ν : Measure (ι → H)} [IsFiniteMeasure μ]
    (h : ∀ J : Finset ι, μ.map J.restrict = ν.map J.restrict) : μ = ν := by
  have hr : ∀ J : Finset ι, Measurable (J.restrict : (ι → H) → (J → H)) := fun J =>
    measurable_pi_iff.2 fun i => measurable_pi_apply (i : ι)
  have huniv : μ Set.univ = ν Set.univ := by
    have := congrArg (fun m : Measure ((∅ : Finset ι) → H) => m Set.univ) (h ∅)
    simp only [Measure.map_apply (hr ∅) MeasurableSet.univ, Set.preimage_univ] at this
    exact this
  refine ext_of_generate_finite (measurableCylinders fun _ : ι => H)
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders ?_ huniv
  intro t ht
  obtain ⟨J, S, hS, rfl⟩ := (mem_measurableCylinders t).1 ht
  have h1 := congrArg (fun m : Measure (J → H) => m S) (h J)
  simp only [Measure.map_apply (hr J) hS] at h1
  exact h1

/-- The evaluation of a path at a sequence of times. -/
def pathEvals (T : ℝ) (s : ℕ → Set.Icc (0 : ℝ) T) : PathSp T H → (ℕ → H) :=
  fun w n => pcm w (s n)

theorem continuous_pathEvals (T : ℝ) (s : ℕ → Set.Icc (0 : ℝ) T) :
    Continuous (pathEvals (H := H) T s) :=
  continuous_pi fun n => by
    have : Continuous fun w : C(Set.Icc (0 : ℝ) T, H) => w (s n) := continuous_eval_const (s n)
    exact this

theorem pathEvals_injective (T : ℝ) (s : ℕ → Set.Icc (0 : ℝ) T) (hs : DenseRange s) :
    Function.Injective (pathEvals (H := H) T s) := by
  intro w w' h
  have hc : Continuous fun t => pcm w t := (pcm w).continuous
  have hc' : Continuous fun t => pcm w' t := (pcm w').continuous
  have hfun : (fun t => pcm w t) = fun t => pcm w' t := hs.equalizer hc hc' (funext fun n => congrFun h n)
  exact ContinuousMap.ext fun t => congrFun hfun t

theorem measurableEmbedding_pathEvals (T : ℝ) (s : ℕ → Set.Icc (0 : ℝ) T) (hs : DenseRange s) :
    MeasurableEmbedding (pathEvals (H := H) T s) := by
  have : PolishSpace (PathSp T H) := inferInstanceAs (PolishSpace C(Set.Icc (0 : ℝ) T, H))
  exact (continuous_pathEvals T s).measurable.measurableEmbedding (pathEvals_injective T s hs)

end Embed

section PathLaw

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

/-- On a path with continuous time sections, the evaluations of the window path are the section values. -/
theorem pathEvals_windowPath {T : ℝ} (s : ℕ → Set.Icc (0 : ℝ) T) {Ω : Type*} (Y : ℝ → Ω → H) {ω : Ω}
    (h : ContinuousOn (fun t => Y t ω) (Set.Icc 0 T)) :
    pathEvals (H := H) T s (windowPath 0 T Y ω) = fun n => Y (s n : ℝ) ω := by
  funext n
  unfold pathEvals
  rw [pcm_windowPath Y h (s n)]

/-- **Uniqueness in law for continuous processes in `H`**: the law of the window path is determined by the joint
laws of finitely many sections at finitely many times of `[0,T]`. -/
theorem law_path_eq_of_fdd {T : ℝ} (hT : 0 ≤ T) {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (Y : ℝ → Ω → H) (Y' : ℝ → Ω' → H) (hm : ∀ t, Measurable (Y t)) (hm' : ∀ t, Measurable (Y' t))
    (hc : ∀ᵐ ω ∂P, ContinuousOn (fun t => Y t ω) (Set.Icc 0 T))
    (hc' : ∀ᵐ ω ∂P', ContinuousOn (fun t => Y' t ω) (Set.Icc 0 T))
    (hfdd : ∀ (p : ℕ) (ts : Fin p → ℝ), (∀ a, ts a ∈ Set.Icc 0 T) →
      P.map (fun ω a => Y (ts a) ω) = P'.map (fun ω a => Y' (ts a) ω)) :
    law P (windowPath 0 T Y) = law P' (windowPath 0 T Y') := by
  haveI : Nonempty (Set.Icc (0 : ℝ) T) := ⟨⟨0, le_rfl, hT⟩⟩
  set s : ℕ → Set.Icc (0 : ℝ) T := TopologicalSpace.denseSeq (Set.Icc (0 : ℝ) T) with hsdef
  have hs : DenseRange s := TopologicalSpace.denseRange_denseSeq _
  have hemb := measurableEmbedding_pathEvals (H := H) T s hs
  obtain ⟨g, hgm, hg⟩ := hemb.exists_measurable_extend (g := id) measurable_id (fun _ => ⟨0⟩)
  set Ψ₀ : Ω → (ℕ → H) := fun ω n => Y (s n : ℝ) ω with hΨ₀
  set Ψ₀' : Ω' → (ℕ → H) := fun ω n => Y' (s n : ℝ) ω with hΨ₀'
  have hΨm : Measurable Ψ₀ := measurable_pi_iff.2 fun n => hm _
  have hΨm' : Measurable Ψ₀' := measurable_pi_iff.2 fun n => hm' _
  have hae : windowPath 0 T Y =ᵐ[P] fun ω => g (Ψ₀ ω) := by
    filter_upwards [hc] with ω h
    have := pathEvals_windowPath s Y h
    have h2 := congrFun hg (windowPath 0 T Y ω)
    simp only [Function.comp, id] at h2
    rw [← h2, this]
  have hae' : windowPath 0 T Y' =ᵐ[P'] fun ω => g (Ψ₀' ω) := by
    filter_upwards [hc'] with ω h
    have := pathEvals_windowPath s Y' h
    have h2 := congrFun hg (windowPath 0 T Y' ω)
    simp only [Function.comp, id] at h2
    rw [← h2, this]
  have hlaw : P.map Ψ₀ = P'.map Ψ₀' := by
    refine measure_ext_of_restrict_H fun J => ?_
    have hr : ∀ J : Finset ℕ, Measurable (J.restrict : (ℕ → H) → (J → H)) := fun J =>
      measurable_pi_iff.2 fun i => measurable_pi_apply (i : ℕ)
    rw [Measure.map_map (hr J) hΨm, Measure.map_map (hr J) hΨm']
    let e : J ≃ Fin J.card := J.equivFin
    set ts : Fin J.card → ℝ := fun a => (s (e.symm a : ℕ) : ℝ) with hts
    have hmem : ∀ a, ts a ∈ Set.Icc (0 : ℝ) T := fun a => (s _).2
    have hf := hfdd J.card ts hmem
    have hre : Measurable (fun (v : Fin J.card → H) (j : J) => v (e j)) :=
      measurable_pi_iff.2 fun j => measurable_pi_apply (e j)
    have e1 : (J.restrict ∘ Ψ₀) = (fun (v : Fin J.card → H) (j : J) => v (e j)) ∘
        (fun ω a => Y (ts a) ω) := by
      funext ω j
      simp [hΨ₀, hts, Function.comp, Finset.restrict]
    have e2 : (J.restrict ∘ Ψ₀') = (fun (v : Fin J.card → H) (j : J) => v (e j)) ∘
        (fun ω a => Y' (ts a) ω) := by
      funext ω j
      simp [hΨ₀', hts, Function.comp, Finset.restrict]
    have hmv : Measurable (fun ω a => Y (ts a) ω) := measurable_pi_iff.2 fun a => hm _
    have hmv' : Measurable (fun ω a => Y' (ts a) ω) := measurable_pi_iff.2 fun a => hm' _
    rw [e1, e2, ← Measure.map_map hre hmv, ← Measure.map_map hre hmv', hf]
  unfold law
  rw [Measure.map_congr hae, Measure.map_congr hae']
  have h1 : (fun ω => g (Ψ₀ ω)) = g ∘ Ψ₀ := rfl
  have h2 : (fun ω => g (Ψ₀' ω)) = g ∘ Ψ₀' := rfl
  rw [h1, h2, ← Measure.map_map hgm hΨm, ← Measure.map_map hgm hΨm', hlaw]

end PathLaw

section FddG

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

open HRS.Uniform.Q07c in
theorem comb_eq_dual {Ω : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι] (G : ℝ → Ω → H) (τ : ι → ℝ) {T : ℝ}
    (hτ : ∀ i, 0 ≤ τ i ∧ τ i ≤ T) (L : StrongDual ℝ (ι → H)) (ω : Ω) :
    L (fun i => G (τ i) ω) = comb G τ (fun i => (InnerProductSpace.toDual ℝ H).symm
      (L.comp (ContinuousLinearMap.single ℝ (fun _ : ι => H) i))) T ω := by
  have h1 : (fun i => G (τ i) ω) = ∑ i, Pi.single i (G (τ i) ω) := by
    rw [Finset.univ_sum_single]
  conv_lhs => rw [h1]
  rw [map_sum]
  unfold comb
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [min_eq_right (hτ i).2, real_inner_comm]
  simp only [InnerProductSpace.toDual_symm_apply]
  rfl

open HRS.Uniform.Q07c in
theorem map_dual_comb {Ω : Type*} {m : MeasurableSpace Ω} {ι : Type*} [Fintype ι] [DecidableEq ι] (μ : Measure Ω)
    (G : ℝ → Ω → H) (τ : ι → ℝ) {T : ℝ} (hτ : ∀ i, 0 ≤ τ i ∧ τ i ≤ T) (hGm : ∀ i, Measurable (G (τ i)))
    (L : StrongDual ℝ (ι → H)) :
    (μ.map fun ω i => G (τ i) ω).map L = μ.map (comb G τ (fun i => (InnerProductSpace.toDual ℝ H).symm
      (L.comp (ContinuousLinearMap.single ℝ (fun _ : ι => H) i))) T) := by
  have hYm : Measurable (fun ω i => G (τ i) ω) := measurable_pi_iff.2 hGm
  rw [Measure.map_map L.continuous.measurable hYm]
  congr 1
  funext ω
  exact comb_eq_dual G τ hτ L ω

open HRS.Uniform.Q07c in
/-- Two continuous Hilbert martingales with the same deterministic covariation density have the same
finite-dimensional laws. -/
theorem law_fdd_eq_G {Ω₁ Ω₂ : Type*} {m₁ : MeasurableSpace Ω₁} {m₂ : MeasurableSpace Ω₂}
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    {ℱ₁ : Filtration ℝ m₁} {ℱ₂ : Filtration ℝ m₂} {G₁ : ℝ → Ω₁ → H} {G₂ : ℝ → Ω₂ → H}
    {d : ℝ → H →L[ℝ] H →L[ℝ] ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hG₁ : IsHilbertMartingaleWithCovariation P₁ ℱ₁ T G₁ (fun r _ => d r))
    (hG₂ : IsHilbertMartingaleWithCovariation P₂ ℱ₂ T G₂ (fun r _ => d r))
    (hc₁ : ∀ ω, Continuous fun s => G₁ s ω) (hz₁ : ∀ ω, G₁ 0 ω = 0)
    (hc₂ : ∀ ω, Continuous fun s => G₂ s ω) (hz₂ : ∀ ω, G₂ 0 ω = 0)
    {ι : Type*} [Fintype ι] (τ : ι → ℝ) (hτ : ∀ i, 0 ≤ τ i ∧ τ i ≤ T) :
    P₁.map (fun ω i => G₁ (τ i) ω) = P₂.map (fun ω i => G₂ (τ i) ω) := by
  classical
  have hYm₁ : Measurable (fun ω i => G₁ (τ i) ω) :=
    measurable_pi_iff.2 fun i => measurable_of_isHM hG₁ (τ i)
  have hYm₂ : Measurable (fun ω i => G₂ (τ i) ω) :=
    measurable_pi_iff.2 fun i => measurable_of_isHM hG₂ (τ i)
  haveI : IsProbabilityMeasure (P₁.map (fun ω i => G₁ (τ i) ω)) :=
    ((Measure.isProbabilityMeasure_map_iff hYm₁.aemeasurable).2 inferInstance)
  haveI : IsProbabilityMeasure (P₂.map (fun ω i => G₂ (τ i) ω)) :=
    ((Measure.isProbabilityMeasure_map_iff hYm₂.aemeasurable).2 inferInstance)
  refine Measure.ext_of_charFunDual (funext fun L => ?_)
  rw [charFunDual_eq_charFun_map_one, charFunDual_eq_charFun_map_one]
  set y : ι → H := fun i => (InnerProductSpace.toDual ℝ H).symm
    (L.comp (ContinuousLinearMap.single ℝ (fun _ : ι => H) i)) with hy
  rw [map_dual_comb P₁ G₁ τ hτ (fun i => measurable_of_isHM hG₁ (τ i)) L,
    map_dual_comb P₂ G₂ τ hτ (fun i => measurable_of_isHM hG₂ (τ i)) L]
  have h1 := law_comb hG₁ hT hc₁ hz₁ τ hτ y (A := Set.univ) MeasurableSet.univ (by simp)
  have h2 := law_comb hG₂ hT hc₂ hz₂ τ hτ y (A := Set.univ) MeasurableSet.univ (by simp)
  rw [ProbabilityTheory.cond_univ] at h1 h2
  unfold law at h1 h2
  rw [h1, h2]

end FddG

end HRS.Uniform.Comp28
