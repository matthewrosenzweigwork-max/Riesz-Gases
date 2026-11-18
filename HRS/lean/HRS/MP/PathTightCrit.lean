import HRS.Whole.AppendixALemmas

/-!
# S.A.21 `path_tightness_criterion`: proof

Proof of `HRS.Whole.AppendixALemmas.path_tightness_criterion` (S L10697-10730).  The compact
set is `K = {z : ∀ l, (modulus ≤ 1/(l+1) at scale δ_l) ∧ (∀ t ∈ F_l, z t ∈ K_{l,t})}`; compactness by
Arzelà-Ascoli.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS.MP.PathTight

open HRS.Whole.AppendixALemmas

section Compactness

variable {E : Type*} [NormedAddCommGroup E] (T : ℝ)

/-- The candidate compact set. -/
def ptc_K (δ : ℕ → ℝ) (F : ℕ → Finset (Set.Icc (0 : ℝ) T)) (Kt : ℕ → Set.Icc (0 : ℝ) T → Set E) :
    Set C(Set.Icc (0 : ℝ) T, E) :=
  {z | ∀ l : ℕ, (∀ s t : Set.Icc (0 : ℝ) T, |(t : ℝ) - s| ≤ δ l →
      dist (z t) (z s) ≤ 1 / ((l : ℝ) + 1)) ∧ ∀ t ∈ F l, z t ∈ Kt l t}

theorem ptc_K_isClosed (δ : ℕ → ℝ) (F : ℕ → Finset (Set.Icc (0 : ℝ) T))
    (Kt : ℕ → Set.Icc (0 : ℝ) T → Set E) (hKt : ∀ l t, IsClosed (Kt l t)) :
    IsClosed (ptc_K T δ F Kt) := by
  have hev : ∀ x : Set.Icc (0 : ℝ) T, Continuous fun z : C(Set.Icc (0 : ℝ) T, E) => z x :=
    fun x => continuous_eval_const x
  simp only [ptc_K, Set.ofPred_forall, Set.ofPred_and]
  refine isClosed_iInter fun l => IsClosed.inter (isClosed_iInter fun s => isClosed_iInter fun t => ?_)
    (isClosed_iInter fun t => isClosed_iInter fun ht => ?_)
  · by_cases hp : |(t : ℝ) - s| ≤ δ l
    · have := isClosed_le ((hev t).dist (hev s)) (continuous_const (y := 1 / ((l : ℝ) + 1)))
      simpa [hp] using this
    · simp [hp]
  · exact (hKt l t).preimage (hev t)

theorem ptc_K_isCompact [CompleteSpace E] (δ : ℕ → ℝ) (hδ : ∀ l, 0 < δ l)
    (F : ℕ → Finset (Set.Icc (0 : ℝ) T))
    (hcov : ∀ l, ∀ t : Set.Icc (0 : ℝ) T, ∃ t' ∈ F l, |(t : ℝ) - t'| ≤ δ l)
    (Kt : ℕ → Set.Icc (0 : ℝ) T → Set E) (hKt : ∀ l t, IsCompact (Kt l t)) :
    IsCompact (ptc_K T δ F Kt) := by
  set K := ptc_K T δ F Kt with hK
  have hclosed : IsClosed K := ptc_K_isClosed T δ F Kt fun l t => (hKt l t).isClosed
  -- range set
  set S : Set E := {y | ∃ z ∈ K, ∃ t : Set.Icc (0 : ℝ) T, y = z t} with hS
  have hSbdd : TotallyBounded S := by
    rw [Metric.totallyBounded_iff]
    intro ε hε
    obtain ⟨l, hl⟩ := exists_nat_one_div_lt (half_pos hε)
    have hQ : IsCompact (⋃ t ∈ F l, Kt l t) := (F l).isCompact_biUnion fun t _ => hKt l t
    obtain ⟨c, hcQ, hcfin, hcov'⟩ := hQ.finite_cover_balls (half_pos hε)
    refine ⟨c, hcfin, ?_⟩
    rintro y ⟨z, hz, t, rfl⟩
    obtain ⟨t', ht', hdt⟩ := hcov l t
    have h1 : dist (z t) (z t') ≤ 1 / ((l : ℝ) + 1) := (hz l).1 t' t hdt
    have h2 : z t' ∈ ⋃ t ∈ F l, Kt l t := Set.mem_biUnion ht' ((hz l).2 t' ht')
    obtain ⟨y', hy', hy'b⟩ := Set.mem_iUnion₂.1 (hcov' h2)
    refine Set.mem_iUnion₂.2 ⟨y', hy', ?_⟩
    rw [Metric.mem_ball] at hy'b ⊢
    calc dist (z t) y' ≤ dist (z t) (z t') + dist (z t') y' := dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt (h1.trans hl.le) hy'b
      _ = ε := add_halves ε
  have hScpt : IsCompact (closure S) :=
    (isCompact_iff_totallyBounded_isComplete.2 ⟨hSbdd.closure, isClosed_closure.isComplete⟩)
  -- Arzelà-Ascoli through `C(I,E) ≃ I →ᵇ E`
  let e := ContinuousMap.equivBoundedOfCompact (Set.Icc (0 : ℝ) T) E
  have he : Topology.IsEmbedding e :=
    (ContinuousMap.isUniformEmbedding_equivBoundedOfCompact (Set.Icc (0 : ℝ) T) E).isEmbedding
  have hecl : Topology.IsClosedEmbedding e :=
    ⟨he, by simp [Set.range_eq_univ.2 e.surjective]⟩
  have hA : IsCompact (closure (e '' K)) := by
    refine BoundedContinuousFunction.arzela_ascoli (closure S) hScpt _ ?_ ?_
    · rintro f x ⟨z, hz, rfl⟩
      exact subset_closure ⟨z, hz, x, rfl⟩
    · intro x0
      rw [Metric.equicontinuousAt_iff]
      intro ε hε
      obtain ⟨l, hl⟩ := exists_nat_one_div_lt hε
      refine ⟨δ l, hδ l, fun x hx f => ?_⟩
      obtain ⟨f, z, hz, rfl⟩ := f
      have hx' : |(x : ℝ) - x0| ≤ δ l := by
        rw [← Real.dist_eq]; exact hx.le
      have := (hz l).1 x0 x hx'
      rw [dist_comm]
      exact lt_of_le_of_lt this hl
  rw [he.isCompact_iff]
  rw [(hecl.isClosedMap K hclosed).closure_eq] at hA
  exact hA

end Compactness

/-- Finite `δ`-nets in `[0,T]` made of points of a dense subset `D`. -/
theorem ptc_cover (T : ℝ) (D : Set ℝ) (hDT : D ⊆ Set.Icc (0 : ℝ) T)
    (hD : Set.Icc (0 : ℝ) T ⊆ closure D) (δ : ℝ) (hδ : 0 < δ) :
    ∃ F : Finset (Set.Icc (0 : ℝ) T), (∀ t ∈ F, (t : ℝ) ∈ D) ∧
      ∀ t : Set.Icc (0 : ℝ) T, ∃ t' ∈ F, |(t : ℝ) - t'| ≤ δ := by
  classical
  obtain ⟨F0, hF0⟩ := (isCompact_univ (X := Set.Icc (0 : ℝ) T)).elim_finite_subcover
    (ι := {d : Set.Icc (0 : ℝ) T // (d : ℝ) ∈ D})
    (fun d => Metric.ball (d : Set.Icc (0 : ℝ) T) δ) (fun _ => Metric.isOpen_ball) (by
      intro x _
      obtain ⟨b, hb, hxb⟩ := Metric.mem_closure_iff.1 (hD x.2) δ hδ
      refine Set.mem_iUnion.2 ⟨⟨⟨b, hDT hb⟩, hb⟩, ?_⟩
      rw [Metric.mem_ball]
      simpa [Subtype.dist_eq] using hxb)
  refine ⟨F0.image Subtype.val, ?_, ?_⟩
  · intro t ht
    obtain ⟨d, _, rfl⟩ := Finset.mem_image.1 ht
    exact d.2
  · intro t
    obtain ⟨d, hd, hdt⟩ := Set.mem_iUnion₂.1 (hF0 (Set.mem_univ t))
    refine ⟨d.1, Finset.mem_image.2 ⟨d, hd, rfl⟩, ?_⟩
    rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq] at hdt
    exact hdt.le


/-- Lemma S.A.21, statement copied verbatim from `HRS.Whole.AppendixALemmas.path_tightness_criterion`. -/
theorem path_tightness_criterion_proof {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [TopologicalSpace.SeparableSpace E] [MeasurableSpace E] [BorelSpace E]
    (T : ℝ) (hT : 0 < T) {Ω : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)] (P : ∀ N, Measure (Ω N))
    [∀ N, IsProbabilityMeasure (P N)] (Z : ∀ N, ℝ → Ω N → E)
    (hZmeas : ∀ N : ℕ, 1 ≤ N → ∀ t, Measurable (Z N t))
    (hcont : ∀ N : ℕ, 1 ≤ N → ∀ᵐ ζ ∂(P N), Continuous fun t : Set.Icc (0 : ℝ) T => Z N t ζ)
    (hpath : ∀ N : ℕ, 1 ≤ N → Measurable fun ζ => contPathOf T (fun t => Z N t ζ))
    (D : Set ℝ) (hDT : D ⊆ Set.Icc (0 : ℝ) T) (hD : Set.Icc (0 : ℝ) T ⊆ closure D)
    (htight : ∀ t ∈ D, IsTightMeasureSet {μ | ∃ N : ℕ, 1 ≤ N ∧ μ = (P N).map (Z N t)})
    (hmod : ∀ ε : ℝ, 0 < ε → Tendsto (fun δ : ℝ =>
      ⨆ N : ℕ, ⨆ (_ : 1 ≤ N), P N {ζ | ENNReal.ofReal ε < omegaE (fun t => Z N t ζ) T δ})
      (𝓝[>] 0) (𝓝 0)) :
    IsTightMeasureSet {μ | ∃ N : ℕ, 1 ≤ N ∧
      μ = (P N).map (fun ζ => contPathOf T (fun t => Z N t ζ))} := by
  classical
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨ε', hε'pos, hsum⟩ := ENNReal.exists_pos_sum_of_countable
    (ENNReal.half_pos hε.ne').ne' ℕ
  have hε'ne : ∀ l, (ε' l : ℝ≥0∞) ≠ 0 := fun l => by exact_mod_cast (hε'pos l).ne'
  -- step 1: scales `δ l`
  have hδ : ∀ l : ℕ, ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, 1 ≤ N →
      P N {ζ | ENNReal.ofReal (1 / ((l : ℝ) + 1)) < omegaE (fun t => Z N t ζ) T δ} ≤ ε' l := by
    intro l
    have h := hmod (1 / ((l : ℝ) + 1)) (by positivity)
    have hlt := h.eventually (Iio_mem_nhds (pos_iff_ne_zero.2 (hε'ne l)))
    obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hlt
    have hu' : (0 : ℝ) < u := hu
    refine ⟨u / 2, half_pos hu', fun N hN => ?_⟩
    have h2 := hsub ⟨half_pos hu', half_lt_self hu'⟩
    exact (le_iSup₂ (f := fun (N : ℕ) (_ : 1 ≤ N) =>
      P N {ζ | ENNReal.ofReal (1 / ((l : ℝ) + 1)) < omegaE (fun t => Z N t ζ) T (u / 2)})
      N hN).trans (le_of_lt h2)
  choose δ hδpos hδbd using hδ
  -- step 2: nets
  have hF : ∀ l : ℕ, ∃ F : Finset (Set.Icc (0 : ℝ) T), (∀ t ∈ F, (t : ℝ) ∈ D) ∧
      ∀ t : Set.Icc (0 : ℝ) T, ∃ t' ∈ F, |(t : ℝ) - t'| ≤ δ l :=
    fun l => ptc_cover T D hDT hD (δ l) (hδpos l)
  choose F hFD hFcov using hF
  -- step 3: compacts in `E`
  have hKt : ∀ (l : ℕ) (t : Set.Icc (0 : ℝ) T), ∃ K : Set E, IsCompact K ∧
      ((t : ℝ) ∈ D → ∀ N : ℕ, 1 ≤ N →
        P N {ζ | Z N t ζ ∉ K} ≤ (ε' l : ℝ≥0∞) / ((F l).card : ℝ≥0∞)) := by
    intro l t
    by_cases ht : (t : ℝ) ∈ D
    · obtain ⟨K, hK, hKb⟩ := (isTightMeasureSet_iff_exists_isCompact_measure_compl_le.1
        (htight t ht)) ((ε' l : ℝ≥0∞) / ((F l).card : ℝ≥0∞))
        (ENNReal.div_pos (hε'ne l) (ENNReal.natCast_ne_top _))
      refine ⟨K, hK, fun _ N hN => ?_⟩
      have h := hKb _ ⟨N, hN, rfl⟩
      rwa [Measure.map_apply (hZmeas N hN t) hK.isClosed.measurableSet.compl] at h
    · exact ⟨∅, isCompact_empty, fun h => absurd h ht⟩
  choose Kt hKtc hKtb using hKt
  refine ⟨ptc_K T δ F Kt, ptc_K_isCompact T δ hδpos F hFcov Kt hKtc, ?_⟩
  rintro μ ⟨N, hN, rfl⟩
  have hKcl : IsClosed (ptc_K T δ F Kt) := ptc_K_isClosed T δ F Kt fun l t => (hKtc l t).isClosed
  rw [Measure.map_apply (hpath N hN) hKcl.measurableSet.compl]
  -- step 6: union bound
  have hsub : (fun ζ => contPathOf T (fun t => Z N t ζ)) ⁻¹' (ptc_K T δ F Kt)ᶜ ⊆
      {ζ | ¬ Continuous fun t : Set.Icc (0 : ℝ) T => Z N t ζ} ∪
        ⋃ l : ℕ, ({ζ | ENNReal.ofReal (1 / ((l : ℝ) + 1)) < omegaE (fun t => Z N t ζ) T (δ l)} ∪
          ⋃ t ∈ F l, {ζ | Z N t ζ ∉ Kt l t}) := by
    intro ζ hζ
    by_contra hnot
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_ofPred_eq, not_or, not_exists, not_lt,
      not_not] at hnot
    obtain ⟨hc, hl⟩ := hnot
    apply hζ
    have hpe : ∀ t : Set.Icc (0 : ℝ) T, contPathOf T (fun t => Z N t ζ) t = Z N t ζ := by
      intro t
      simp [contPathOf, hc]
    intro l
    simp only [hpe]
    refine ⟨fun s t hst => ?_, fun t ht => hl l |>.2 t ht⟩
    have hle : ‖Z N t ζ - Z N s ζ‖ₑ ≤ omegaE (fun t => Z N t ζ) T (δ l) :=
      le_iSup₂_of_le (s : ℝ) s.2 (le_iSup₂_of_le (t : ℝ) t.2 (le_iSup_of_le hst le_rfl))
    have h1 := hle.trans (hl l).1
    have hr : (0 : ℝ) ≤ 1 / ((l : ℝ) + 1) := by positivity
    rw [← ofReal_norm] at h1
    rw [dist_eq_norm]
    exact (ENNReal.ofReal_le_ofReal_iff hr).1 h1
  have hnull : P N {ζ | ¬ Continuous fun t : Set.Icc (0 : ℝ) T => Z N t ζ} = 0 :=
    ae_iff.1 (hcont N hN)
  have hcard : ∀ l : ℕ, ∑ t ∈ F l, (ε' l : ℝ≥0∞) / ((F l).card : ℝ≥0∞) ≤ ε' l := by
    intro l
    rw [Finset.sum_const, nsmul_eq_mul]
    exact ENNReal.mul_div_le
  calc P N ((fun ζ => contPathOf T (fun t => Z N t ζ)) ⁻¹' (ptc_K T δ F Kt)ᶜ)
      ≤ P N ({ζ | ¬ Continuous fun t : Set.Icc (0 : ℝ) T => Z N t ζ} ∪
        ⋃ l : ℕ, ({ζ | ENNReal.ofReal (1 / ((l : ℝ) + 1)) < omegaE (fun t => Z N t ζ) T (δ l)} ∪
          ⋃ t ∈ F l, {ζ | Z N t ζ ∉ Kt l t})) := measure_mono hsub
    _ ≤ 0 + ∑' l : ℕ, ((ε' l : ℝ≥0∞) + ε' l) := by
        refine (measure_union_le _ _).trans (add_le_add hnull.le ?_)
        refine (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun l => ?_)
        refine (measure_union_le _ _).trans (add_le_add (hδbd l N hN) ?_)
        refine (measure_biUnion_finset_le _ _).trans ?_
        refine (Finset.sum_le_sum fun t ht => hKtb l t (hFD l t ht) N hN).trans (hcard l)
    _ = ∑' l : ℕ, (ε' l : ℝ≥0∞) + ∑' l : ℕ, (ε' l : ℝ≥0∞) := by
        rw [zero_add, ENNReal.tsum_add]
    _ ≤ ε / 2 + ε / 2 := add_le_add hsum.le hsum.le
    _ = ε := ENNReal.add_halves ε

end HRS.MP.PathTight

example := (@HRS.MP.PathTight.path_tightness_criterion_proof : type_of% @HRS.Whole.AppendixALemmas.path_tightness_criterion)
