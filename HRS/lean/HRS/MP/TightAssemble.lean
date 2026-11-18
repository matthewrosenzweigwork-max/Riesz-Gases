import HRS.MP.PathTightCrit

/-!
# MPTASM: tightness of an a.s. continuous process that is a sum of two controlled versions and a small remainder
-/

open MeasureTheory Filter Topology
open HRS.Whole.AppendixALemmas
open scoped ENNReal

namespace HRS.MP.TightAsm

section Pointwise

variable {E : Type*} [NormedAddCommGroup E]

theorem mta_le_omegaE (z : ℝ → E) (T δ : ℝ) {s t : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) T)
    (ht : t ∈ Set.Icc (0 : ℝ) T) (hst : |t - s| ≤ δ) : ‖z t - z s‖ₑ ≤ omegaE z T δ := by
  unfold omegaE
  exact le_iSup₂_of_le s hs (le_iSup₂_of_le t ht (le_iSup_of_le hst le_rfl))

theorem mta_omegaE_mono (z : ℝ → E) (T : ℝ) {δ δ' : ℝ} (h : δ ≤ δ') :
    omegaE z T δ ≤ omegaE z T δ' := by
  unfold omegaE
  refine iSup₂_le fun s hs => iSup₂_le fun t ht => iSup_le fun hst => ?_
  exact mta_le_omegaE z T δ' hs ht (hst.trans h)

theorem mta_le_sup (r : ℝ → E) (T : ℝ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ‖r t‖ₑ ≤ ⨆ t ∈ Set.Icc (0 : ℝ) T, ‖r t‖ₑ :=
  le_iSup₂_of_le t ht le_rfl

theorem mta_omegaE_sum (z i m : ℝ → E) (T δ : ℝ) :
    omegaE z T δ ≤ omegaE i T δ + omegaE m T δ +
      2 * ⨆ t ∈ Set.Icc (0 : ℝ) T, ‖z t - i t - m t‖ₑ := by
  unfold omegaE
  refine iSup₂_le fun s hs => iSup₂_le fun t ht => iSup_le fun hst => ?_
  set R := ⨆ t ∈ Set.Icc (0 : ℝ) T, ‖z t - i t - m t‖ₑ with hR
  have h1 := mta_le_omegaE i T δ hs ht hst
  have h2 := mta_le_omegaE m T δ hs ht hst
  have h3 := mta_le_sup (fun t => z t - i t - m t) T ht
  have h4 := mta_le_sup (fun t => z t - i t - m t) T hs
  have e : z t - z s = (i t - i s) + (m t - m s) + ((z t - i t - m t) - (z s - i s - m s)) := by abel
  calc ‖z t - z s‖ₑ = ‖(i t - i s) + (m t - m s) + ((z t - i t - m t) - (z s - i s - m s))‖ₑ := by rw [e]
    _ ≤ ‖i t - i s‖ₑ + ‖m t - m s‖ₑ + (‖z t - i t - m t‖ₑ + ‖z s - i s - m s‖ₑ) := by
        refine (enorm_add_le _ _).trans (add_le_add (enorm_add_le _ _) enorm_sub_le)
    _ ≤ _ := by
        rw [two_mul]
        have h3' : ‖z t - i t - m t‖ₑ ≤ R := h3
        have h4' : ‖z s - i s - m s‖ₑ ≤ R := h4
        exact add_le_add (add_le_add h1 h2) (add_le_add h3' h4')

theorem mta_event_split {ε : ℝ} (_hε : 0 < ε) (z i m : ℝ → E) (T δ : ℝ)
    (h : ENNReal.ofReal ε < omegaE z T δ) :
    ENNReal.ofReal (ε / 4) < omegaE i T δ ∨ ENNReal.ofReal (ε / 4) < omegaE m T δ ∨
      ENNReal.ofReal (ε / 4) < ⨆ t ∈ Set.Icc (0 : ℝ) T, ‖z t - i t - m t‖ₑ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2, h3⟩ := hcon
  have h4 := mta_omegaE_sum z i m T δ
  have : omegaE z T δ ≤ ENNReal.ofReal ε := by
    refine h4.trans ?_
    calc _ ≤ ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) + 2 * ENNReal.ofReal (ε / 4) :=
          add_le_add (add_le_add h1 h2) (mul_le_mul_right h3 _)
      _ = 4 * ENNReal.ofReal (ε / 4) := by ring
      _ = ENNReal.ofReal ε := by
          have : (4 : ℝ≥0∞) = ENNReal.ofReal 4 := by simp
          rw [this, ← ENNReal.ofReal_mul (by norm_num)]
          congr 1; ring
  exact absurd h (not_lt.2 this)

theorem mta_omegaE_small (z : ℝ → E) (T : ℝ) (hz : Continuous fun t : Set.Icc (0 : ℝ) T => z t)
    {ε : ℝ} (hε : 0 < ε) : ∃ δ > 0, omegaE z T δ < ENNReal.ofReal ε := by
  have huc : UniformContinuous fun t : Set.Icc (0 : ℝ) T => z t :=
    CompactSpace.uniformContinuous_of_continuous hz
  obtain ⟨δ, hδ, hd⟩ := Metric.uniformContinuous_iff.1 huc (ε / 2) (half_pos hε)
  refine ⟨δ / 2, half_pos hδ, ?_⟩
  have : omegaE z T (δ / 2) ≤ ENNReal.ofReal (ε / 2) := by
    unfold omegaE
    refine iSup₂_le fun s hs => iSup₂_le fun t ht => iSup_le fun hst => ?_
    have := hd (a := ⟨t, ht⟩) (b := ⟨s, hs⟩) (by
      rw [Subtype.dist_eq, Real.dist_eq]; linarith [half_lt_self hδ])
    rw [dist_eq_norm] at this
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal this.le
  exact this.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hε).2 (half_lt_self hε))

end Pointwise

section Prob

variable {E : Type*} [NormedAddCommGroup E]

/-- The modulus of continuity of an element of `C([0,T], E)`. -/
noncomputable def mta_omegaC (T δ : ℝ) (z : C(Set.Icc (0 : ℝ) T, E)) : ℝ≥0∞ :=
  ⨆ (s : Set.Icc (0 : ℝ) T) (t : Set.Icc (0 : ℝ) T) (_ : |(t : ℝ) - s| ≤ δ), ‖z t - z s‖ₑ

theorem mta_omegaC_lsc (T δ : ℝ) : LowerSemicontinuous (mta_omegaC (E := E) T δ) := by
  unfold mta_omegaC
  refine lowerSemicontinuous_iSup fun s => lowerSemicontinuous_iSup fun t =>
    lowerSemicontinuous_iSup fun _ => Continuous.lowerSemicontinuous ?_
  exact continuous_enorm.comp ((continuous_eval_const t).sub
    (continuous_eval_const s))

theorem mta_contPathOf_apply (T : ℝ) (z : ℝ → E) (hz : Continuous fun t : Set.Icc (0 : ℝ) T => z t)
    (t : Set.Icc (0 : ℝ) T) : (contPathOf T z) t = z t := by
  unfold contPathOf
  rw [dif_pos hz]
  rfl

theorem mta_omegaE_eq (T δ : ℝ) (z : ℝ → E) (hz : Continuous fun t : Set.Icc (0 : ℝ) T => z t) :
    omegaE z T δ = mta_omegaC T δ (contPathOf T z) := by
  have hc : ∀ t : Set.Icc (0 : ℝ) T, (contPathOf T z) t = z t := mta_contPathOf_apply T z hz
  unfold omegaE mta_omegaC
  simp only [hc]
  rw [iSup_subtype']
  refine iSup_congr fun s => ?_
  rw [iSup_subtype']

theorem mta_omegaE_measurable [MeasurableSpace E] [BorelSpace E] {Ω : Type*} [MeasurableSpace Ω]
    (T δ : ℝ) (Y : ℝ → Ω → E) (hcont : ∀ ζ, Continuous fun t : Set.Icc (0 : ℝ) T => Y t ζ)
    (hpath : Measurable fun ζ => contPathOf T (fun t => Y t ζ)) :
    Measurable fun ζ => omegaE (fun t => Y t ζ) T δ := by
  have : (fun ζ => omegaE (fun t => Y t ζ) T δ) =
      mta_omegaC T δ ∘ fun ζ => contPathOf T (fun t => Y t ζ) := by
    funext ζ
    exact mta_omegaE_eq T δ _ (hcont ζ)
  rw [this]
  exact (mta_omegaC_lsc T δ).measurable.comp hpath

/-- For a fixed `N`, the modulus event of a path with everywhere continuous paths shrinks. -/
theorem mta_fixed_N [MeasurableSpace E] [BorelSpace E] {Ω : Type*} [MeasurableSpace Ω]
    (T : ℝ) (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℝ → Ω → E)
    (hcont : ∀ ζ, Continuous fun t : Set.Icc (0 : ℝ) T => Y t ζ)
    (hpath : Measurable fun ζ => contPathOf T (fun t => Y t ζ)) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun δ : ℝ => P {ζ | ENNReal.ofReal ε < omegaE (fun t => Y t ζ) T δ})
      (𝓝[>] 0) (𝓝 0) := by
  set A : ℕ → Set Ω := fun k => {ζ | ENNReal.ofReal ε < omegaE (fun t => Y t ζ) T (1 / ((k : ℝ) + 1))}
    with hA
  have hAm : ∀ k, MeasurableSet (A k) := fun k =>
    measurableSet_lt measurable_const (mta_omegaE_measurable T _ Y hcont hpath)
  have hanti : Antitone A := by
    intro k l hkl ζ hζ
    refine lt_of_lt_of_le hζ (mta_omegaE_mono _ T ?_)
    have : (k : ℝ) ≤ l := by exact_mod_cast hkl
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hinter : (⋂ k, A k) = ∅ := by
    ext ζ
    simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false]
    intro h
    obtain ⟨δ, hδ, hlt⟩ := mta_omegaE_small (fun t => Y t ζ) T (hcont ζ) hε
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hδ
    have := h k
    simp only [hA, Set.mem_ofPred_eq] at this
    exact absurd (lt_of_lt_of_le this ((mta_omegaE_mono _ T hk.le).trans hlt.le)) (lt_irrefl _)
  have hlim := tendsto_measure_iInter_atTop (μ := P) (fun k => (hAm k).nullMeasurableSet) hanti
    ⟨0, measure_ne_top _ _⟩
  rw [hinter, measure_empty] at hlim
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  obtain ⟨k, hk⟩ := (ENNReal.tendsto_nhds_zero.1 hlim η hη).exists
  have hmem : Set.Ioo (0 : ℝ) (1 / ((k : ℝ) + 1)) ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by positivity)
  filter_upwards [hmem] with δ hδ
  refine le_trans (measure_mono ?_) hk
  intro ζ hζ
  exact lt_of_lt_of_le hζ (mta_omegaE_mono _ T hδ.2.le)

/-- Markov-type event bound with non-measurable `I`, `M`. -/
theorem mta_event_bound {Ω : Type*} [MeasurableSpace Ω] (T : ℝ) (P : Measure Ω)
    (Y I M : ℝ → Ω → E) {ε : ℝ} (hε : 0 < ε) (δ : ℝ) (c : ℝ≥0∞)
    (hmeas : MeasurableSet {ζ | ENNReal.ofReal ε < omegaE (fun t => Y t ζ) T δ})
    (hR : ∫⁻ ζ, ⨆ t ∈ Set.Icc (0 : ℝ) T, ‖Y t ζ - I t ζ - M t ζ‖ₑ ∂P ≤ c) :
    P {ζ | ENNReal.ofReal ε < omegaE (fun t => Y t ζ) T δ} ≤
      P {ζ | ENNReal.ofReal (ε / 4) < omegaE (fun t => I t ζ) T δ} +
      P {ζ | ENNReal.ofReal (ε / 4) < omegaE (fun t => M t ζ) T δ} +
      c / ENNReal.ofReal (ε / 4) := by
  set A := {ζ | ENNReal.ofReal ε < omegaE (fun t => Y t ζ) T δ} with hA
  set AI := {ζ | ENNReal.ofReal (ε / 4) < omegaE (fun t => I t ζ) T δ} with hAI
  set AM := {ζ | ENNReal.ofReal (ε / 4) < omegaE (fun t => M t ζ) T δ} with hAM
  set a : ℝ≥0∞ := ENNReal.ofReal (ε / 4) with ha
  have ha0 : a ≠ 0 := by
    rw [ha]; exact (ENNReal.ofReal_pos.2 (by positivity)).ne'
  obtain ⟨U, hUsub, hUm, hUeq⟩ := exists_measurable_superset P (AI ∪ AM)
  set B := A \ U with hB
  have hBm : MeasurableSet B := hmeas.diff hUm
  have hBsub : ∀ ζ ∈ B, a < ⨆ t ∈ Set.Icc (0 : ℝ) T, ‖Y t ζ - I t ζ - M t ζ‖ₑ := by
    intro ζ hζ
    have hζA : ζ ∈ A := hζ.1
    have hζU : ζ ∉ U := hζ.2
    rcases mta_event_split hε (fun t => Y t ζ) (fun t => I t ζ) (fun t => M t ζ) T δ hζA with h | h | h
    · exact absurd (hUsub (Or.inl h)) hζU
    · exact absurd (hUsub (Or.inr h)) hζU
    · exact h
  have hmarkov : a * P B ≤ c := by
    refine le_trans ?_ hR
    calc a * P B = ∫⁻ ζ, B.indicator (fun _ => a) ζ ∂P := (lintegral_indicator_const hBm a).symm
      _ ≤ _ := by
        refine lintegral_mono fun ζ => ?_
        by_cases hζ : ζ ∈ B
        · simp only [Set.indicator_of_mem hζ]
          exact (hBsub ζ hζ).le
        · simp [Set.indicator_of_notMem hζ]
  have hBle : P B ≤ c / a := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl ha0) (Or.inl (by rw [ha]; exact ENNReal.ofReal_ne_top))]
    rwa [mul_comm]
  have hAsub : A ⊆ U ∪ B := by
    intro ζ hζ
    by_cases hU : ζ ∈ U
    · exact Or.inl hU
    · exact Or.inr ⟨hζ, hU⟩
  calc P A ≤ P (U ∪ B) := measure_mono hAsub
    _ ≤ P U + P B := measure_union_le _ _
    _ ≤ (P AI + P AM) + c / a := by
        rw [hUeq]
        exact add_le_add (measure_union_le _ _) hBle
    _ = _ := rfl

end Prob

theorem mta_tight {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E] [MeasurableSpace E] [BorelSpace E]
    (T : ℝ) (hT : 0 < T) {Ω : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)] (P : ∀ N, Measure (Ω N))
    [∀ N, IsProbabilityMeasure (P N)] (Z I M : ∀ N, ℝ → Ω N → E)
    (hZmeas : ∀ N : ℕ, 1 ≤ N → ∀ t, Measurable (Z N t))
    (hZcont : ∀ N : ℕ, 1 ≤ N → ∀ᵐ ζ ∂(P N), Continuous fun t : Set.Icc (0 : ℝ) T => Z N t ζ)
    (hZpath : ∀ N : ℕ, 1 ≤ N → AEMeasurable (fun ζ => contPathOf T (fun t => Z N t ζ)) (P N))
    (hI : ∀ ε : ℝ, 0 < ε → Tendsto (fun δ : ℝ =>
      ⨆ N : ℕ, ⨆ (_ : 1 ≤ N), P N {ζ | ENNReal.ofReal ε < omegaE (fun t => I N t ζ) T δ})
      (𝓝[>] 0) (𝓝 0))
    (hM : ∀ ε : ℝ, 0 < ε → Tendsto (fun δ : ℝ =>
      ⨆ N : ℕ, ⨆ (_ : 1 ≤ N), P N {ζ | ENNReal.ofReal ε < omegaE (fun t => M N t ζ) T δ})
      (𝓝[>] 0) (𝓝 0))
    (c : ℕ → ℝ) (hc : Tendsto c atTop (𝓝 0))
    (hR : ∀ N : ℕ, 1 ≤ N → ∫⁻ ζ, ⨆ t ∈ Set.Icc (0 : ℝ) T,
      ‖Z N t ζ - I N t ζ - M N t ζ‖ₑ ∂(P N) ≤ ENNReal.ofReal (c N))
    (hfix : ∀ t ∈ Set.Icc (0 : ℝ) T,
      IsTightMeasureSet {μ | ∃ N : ℕ, 1 ≤ N ∧ μ = (P N).map (Z N t)}) :
    IsTightMeasureSet {μ | ∃ N : ℕ, 1 ≤ N ∧
      μ = (P N).map (fun ζ => contPathOf T (fun t => Z N t ζ))} := by
  classical
  have hNn : ∀ N : ℕ, ∃ s : Set (Ω N), MeasurableSet s ∧ P N s = 0 ∧
      ∀ ζ, ζ ∉ s → 1 ≤ N → Continuous fun t : Set.Icc (0 : ℝ) T => Z N t ζ := by
    intro N
    by_cases hN : 1 ≤ N
    · obtain ⟨s, hsub, hm, h0⟩ := exists_measurable_superset_of_null (ae_iff.1 (hZcont N hN))
      refine ⟨s, hm, h0, fun ζ hζ _ => ?_⟩
      by_contra hcn
      exact hζ (hsub hcn)
    · exact ⟨∅, MeasurableSet.empty, measure_empty, fun _ _ h => absurd h hN⟩
  choose Nn hNm hN0 hNc using hNn
  let Zh : ∀ N, ℝ → Ω N → E := fun N t ζ => if ζ ∈ Nn N then 0 else Z N t ζ
  have hae : ∀ N, ∀ᵐ ζ ∂(P N), ζ ∉ Nn N := fun N => measure_eq_zero_iff_ae_notMem.1 (hN0 N)
  have hZh_eq : ∀ N ζ, ζ ∉ Nn N → ∀ t, Zh N t ζ = Z N t ζ := by
    intro N ζ hζ t
    simp only [Zh, hζ, ite_false]
  have hZh_meas : ∀ N : ℕ, 1 ≤ N → ∀ t, Measurable (Zh N t) := fun N hN t =>
    Measurable.ite (hNm N) measurable_const (hZmeas N hN t)
  have hZh_cont : ∀ N : ℕ, 1 ≤ N → ∀ ζ, Continuous fun t : Set.Icc (0 : ℝ) T => Zh N t ζ := by
    intro N hN ζ
    by_cases hζ : ζ ∈ Nn N
    · simp only [Zh, hζ, ite_true]
      exact continuous_const
    · have : (fun t : Set.Icc (0 : ℝ) T => Zh N t ζ) = fun t : Set.Icc (0 : ℝ) T => Z N t ζ :=
        funext fun t => hZh_eq N ζ hζ t
      rw [this]
      exact hNc N ζ hζ hN
  have hZh_path : ∀ N : ℕ, 1 ≤ N → Measurable fun ζ => contPathOf T (fun t => Zh N t ζ) := by
    intro N hN
    refine ContinuousMap.measurable_iff_eval.2 fun s => ?_
    have : (fun ζ => (contPathOf T (fun t => Zh N t ζ)) s) = fun ζ => Zh N s ζ :=
      funext fun ζ => mta_contPathOf_apply T _ (hZh_cont N hN ζ) s
    rw [this]
    exact hZh_meas N hN s
  have hmapt : ∀ N t, (P N).map (Zh N t) = (P N).map (Z N t) := by
    intro N t
    refine Measure.map_congr ?_
    filter_upwards [hae N] with ζ hζ using hZh_eq N ζ hζ t
  have hmapp : ∀ N, (P N).map (fun ζ => contPathOf T (fun t => Zh N t ζ)) =
      (P N).map (fun ζ => contPathOf T (fun t => Z N t ζ)) := by
    intro N
    refine Measure.map_congr ?_
    filter_upwards [hae N] with ζ hζ
    have : (fun t => Zh N t ζ) = fun t => Z N t ζ := funext fun t => hZh_eq N ζ hζ t
    simp only [this]
  have hRh : ∀ N : ℕ, 1 ≤ N → ∫⁻ ζ, ⨆ t ∈ Set.Icc (0 : ℝ) T,
      ‖Zh N t ζ - I N t ζ - M N t ζ‖ₑ ∂(P N) ≤ ENNReal.ofReal (c N) := by
    intro N hN
    refine le_trans (le_of_eq ?_) (hR N hN)
    refine lintegral_congr_ae ?_
    filter_upwards [hae N] with ζ hζ
    simp only [hZh_eq N ζ hζ]
  -- modulus hypothesis
  have hmod : ∀ ε : ℝ, 0 < ε → Tendsto (fun δ : ℝ =>
      ⨆ N : ℕ, ⨆ (_ : 1 ≤ N), P N {ζ | ENNReal.ofReal ε < omegaE (fun t => Zh N t ζ) T δ})
      (𝓝[>] 0) (𝓝 0) := by
    intro ε hε
    rw [ENNReal.tendsto_nhds_zero]
    intro η hη
    by_cases hηt : η = ⊤
    · exact Eventually.of_forall fun δ => by rw [hηt]; exact le_top
    set ν : ℝ≥0∞ := η / 3 with hν
    have hν0 : 0 < ν := ENNReal.div_pos hη.ne' (by norm_num)
    have hsum : ν + ν + ν = η := ENNReal.add_thirds η
    have hνη : ν ≤ η := by
      rw [← hsum]
      exact le_self_add.trans le_self_add
    have ha : ENNReal.ofReal (ε / 4) ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
    have hcN : Tendsto (fun N : ℕ => ENNReal.ofReal (c N) / ENNReal.ofReal (ε / 4)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun N : ℕ => ENNReal.ofReal (c N)) atTop (𝓝 0) := by
        have := (ENNReal.continuous_ofReal.tendsto 0).comp hc
        simpa [Function.comp_def] using this
      have := ENNReal.Tendsto.div_const h1 (Or.inr ha)
      simpa using this
    obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (ENNReal.tendsto_nhds_zero.1 hcN ν hν0)
    have h2 := ENNReal.tendsto_nhds_zero.1 (hI (ε / 4) (by positivity)) ν hν0
    have h3 := ENNReal.tendsto_nhds_zero.1 (hM (ε / 4) (by positivity)) ν hν0
    have h4 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ N ∈ Finset.range N₀, 1 ≤ N →
        P N {ζ | ENNReal.ofReal ε < omegaE (fun t => Zh N t ζ) T δ} ≤ ν := by
      refine (Filter.eventually_all_finset _).2 fun N _ => ?_
      by_cases hN : 1 ≤ N
      · exact (ENNReal.tendsto_nhds_zero.1 (mta_fixed_N T (P N) (Zh N) (hZh_cont N hN)
          (hZh_path N hN) hε) ν hν0).mono fun δ h _ => h
      · exact Eventually.of_forall fun δ h => absurd h hN
    filter_upwards [h2, h3, h4] with δ hIδ hMδ hFδ
    refine iSup₂_le fun N hN => ?_
    by_cases hNN : N < N₀
    · exact (hFδ N (Finset.mem_range.2 hNN) hN).trans hνη
    · have hNN' : N₀ ≤ N := not_lt.1 hNN
      have hmeas : MeasurableSet {ζ | ENNReal.ofReal ε < omegaE (fun t => Zh N t ζ) T δ} :=
        measurableSet_lt measurable_const
          (mta_omegaE_measurable T δ (Zh N) (hZh_cont N hN) (hZh_path N hN))
      have hb := mta_event_bound T (P N) (Zh N) (I N) (M N) hε δ (ENNReal.ofReal (c N)) hmeas
        (hRh N hN)
      refine hb.trans ?_
      rw [← hsum]
      refine add_le_add (add_le_add ?_ ?_) (hN₀ N hNN')
      · exact (le_iSup₂ (f := fun (N : ℕ) (_ : 1 ≤ N) =>
          P N {ζ | ENNReal.ofReal (ε / 4) < omegaE (fun t => I N t ζ) T δ}) N hN).trans hIδ
      · exact (le_iSup₂ (f := fun (N : ℕ) (_ : 1 ≤ N) =>
          P N {ζ | ENNReal.ofReal (ε / 4) < omegaE (fun t => M N t ζ) T δ}) N hN).trans hMδ
  have htight : ∀ t ∈ Set.Icc (0 : ℝ) T,
      IsTightMeasureSet {μ | ∃ N : ℕ, 1 ≤ N ∧ μ = (P N).map (Zh N t)} := by
    intro t ht
    have : {μ | ∃ N : ℕ, 1 ≤ N ∧ μ = (P N).map (Zh N t)} =
        {μ | ∃ N : ℕ, 1 ≤ N ∧ μ = (P N).map (Z N t)} := by
      ext μ
      simp only [Set.mem_ofPred_eq, hmapt]
    rw [this]
    exact hfix t ht
  have key := HRS.MP.PathTight.path_tightness_criterion_proof T hT P Zh hZh_meas
    (fun N hN => ae_of_all _ (hZh_cont N hN)) hZh_path (Set.Icc (0 : ℝ) T) subset_rfl
    subset_closure htight hmod
  have : {μ | ∃ N : ℕ, 1 ≤ N ∧ μ = (P N).map (fun ζ => contPathOf T (fun t => Zh N t ζ))} =
      {μ | ∃ N : ℕ, 1 ≤ N ∧ μ = (P N).map (fun ζ => contPathOf T (fun t => Z N t ζ))} := by
    ext μ
    simp only [Set.mem_ofPred_eq, hmapp]
  rw [this] at key
  exact key

end HRS.MP.TightAsm
