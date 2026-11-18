import HRS.Main.GFSpec3
import HRS.Uniform.Q54cAux59

/-!
# GFB4, part 1: completing a filtration and replacing a martingale by an everywhere continuous version

`gf_law_identification` has a Hilbert martingale `G` that is only a.s. continuous with `G 0 = 0` a.s., whereas the Gaussian
machinery of `Q54c` (`law_comb`) needs everywhere continuous paths over all of `ℝ`.  We pass to the augmented filtration
`ℱ ⊔ nullSets` (the martingale property is unchanged) and to the version `G'_τ = G_{clamp τ}` modified on a null set.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.GF

/-- The augmentation `ℱ_t ⊔ nullSets P` of a filtration. -/
def gfb4_aug {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) (ℱ : Filtration ℝ mΩ) :
    Filtration ℝ mΩ where
  seq t := ℱ t ⊔ HRS.nullSets P
  mono' := fun s t h => sup_le_sup_right (ℱ.mono h) _
  le' t := sup_le (ℱ.le t) (HRS.nullSets_le P)

theorem gfb4_aug_le {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) (ℱ : Filtration ℝ mΩ) (t : ℝ) :
    ℱ t ≤ gfb4_aug P ℱ t := le_sup_left

theorem gfb4_nullSets_le_aug {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) (ℱ : Filtration ℝ mΩ)
    (t : ℝ) : HRS.nullSets P ≤ gfb4_aug P ℱ t := le_sup_right

set_option warn.classDefReducibility false in
/-- The σ-algebra of sets that are a.e. equal to a set of `ℱ t`. -/
def gfb4_aeSigma {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) (ℱ : Filtration ℝ mΩ) (t : ℝ) :
    MeasurableSpace Ω where
  MeasurableSet' := fun A => ∃ B, MeasurableSet[ℱ t] B ∧ A =ᵐ[P] B
  measurableSet_empty := ⟨∅, @MeasurableSet.empty Ω (ℱ t), Filter.EventuallyEq.refl _ _⟩
  measurableSet_compl := fun A ⟨B, hB, hAB⟩ => ⟨Bᶜ, @MeasurableSet.compl Ω B (ℱ t) hB, hAB.compl⟩
  measurableSet_iUnion := fun f hf => by
    choose B hB hfB using hf
    exact ⟨⋃ i, B i, @MeasurableSet.iUnion Ω ℕ (ℱ t) _ B hB, Filter.EventuallyEqSet.countable_iUnion hfB⟩

/-- Sets of the augmentation are a.e. equal to sets of the original σ-algebra. -/
theorem gfb4_aug_ae {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) (ℱ : Filtration ℝ mΩ) (t : ℝ)
    {A : Set Ω} (hA : MeasurableSet[gfb4_aug P ℱ t] A) : ∃ B, MeasurableSet[ℱ t] B ∧ A =ᵐ[P] B := by
  have h1 : ℱ t ≤ gfb4_aeSigma P ℱ t := fun A hA => ⟨A, hA, Filter.EventuallyEq.refl _ _⟩
  have h2 : HRS.nullSets P ≤ gfb4_aeSigma P ℱ t := by
    refine MeasurableSpace.generateFrom_le fun A hA => ⟨∅, @MeasurableSet.empty Ω (ℱ t), ?_⟩
    exact (ae_eq_empty.2 hA.2)
  have h3 : gfb4_aug P ℱ t ≤ gfb4_aeSigma P ℱ t := sup_le h1 h2
  exact h3 A hA

open Classical in
/-- Modifying a martingale on a null set and freezing it outside `[0,T]` gives a martingale for the augmented
filtration. -/
theorem gfb4_mart_mod {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ mΩ) {F : ℝ → Ω → ℝ} (hF : Martingale F ℱ P) {T : ℝ} (hT : 0 ≤ T) {N : Set Ω}
    (hNm : MeasurableSet N) (hN0 : P N = 0) (h0 : ∀ ω, ω ∉ N → F 0 ω = 0) (b : ℝ → ℝ) :
    Martingale (fun τ ω => if ω ∈ N then b τ else F (max 0 (min τ T)) ω) (gfb4_aug P ℱ) P := by
  set c : ℝ → ℝ := fun τ => max 0 (min τ T) with hc
  have hNaug : ∀ τ, MeasurableSet[gfb4_aug P ℱ τ] N := fun τ =>
    gfb4_nullSets_le_aug P ℱ τ _ (MeasurableSpace.measurableSet_generateFrom ⟨hNm, hN0⟩)
  have hae : ∀ τ, (fun ω => if ω ∈ N then b τ else F (c τ) ω) =ᵐ[P] F (c τ) := by
    intro τ
    have : ∀ᵐ ω ∂P, ω ∉ N := by
      rw [ae_iff]; simpa using hN0
    filter_upwards [this] with ω hω
    simp [hω]
  have hmeas : ∀ τ, Measurable[gfb4_aug P ℱ τ] (fun ω => if ω ∈ N then b τ else F (c τ) ω) := by
    intro τ
    by_cases hτ : τ ≤ 0
    · have hcτ : c τ = 0 := by
        simp only [hc]
        rw [max_eq_left]
        exact min_le_of_left_le hτ
      have : (fun ω => if ω ∈ N then b τ else F (c τ) ω) = fun ω => if ω ∈ N then b τ else 0 := by
        funext ω
        by_cases hω : ω ∈ N
        · simp [hω]
        · simp [hω, hcτ, h0 ω hω]
      rw [this]
      exact Measurable.ite (hNaug τ) measurable_const measurable_const
    · push Not at hτ
      have hcτ : c τ ≤ τ := by
        simp only [hc]
        exact max_le hτ.le (min_le_left _ _)
      have h1 : Measurable[ℱ (c τ)] (F (c τ)) := (hF.1 (c τ)).measurable
      have h2 : Measurable[gfb4_aug P ℱ τ] (F (c τ)) :=
        h1.mono ((ℱ.mono hcτ).trans (gfb4_aug_le P ℱ τ)) le_rfl
      exact Measurable.ite (hNaug τ) measurable_const h2
  refine ⟨fun τ => (hmeas τ).stronglyMeasurable, fun s τ hsτ => ?_⟩
  have hint : ∀ τ, Integrable (fun ω => if ω ∈ N then b τ else F (c τ) ω) P := fun τ =>
    (hF.integrable (c τ)).congr (hae τ).symm
  have hle : gfb4_aug P ℱ s ≤ mΩ := (gfb4_aug P ℱ).le s
  haveI : IsFiniteMeasure (P.trim hle) := isFiniteMeasure_trim hle
  symm
  refine ae_eq_condExp_of_forall_setIntegral_eq hle (hint τ) (fun A hA _ => (hint s).integrableOn)
    (fun A hA _ => ?_) (hmeas s).stronglyMeasurable.aestronglyMeasurable
  obtain ⟨B, hB, hAB⟩ := gfb4_aug_ae P ℱ s hA
  rw [setIntegral_congr_set hAB, setIntegral_congr_set hAB,
    integral_congr_ae (ae_restrict_of_ae (hae s)), integral_congr_ae (ae_restrict_of_ae (hae τ))]
  have hBs : MeasurableSet B := ℱ.le s _ hB
  by_cases hsT : T ≤ s
  · have e1 : c s = T := by
      simp only [hc]
      rw [min_eq_right hsT, max_eq_right hT]
    have e2 : c τ = T := by
      simp only [hc]
      rw [min_eq_right (hsT.trans hsτ), max_eq_right hT]
    rw [e1, e2]
  · push Not at hsT
    by_cases hs0 : 0 ≤ s
    · have e1 : c s = s := by
        simp only [hc]
        rw [min_eq_left hsT.le, max_eq_right hs0]
      have e2 : s ≤ c τ := by
        simp only [hc]
        exact le_max_of_le_right (le_min hsτ hsT.le)
      rw [e1]
      exact hF.setIntegral_eq e2 hB
    · push Not at hs0
      have e1 : c s = 0 := by
        simp only [hc]
        rw [max_eq_left]
        exact min_le_of_left_le hs0.le
      have e2 : 0 ≤ c τ := le_max_left _ _
      have hB0 : MeasurableSet[ℱ 0] B := ℱ.mono hs0.le _ hB
      rw [e1]
      exact hF.setIntegral_eq e2 hB0


variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

theorem gfb4_integral_Icc_clamp (Cd : ℝ → H →L[ℝ] H →L[ℝ] ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hCd : ∀ σ, σ ∉ Set.Icc 0 T → Cd σ = 0) (x y : H) (τ : ℝ) :
    ∫ σ in Set.Icc 0 τ, Cd σ x y = ∫ σ in Set.Icc 0 (max 0 (min τ T)), Cd σ x y := by
  by_cases hτ : τ ≤ 0
  · have hc : max 0 (min τ T) = 0 := by
      rw [max_eq_left]; exact min_le_of_left_le hτ
    rw [hc]
    rcases hτ.lt_or_eq with h | h
    · rw [Set.Icc_eq_empty (by linarith)]
      simp
    · rw [h]
  · push Not at hτ
    by_cases hτT : T ≤ τ
    · have hc : max 0 (min τ T) = T := by
        rw [min_eq_right hτT, max_eq_right hT]
      rw [hc]
      refine (setIntegral_eq_of_subset_of_ae_sdiff_eq_zero (f := fun σ => Cd σ x y)
        measurableSet_Icc.nullMeasurableSet (Set.Icc_subset_Icc le_rfl hτT) ?_)
      refine Filter.Eventually.of_forall fun σ hσ => ?_
      have : σ ∉ Set.Icc 0 T := fun h => hσ.2 h
      simp [hCd σ this]
    · push Not at hτT
      have hc : max 0 (min τ T) = τ := by
        rw [min_eq_left hτT.le, max_eq_right hτ.le]
      rw [hc]

open Classical in
/-- Replacement of a Hilbert martingale with a.s. continuous paths by one with everywhere continuous paths over `ℝ`,
for the augmented filtration. -/
theorem gfb4_modify {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ mΩ) {T : ℝ} (hT : 0 ≤ T) (G : ℝ → Ω → H) (Cd : ℝ → H →L[ℝ] H →L[ℝ] ℝ)
    (hCd : ∀ σ, σ ∉ Set.Icc 0 T → Cd σ = 0)
    (hG : IsHilbertMartingaleWithCovariation P ℱ T G (fun r _ => Cd r)) :
    ∃ G' : ℝ → Ω → H, IsHilbertMartingaleWithCovariation P (gfb4_aug P ℱ) T G' (fun r _ => Cd r) ∧
      (∀ ω, Continuous fun s => G' s ω) ∧ (∀ ω, G' 0 ω = 0) ∧
      ∀ τ ∈ Set.Icc (0 : ℝ) T, G' τ =ᵐ[P] G τ := by
  obtain ⟨N, hsub, hNm, hN0⟩ := exists_measurable_superset_of_null
    (show P {ω | ¬ (ContinuousOn (fun τ => G τ ω) (Set.Icc 0 T) ∧ G 0 ω = 0)} = 0 from by
      rw [← ae_iff]
      filter_upwards [hG.cont, hG.zero] with ω h1 h2 using ⟨h1, h2⟩)
  have hgood : ∀ ω, ω ∉ N → ContinuousOn (fun τ => G τ ω) (Set.Icc 0 T) ∧ G 0 ω = 0 := by
    intro ω hω
    by_contra h
    exact hω (hsub h)
  set c : ℝ → ℝ := fun τ => max 0 (min τ T) with hc
  have hcmem : ∀ τ, c τ ∈ Set.Icc 0 T := fun τ => ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩
  have hcc : Continuous c := continuous_const.max (continuous_id.min continuous_const)
  have hNae : ∀ᵐ ω ∂P, ω ∉ N := by rw [ae_iff]; simpa using hN0
  have hc0 : c 0 = 0 := by simp [hc, hT]
  have hcτ : ∀ τ ∈ Set.Icc (0 : ℝ) T, c τ = τ := fun τ hτ => by
    simp only [hc]; rw [min_eq_left hτ.2, max_eq_right hτ.1]
  refine ⟨fun τ ω => if ω ∈ N then 0 else G (c τ) ω, ?_, ?_, ?_, ?_⟩
  · -- the martingale structure
    refine
      { martingale := ?_, zero := ?_, cont := ?_, sq_int := ?_, sigma_meas := hG.sigma_meas,
        sigma_adapted := fun σ x y => (hG.sigma_adapted σ x y).mono (gfb4_aug_le P ℱ σ) le_rfl,
        sigma_traceClass := hG.sigma_traceClass, sigma_int := hG.sigma_int,
        sigma_pathint := hG.sigma_pathint, sigma_entry_int := hG.sigma_entry_int, covariation := ?_ }
    · intro x
      have := gfb4_mart_mod P ℱ (hG.martingale x) hT hNm hN0
        (fun ω hω => by simp [(hgood ω hω).2]) (fun _ => 0)
      have e : (fun (τ : ℝ) (ω : Ω) => inner ℝ (if ω ∈ N then (0 : H) else G (c τ) ω) x) =
          (fun τ ω => if ω ∈ N then (fun _ : ℝ => (0 : ℝ)) τ else inner ℝ (G (max 0 (min τ T)) ω) x) := by
        funext τ ω
        by_cases hω : ω ∈ N <;> simp [hω, hc]
      rw [e]
      exact this
    · refine Filter.Eventually.of_forall fun ω => ?_
      by_cases hω : ω ∈ N
      · simp [hω]
      · simp [hω, hc0, (hgood ω hω).2]
    · refine Filter.Eventually.of_forall fun ω => ?_
      refine Continuous.continuousOn ?_
      by_cases hω : ω ∈ N
      · simp only [hω, ite_true]; exact continuous_const
      · simp only [hω, ite_false]
        exact (hgood ω hω).1.comp_continuous hcc hcmem
    · intro τ hτ
      refine (hG.sq_int (c τ) (hcmem τ)).ae_eq ?_
      filter_upwards [hNae] with ω hω
      simp [hω, hcτ τ hτ]
    · intro x y
      have h0 : ∀ ω, ω ∉ N → (inner ℝ (G 0 ω) x * inner ℝ (G 0 ω) y -
          ∫ σ in Set.Icc 0 (0 : ℝ), Cd σ x y) = 0 := by
        intro ω hω
        simp [(hgood ω hω).2]
      have := gfb4_mart_mod P ℱ (hG.covariation x y) hT hNm hN0 h0
        (fun τ => -∫ σ in Set.Icc 0 τ, Cd σ x y)
      have e : (fun (τ : ℝ) (ω : Ω) => inner ℝ (if ω ∈ N then (0 : H) else G (c τ) ω) x *
          inner ℝ (if ω ∈ N then (0 : H) else G (c τ) ω) y - ∫ σ in Set.Icc 0 τ, Cd σ x y) =
          (fun τ ω => if ω ∈ N then (fun τ => -∫ σ in Set.Icc 0 τ, Cd σ x y) τ else
            (inner ℝ (G (max 0 (min τ T)) ω) x * inner ℝ (G (max 0 (min τ T)) ω) y -
              ∫ σ in Set.Icc 0 (max 0 (min τ T)), Cd σ x y)) := by
        funext τ ω
        by_cases hω : ω ∈ N
        · simp [hω]
        · simp only [hω, ite_false, hc]
          rw [gfb4_integral_Icc_clamp Cd hT hCd x y τ]
      rw [e]
      exact this
  · intro ω
    by_cases hω : ω ∈ N
    · simp only [hω, ite_true]; exact continuous_const
    · simp only [hω, ite_false]
      exact (hgood ω hω).1.comp_continuous hcc hcmem
  · intro ω
    by_cases hω : ω ∈ N
    · simp [hω]
    · simp [hω, hc0, (hgood ω hω).2]
  · intro τ hτ
    filter_upwards [hNae] with ω hω
    simp [hω, hcτ τ hτ]

end HRS.GF
