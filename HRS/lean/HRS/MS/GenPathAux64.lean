import HRS.MS.GenPathAux63

/-!
# S5.6 packet P10d: a.e. measurability of the initial functional from the independence of the Gaussian part

If `f` and `g` are independent in the sense of `ProbabilityTheory.IndepFun` (outer-measure form, no measurability assumed)
and `f + g` is measurable, then `g` is a.e. measurable.  (The outer measure of preimages of separated Borel sets is
additive, because they are separated by the measurable level sets of `f + g`; hence `P*(g ∈ U) + P*(g ∉ U) = 1` for
open `U`.)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.GenPath

open HRS HRS.Whole

variable {d : ℕ}

theorem s56_sep_additive {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f g : Ω → ℝ) (hind : IndepFun f g P) (hY : Measurable fun ω => f ω + g ω) (δ : ℝ) (hδ : 0 < δ)
    (B B' : Set ℝ) (hB : MeasurableSet B) (hB' : MeasurableSet B')
    (hsep : ∀ x ∈ B, ∀ y ∈ B', δ ≤ |x - y|) :
    P (g ⁻¹' (B ∪ B')) = P (g ⁻¹' B) + P (g ⁻¹' B') := by
  have hδ3 : 0 < δ / 3 := by positivity
  -- an interval of length `δ/3` on which `f` has positive outer measure
  obtain ⟨k, hk⟩ : ∃ k : ℤ, P (f ⁻¹' Set.Ioc (k * (δ / 3)) ((k + 1) * (δ / 3))) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hcover : (Set.univ : Set Ω) ⊆ ⋃ k : ℤ, f ⁻¹' Set.Ioc (k * (δ / 3)) ((k + 1) * (δ / 3)) := by
      intro ω _
      simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_Ioc]
      refine ⟨⌈f ω / (δ / 3)⌉ - 1, ?_, ?_⟩
      · have h1 := Int.ceil_lt_add_one (f ω / (δ / 3))
        have h2 : ((⌈f ω / (δ / 3)⌉ : ℤ) : ℝ) - 1 < f ω / (δ / 3) := by linarith
        push_cast
        calc ((⌈f ω / (δ / 3)⌉ : ℝ) - 1) * (δ / 3) < (f ω / (δ / 3)) * (δ / 3) :=
              mul_lt_mul_of_pos_right h2 hδ3
          _ = f ω := by field_simp
      · have h1 := Int.le_ceil (f ω / (δ / 3))
        push_cast
        calc f ω = (f ω / (δ / 3)) * (δ / 3) := by field_simp
          _ ≤ ((⌈f ω / (δ / 3)⌉ : ℝ) - 1 + 1) * (δ / 3) := mul_le_mul_of_nonneg_right (by linarith) hδ3.le
    have h0 : P (⋃ k : ℤ, f ⁻¹' Set.Ioc (k * (δ / 3)) ((k + 1) * (δ / 3))) = 0 :=
      measure_iUnion_null fun k => by simpa using hcon k
    have := measure_mono_null hcover h0
    simp at this
  set A : Set ℝ := Set.Ioc (k * (δ / 3)) ((k + 1) * (δ / 3)) with hA
  have hAm : MeasurableSet A := measurableSet_Ioc
  have hAdiam : ∀ a ∈ A, ∀ a' ∈ A, |a - a'| ≤ δ / 3 := by
    intro a ha a' ha'
    rw [abs_le]
    constructor <;> nlinarith [ha.1, ha.2, ha'.1, ha'.2]
  set C : Set ℝ := ⋃ b ∈ B, ⋃ a ∈ A, Metric.ball (a + b) (δ / 3) with hC
  have hCo : IsOpen C := isOpen_biUnion fun b _ => isOpen_biUnion fun a _ => Metric.isOpen_ball
  set M : Set Ω := (fun ω => f ω + g ω) ⁻¹' C with hM
  have hMm : MeasurableSet M := hY hCo.measurableSet
  set E : Set Ω := f ⁻¹' A with hE
  have h1 : E ∩ g ⁻¹' B ⊆ M := by
    rintro ω ⟨hω1, hω2⟩
    simp only [hM, hC, Set.mem_preimage, Set.mem_iUnion]
    exact ⟨g ω, hω2, f ω, hω1, Metric.mem_ball_self hδ3⟩
  have h2 : (E ∩ g ⁻¹' B') ∩ M = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun ω ⟨⟨hω1, hω2⟩, hω3⟩ => ?_
    simp only [hM, hC, Set.mem_preimage, Set.mem_iUnion] at hω3
    obtain ⟨b, hb, a, ha, hmem⟩ := hω3
    have hsep' := hsep b hb (g ω) hω2
    rw [Metric.mem_ball, Real.dist_eq] at hmem
    have h3 := hAdiam a ha (f ω) hω1
    have : |b - g ω| < δ := by
      have e : b - g ω = (a + b - (f ω + g ω)) + (f ω - a) := by ring
      rw [e]
      calc |(a + b - (f ω + g ω)) + (f ω - a)| ≤ |a + b - (f ω + g ω)| + |f ω - a| := abs_add_le _ _
        _ < δ / 3 + δ / 3 := by
            have : |f ω - a| ≤ δ / 3 := by rw [abs_sub_comm]; exact h3
            rw [abs_sub_comm (a + b)] at *
            linarith
        _ < δ := by linarith
    linarith
  have hS : P (E ∩ g ⁻¹' (B ∪ B')) = P (E ∩ g ⁻¹' B) + P (E ∩ g ⁻¹' B') := by
    have := measure_inter_add_sdiff (μ := P) (E ∩ g ⁻¹' (B ∪ B')) hMm
    have e1 : (E ∩ g ⁻¹' (B ∪ B')) ∩ M = E ∩ g ⁻¹' B := by
      ext ω
      constructor
      · rintro ⟨⟨hω1, hω2 | hω2⟩, hω3⟩
        · exact ⟨hω1, hω2⟩
        · exact absurd (h2.subset ⟨⟨hω1, hω2⟩, hω3⟩) (Set.notMem_empty _)
      · intro hω
        exact ⟨⟨hω.1, Or.inl hω.2⟩, h1 hω⟩
    have e2 : (E ∩ g ⁻¹' (B ∪ B')) \ M = E ∩ g ⁻¹' B' := by
      ext ω
      constructor
      · rintro ⟨⟨hω1, hω2 | hω2⟩, hω3⟩
        · exact absurd (h1 ⟨hω1, hω2⟩) hω3
        · exact ⟨hω1, hω2⟩
      · intro hω
        refine ⟨⟨hω.1, Or.inr hω.2⟩, fun hm => ?_⟩
        exact (Set.eq_empty_iff_forall_notMem.1 h2) ω ⟨hω, hm⟩
    rw [e1, e2] at this
    exact this.symm
  have hind1 := fun X (hX : MeasurableSet X) => hind.measure_inter_preimage_eq_mul A X hAm hX
  have hPE : P E ≠ ⊤ := measure_ne_top _ _
  have hPE0 : P E ≠ 0 := hk
  have key : P E * P (g ⁻¹' (B ∪ B')) = P E * (P (g ⁻¹' B) + P (g ⁻¹' B')) := by
    rw [mul_add, ← hind1 B hB, ← hind1 B' hB', ← hind1 (B ∪ B') (hB.union hB')]
    exact hS
  exact (ENNReal.mul_right_inj hPE0 hPE).1 key

theorem s56_nullMeasurable_of_outer_sum {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (s : Set Ω) (h : P s + P sᶜ = 1) : NullMeasurableSet s P := by
  set h1 : Set Ω := toMeasurable P s with hh1
  set h2 : Set Ω := toMeasurable P sᶜ with hh2
  have e1 : P h1 = P s := measure_toMeasurable s
  have e2 : P h2 = P sᶜ := measure_toMeasurable sᶜ
  have hcover : (Set.univ : Set Ω) ⊆ h1 ∪ h2 := fun ω _ => by
    by_cases hω : ω ∈ s
    · exact Or.inl (subset_toMeasurable P s hω)
    · exact Or.inr (subset_toMeasurable P sᶜ hω)
  have hu : P (h1 ∪ h2) = 1 := le_antisymm prob_le_one (by simpa using measure_mono (μ := P) hcover)
  have hi := measure_union_add_inter (μ := P) h1 (measurableSet_toMeasurable P sᶜ)
  rw [hu, e1, e2, h] at hi
  have hi0 : P (h1 ∩ h2) = 0 := by
    have : (1 : ℝ≥0∞) + P (h1 ∩ h2) = 1 + 0 := by rw [add_zero]; exact hi
    exact (ENNReal.add_right_inj ENNReal.one_ne_top).1 this
  have hsub : h1 \ s ⊆ h1 ∩ h2 := fun ω ⟨hω1, hω2⟩ => ⟨hω1, subset_toMeasurable P sᶜ hω2⟩
  have hae : h1 =ᵐ[P] s := by
    rw [ae_eq_set]
    refine ⟨measure_mono_null hsub hi0, ?_⟩
    have : s \ h1 = ∅ := Set.diff_eq_empty.2 (subset_toMeasurable P s)
    rw [this]; exact measure_empty
  exact (measurableSet_toMeasurable P s).nullMeasurableSet.congr hae

theorem s56_aem_of_indep_sum {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f g : Ω → ℝ) (hind : IndepFun f g P) (hY : Measurable fun ω => f ω + g ω) : AEMeasurable g P := by
  have hopen : ∀ U : Set ℝ, IsOpen U → NullMeasurableSet (g ⁻¹' U) P := by
    intro U hU
    set Uk : ℕ → Set ℝ := fun k => {x | ∀ y ∈ Uᶜ, 1 / ((k : ℝ) + 1) ≤ |x - y|} with hUk
    have hUkc : ∀ k, IsClosed (Uk k) := fun k => by
      have : Uk k = ⋂ y ∈ Uᶜ, {x | 1 / ((k : ℝ) + 1) ≤ |x - y|} := by
        ext x; simp [hUk]
      rw [this]
      exact isClosed_biInter fun y _ =>
        isClosed_le continuous_const (continuous_abs.comp (continuous_id.sub continuous_const))
    have hUkmono : Monotone Uk := fun k k' hkk' x hx y hy => by
      refine le_trans ?_ (hx y hy)
      have : (k : ℝ) + 1 ≤ k' + 1 := by exact_mod_cast Nat.succ_le_succ hkk'
      exact one_div_le_one_div_of_le (by positivity) this
    have hUkU : (⋃ k, Uk k) = U := by
      ext x
      simp only [Set.mem_iUnion]
      constructor
      · rintro ⟨k, hk⟩
        by_contra hx
        have := hk x hx
        simp at this
        have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
        linarith
      · intro hx
        obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU x hx
        obtain ⟨k, hk⟩ := exists_nat_one_div_lt hr
        refine ⟨k, fun y hy => ?_⟩
        have : ¬ dist y x < r := fun h => hy (hball h)
        rw [not_lt, Real.dist_eq] at this
        rw [abs_sub_comm]
        exact (hk.le.trans this)
    have hadd : ∀ k, P (g ⁻¹' (Uk k ∪ Uᶜ)) = P (g ⁻¹' Uk k) + P (g ⁻¹' Uᶜ) := fun k =>
      s56_sep_additive P f g hind hY (1 / ((k : ℝ) + 1)) (by positivity) _ _ (hUkc k).measurableSet
        hU.isClosed_compl.measurableSet (fun x hx y hy => hx y hy)
    have hsup : P (g ⁻¹' U) = ⨆ k, P (g ⁻¹' Uk k) := by
      rw [← hUkU, Set.preimage_iUnion]
      exact Monotone.measure_iUnion (μ := P) (s := fun k => g ⁻¹' Uk k)
        (fun k k' hkk' => Set.preimage_mono (hUkmono hkk'))
    have hle : P (g ⁻¹' U) + P (g ⁻¹' Uᶜ) ≤ 1 := by
      rw [hsup, ENNReal.iSup_add]
      refine iSup_le fun k => ?_
      rw [← hadd k]
      exact prob_le_one
    have hge : 1 ≤ P (g ⁻¹' U) + P (g ⁻¹' Uᶜ) := by
      calc (1 : ℝ≥0∞) = P Set.univ := measure_univ.symm
        _ ≤ P (g ⁻¹' U ∪ g ⁻¹' Uᶜ) := measure_mono (fun ω _ => by
            by_cases h : g ω ∈ U
            · exact Or.inl h
            · exact Or.inr h)
        _ ≤ _ := measure_union_le _ _
    exact s56_nullMeasurable_of_outer_sum P _ (by
      rw [← Set.preimage_compl]
      exact le_antisymm hle hge)
  have hnm : NullMeasurable g P := measurable_of_isOpen fun U hU => hopen U hU
  exact hnm.aemeasurable

end HRS.MS.GenPath
