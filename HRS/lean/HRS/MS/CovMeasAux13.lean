import HRS.MS.CovMeasAux12

/-!
# S10.1 (worker S101B), part 13: measurability of the basic pairings

`s101_D_W_aem`: for all `s, s' ∈ [0,T]` and `α, β` the function `τ ↦ D_τ(W_{s,α}, W_{s',β})` is a.e.-measurable on `[0,T]`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.CovMeas

open HRS HRS.Whole HRS.MS.Go HRS.MS.FixEq

variable {d : ℕ} {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {Pw : ℝ} {z : ℝ → (Euc d → ℝ) → ℝ}

lemma s101_D_symm (A : S101Adm C m T r Pw z) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) T)
    (u v : KSpace d m T) : s101D C m T z τ u v = s101D C m T z τ v u := by
  obtain ⟨K0, -, hK⟩ := s101_D_data A.hd A.hP A.horb
  exact (hK z A.hz τ hτ).2.1 u v

theorem s101_D_W_aem_le (A : S101Adm C m T r Pw z) (hT : 0 ≤ T) {s s' : ℝ} (hs : s ∈ Icc (0 : ℝ) T)
    (hs' : s' ∈ Icc (0 : ℝ) T) (hss : s ≤ s') (α β : MultiIndex d) :
    AEMeasurable (fun τ => s101D C m T z τ (s101W m T s α) (s101W m T s' β))
      (volume.restrict (Icc 0 T)) := by
  set P1 : Set ℝ := Icc 0 T ∩ Iio s with hP1
  set P2 : Set ℝ := Icc 0 T ∩ (Ico s s') with hP2
  set P3 : Set ℝ := Icc 0 T ∩ Ici s' with hP3
  have hunion : Icc (0 : ℝ) T = P1 ∪ P2 ∪ P3 := by
    ext τ
    simp only [hP1, hP2, hP3, mem_union, mem_inter_iff, mem_Icc, mem_Iio, mem_Ico, mem_Ici]
    constructor
    · intro h
      by_cases h1 : τ < s
      · exact Or.inl (Or.inl ⟨h, h1⟩)
      · by_cases h2 : τ < s'
        · exact Or.inl (Or.inr ⟨h, not_lt.1 h1, h2⟩)
        · exact Or.inr ⟨h, not_lt.1 h2⟩
    · rintro ((h | h) | h) <;> exact h.1
  have hP1m : MeasurableSet P1 := measurableSet_Icc.inter measurableSet_Iio
  have hP2m : MeasurableSet P2 := measurableSet_Icc.inter measurableSet_Ico
  have hP3m : MeasurableSet P3 := measurableSet_Icc.inter measurableSet_Ici
  rw [hunion, aemeasurable_union_iff, aemeasurable_union_iff]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- τ < s ≤ s'
    refine s101_aem_lt A hs hs' α β hP1m fun τ hτ => ?_
    exact ⟨⟨hτ.1, hτ.2⟩, lt_of_lt_of_le hτ.2 hss⟩
  · -- s ≤ τ < s'
    have hD := s101_aem_diag (d := d) (m := m) hT (ν := volume) hP2m (fun τ hτ => hτ.1)
      (s101D C m T z) (fun t => s101W m T t α) (fun _ => s101W m T s' β)
      (fun τ => s101W m T τ α) (fun _ => s101W m T s' β)
      (fun t ht => by
        refine s101_aem_lt A ht hs' α β (hP2m.inter measurableSet_Iio) fun τ hτ => ?_
        exact ⟨⟨hτ.1.1, hτ.2⟩, hτ.1.2.2⟩)
      (fun τ hτ hτT => ⟨s101_W_tendsto α hτ.1.1 hτT, tendsto_const_nhds⟩)
    refine hD.congr ?_
    refine (ae_restrict_iff' hP2m).2 (Eventually.of_forall fun τ hτ => ?_)
    exact (s101_D_W_left A hτ.1 hs hs' hτ.2.1 α β).symm
  · -- s' ≤ τ
    have hD := s101_aem_diag (d := d) (m := m) hT (ν := volume) hP3m (fun τ hτ => hτ.1)
      (s101D C m T z) (fun t => s101W m T t α) (fun t => s101W m T t β)
      (fun τ => s101W m T τ α) (fun τ => s101W m T τ β)
      (fun t ht => by
        refine s101_aem_lt A ht ht α β (hP3m.inter measurableSet_Iio) fun τ hτ => ?_
        exact ⟨⟨hτ.1.1, hτ.2⟩, hτ.2⟩)
      (fun τ hτ hτT => ⟨s101_W_tendsto α hτ.1.1 hτT, s101_W_tendsto β hτ.1.1 hτT⟩)
    refine hD.congr ?_
    refine (ae_restrict_iff' hP3m).2 (Eventually.of_forall fun τ hτ => ?_)
    have hsτ : s ≤ τ := hss.trans hτ.2
    show s101D C m T z τ (s101W m T τ α) (s101W m T τ β) =
      s101D C m T z τ (s101W m T s α) (s101W m T s' β)
    rw [s101_D_W_left A hτ.1 hs hs' hsτ α β, s101_D_W_right A hτ.1 hτ.1 hs' hτ.2 α β]

theorem s101_D_W_aem (A : S101Adm C m T r Pw z) (hT : 0 ≤ T) {s s' : ℝ} (hs : s ∈ Icc (0 : ℝ) T)
    (hs' : s' ∈ Icc (0 : ℝ) T) (α β : MultiIndex d) :
    AEMeasurable (fun τ => s101D C m T z τ (s101W m T s α) (s101W m T s' β))
      (volume.restrict (Icc 0 T)) := by
  rcases le_total s s' with h | h
  · exact s101_D_W_aem_le A hT hs hs' h α β
  · have := s101_D_W_aem_le A hT hs' hs h β α
    refine this.congr ?_
    refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun τ hτ => ?_)
    exact s101_D_symm A hτ _ _

end HRS.MS.CovMeas
