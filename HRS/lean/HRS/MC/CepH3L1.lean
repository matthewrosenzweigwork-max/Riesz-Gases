import HRS.MC.CepH3K2

/-!
# Packet CEPH3, part L1: abstract assembly of part (b) (Lindelof, finite maxima, Fatou)
-/


open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal
namespace HRS.MC.CepH3
noncomputable section

/-- Lindelöf: a pointwise supremum of continuous functions of one real variable is a supremum along
a sequence. -/
lemma h3l_lindelof {ι : Type*} [Nonempty ι] (a : ι → ℝ → ℝ≥0∞) (hac : ∀ i, Continuous (a i)) :
    ∃ s : ℕ → ι, ∀ r, ⨆ i, a i r ≤ ⨆ k, a (s k) r := by
  have hex : ∀ q : ℚ, ∃ T : Set ι, T.Countable ∧
      ⋃ i ∈ T, {r : ℝ | (Real.toNNReal q : ℝ≥0∞) < a i r} = ⋃ i, {r : ℝ | (Real.toNNReal q : ℝ≥0∞) < a i r} := by
    intro q
    exact TopologicalSpace.isOpen_iUnion_countable _ fun i => isOpen_lt continuous_const (hac i)
  choose T hTc hTeq using hex
  set T' : Set ι := (⋃ q, T q) ∪ {Classical.arbitrary ι} with hT'
  have hT'c : T'.Countable := ((Set.countable_iUnion hTc)).union (Set.countable_singleton _)
  have hT'n : T'.Nonempty := ⟨Classical.arbitrary ι, Or.inr rfl⟩
  obtain ⟨s, hs⟩ := hT'c.exists_eq_range hT'n
  refine ⟨s, fun r => ?_⟩
  refine iSup_le fun i => ?_
  by_contra hlt
  push_neg at hlt
  obtain ⟨q, -, hq1, hq2⟩ := ENNReal.lt_iff_exists_rat_btwn.mp hlt
  have hr : r ∈ ⋃ i, {r : ℝ | (Real.toNNReal q : ℝ≥0∞) < a i r} := mem_iUnion.mpr ⟨i, hq2⟩
  rw [← hTeq q] at hr
  obtain ⟨j, hjT, hj⟩ := by simpa using hr
  have hjT' : j ∈ T' := Or.inl (mem_iUnion.mpr ⟨q, hjT⟩)
  rw [hs] at hjT'
  obtain ⟨k, rfl⟩ := hjT'
  have : a (s k) r ≤ ⨆ k, a (s k) r := le_iSup (fun k => a (s k) r) k
  exact absurd (lt_of_lt_of_le hj this) (not_lt.mpr hq1.le)

lemma h3l_iSup_sup (f : ℕ → ℝ≥0∞) : ⨆ k, f k = ⨆ J : ℕ, (Finset.range J).sup f := by
  refine le_antisymm (iSup_le fun k => ?_) (iSup_le fun J => Finset.sup_le fun k _ => le_iSup f k)
  exact le_iSup_of_le (k + 1) (Finset.le_sup (f := f) (Finset.mem_range.mpr (Nat.lt_succ_self k)))

lemma h3l_meas_sup (J : ℕ) (f : ℕ → ℝ → ℝ≥0∞) (h : ∀ k, Measurable (f k)) :
    Measurable fun r => (Finset.range J).sup (fun k => f k r) := by
  induction J with
  | zero => simpa using measurable_const
  | succ J ih =>
    have : (fun r => (Finset.range (J + 1)).sup (fun k => f k r)) =
        fun r => (Finset.range J).sup (fun k => f k r) ⊔ f J r := by
      funext r; rw [Finset.range_add_one, Finset.sup_insert, sup_comm]
    rw [this]; exact ih.sup (h J)

/-- Abstract assembly of part (b): Lindelöf, finite maxima, Fatou. -/
theorem h3l_assembly {ι : Type*} (a : ι → ℝ → ℝ≥0∞) (A : ι → ℕ → ℝ → ℝ≥0∞) (c : ℕ → ℝ → ℝ≥0∞) (t : ℝ)
    (hac : ∀ i, Continuous (a i)) (hAm : ∀ i n, Measurable (A i n))
    (hAc : ∀ i, ∀ᶠ n in atTop, ∀ r ∈ Icc (0 : ℝ) t, A i n r ≤ c n r)
    (hlim : ∀ i, ∀ r ∈ Icc (0 : ℝ) t, a i r ≤ liminf (fun n => A i n r) atTop) :
    ∫⁻ r in Icc (0 : ℝ) t, ⨆ i, a i r ≤ liminf (fun n => ∫⁻ r in Icc (0 : ℝ) t, c n r) atTop := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
  obtain ⟨s, hs⟩ := h3l_lindelof a hac
  calc ∫⁻ r in Icc (0 : ℝ) t, ⨆ i, a i r ≤ ∫⁻ r in Icc (0 : ℝ) t, ⨆ k, a (s k) r := lintegral_mono fun r => hs r
    _ = ∫⁻ r in Icc (0 : ℝ) t, ⨆ J : ℕ, (Finset.range J).sup (fun k => a (s k) r) := by
        exact lintegral_congr fun r => h3l_iSup_sup _
    _ = ⨆ J : ℕ, ∫⁻ r in Icc (0 : ℝ) t, (Finset.range J).sup (fun k => a (s k) r) := by
        refine lintegral_iSup (fun J => ?_) (fun J J' hJ r => ?_)
        · exact h3l_meas_sup J (fun k => a (s k)) fun k => (hac (s k)).measurable
        · exact Finset.sup_mono (Finset.range_mono hJ)
    _ ≤ _ := by
        refine iSup_le fun J => ?_
        set M : ℕ → ℝ → ℝ≥0∞ := fun n r => (Finset.range J).sup (fun k => A (s k) n r) with hM
        have hMm : ∀ n, Measurable (M n) := fun n => h3l_meas_sup J (fun k => A (s k) n) fun k => hAm _ _
        have hev : ∀ᶠ n in atTop, ∀ r ∈ Icc (0 : ℝ) t, M n r ≤ c n r := by
          have : ∀ᶠ n in atTop, ∀ k ∈ Finset.range J, ∀ r ∈ Icc (0 : ℝ) t, A (s k) n r ≤ c n r :=
            (Filter.eventually_all_finset _).mpr fun k _ => hAc (s k)
          filter_upwards [this] with n hn r hr
          exact Finset.sup_le fun k hk => hn k hk r hr
        calc ∫⁻ r in Icc (0 : ℝ) t, (Finset.range J).sup (fun k => a (s k) r)
            ≤ ∫⁻ r in Icc (0 : ℝ) t, liminf (fun n => M n r) atTop := by
              refine setLIntegral_mono' measurableSet_Icc fun r hr => Finset.sup_le fun k hk => ?_
              refine (hlim (s k) r hr).trans (liminf_le_liminf (Eventually.of_forall fun n => ?_))
              exact Finset.le_sup (f := fun k => A (s k) n r) hk
          _ ≤ liminf (fun n => ∫⁻ r in Icc (0 : ℝ) t, M n r) atTop := lintegral_liminf_le hMm
          _ ≤ liminf (fun n => ∫⁻ r in Icc (0 : ℝ) t, c n r) atTop := by
              refine liminf_le_liminf ?_
              filter_upwards [hev] with n hn
              exact setLIntegral_mono' measurableSet_Icc hn

end
end HRS.MC.CepH3
