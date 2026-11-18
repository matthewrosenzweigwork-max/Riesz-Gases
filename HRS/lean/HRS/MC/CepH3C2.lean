import HRS.MC.CepH3C1

/-!
# Packet CEPH3, part C2: monotonicity, restriction invariance, data processing and isomorphism for `F`
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepH3

open HRS

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- Larger reference measure, smaller entropy. -/
theorem h3c_F_mono (ν m m' : Measure α) [IsProbabilityMeasure ν] [IsFiniteMeasure m] [IsFiniteMeasure m']
    (hmm' : m ≤ m') (h0 : m univ ≠ 0) : h3c_F ν m' ≤ h3c_F ν m := by
  classical
  have h0' : m' univ ≠ 0 := fun h => h0 (le_antisymm (h ▸ hmm' univ) bot_le)
  rw [h3c_F_eq ν m h0, h3c_F_eq ν m' h0']
  by_cases hA : ν ≪ m ∧ Integrable (llr ν m) ν
  swap
  · unfold h3c_Fu; rw [if_neg hA]; exact le_top
  obtain ⟨hA, hI⟩ := hA
  have hmm'ac : m ≪ m' := Measure.absolutelyContinuous_of_le hmm'
  have hA' : ν ≪ m' := hA.trans hmm'ac
  -- pointwise comparison of the log-likelihood ratios
  have hle : llr ν m' ≤ᵐ[ν] llr ν m := by
    have h1 : ν.rnDeriv m * m.rnDeriv m' =ᵐ[m] ν.rnDeriv m' := Measure.rnDeriv_mul_rnDeriv' hmm'ac
    have h2 : m.rnDeriv m' ≤ᵐ[m'] 1 := Measure.rnDeriv_le_one_of_le hmm'
    filter_upwards [hA.ae_le h1, hA.ae_le (hmm'ac.ae_le h2), Measure.rnDeriv_pos hA',
      hA'.ae_le (Measure.rnDeriv_lt_top ν m'), hA.ae_le (Measure.rnDeriv_lt_top ν m)] with x hx1 hx2 hx3 hx4 hx5
    simp only [llr]
    refine Real.log_le_log (ENNReal.toReal_pos hx3.ne' hx4.ne) ?_
    refine ENNReal.toReal_mono hx5.ne ?_
    rw [← hx1]
    calc (ν.rnDeriv m * m.rnDeriv m') x ≤ ν.rnDeriv m x * 1 := by
          simp only [Pi.mul_apply]
          gcongr
          simpa using hx2
      _ = ν.rnDeriv m x := mul_one _
  -- integrability for `m'`
  have hI' : Integrable (llr ν m') ν := by
    have hexp : Integrable (fun x => Real.exp (-llr ν m' x)) ν := by
      refine (Measure.integrable_toReal_rnDeriv (μ := m') (ν := ν)).congr ?_
      filter_upwards [exp_neg_llr hA'] with x hx
      rw [hx]
    refine Integrable.mono' (g := fun x => |llr ν m x| + Real.exp (-llr ν m' x)) (hI.abs.add hexp)
      (measurable_llr ν m').aestronglyMeasurable ?_
    filter_upwards [hle] with x hx
    rw [Real.norm_eq_abs]
    have h3 : -llr ν m' x ≤ Real.exp (-llr ν m' x) := by
      linarith [Real.add_one_le_exp (-llr ν m' x)]
    rw [abs_le]
    constructor
    · nlinarith [abs_nonneg (llr ν m x)]
    · have := le_abs_self (llr ν m x); linarith [abs_nonneg (llr ν m x), Real.exp_pos (-llr ν m' x)]
  unfold h3c_Fu
  rw [if_pos ⟨hA', hI'⟩, if_pos ⟨hA, hI⟩]
  exact_mod_cast integral_mono_ae hI' hI hle

/-- Restriction to a set carrying `ν` does not change `F`. -/
theorem h3c_F_restrict (ν m : Measure α) [IsProbabilityMeasure ν] [IsFiniteMeasure m] {S : Set α}
    (hS : MeasurableSet S) (hνS : ν Sᶜ = 0) (h0 : m.restrict S univ ≠ 0) :
    h3c_F ν (m.restrict S) ≤ h3c_F ν m := by
  classical
  have h0' : m univ ≠ 0 := fun h => h0 (le_antisymm
    ((Measure.restrict_apply_le S univ).trans (le_of_eq h)) bot_le)
  rw [h3c_F_eq ν m h0', h3c_F_eq ν (m.restrict S) h0]
  by_cases hA : ν ≪ m ∧ Integrable (llr ν m) ν
  swap
  · unfold h3c_Fu; rw [if_neg hA]; exact le_top
  obtain ⟨hA, hI⟩ := hA
  have hA' : ν ≪ m.restrict S := by
    intro B hB
    have hm : m (B ∩ S) = 0 := by simpa [Measure.restrict_apply' hS] using hB
    have h1 : ν (B ∩ S) = 0 := hA hm
    have h2 : ν (B ∩ Sᶜ) = 0 := measure_mono_null (inter_subset_right) hνS
    have : ν B ≤ ν (B ∩ S) + ν (B ∩ Sᶜ) := by
      calc ν B = ν ((B ∩ S) ∪ (B ∩ Sᶜ)) := by rw [← inter_union_distrib_left, union_compl_self, inter_univ]
        _ ≤ _ := measure_union_le _ _
    rw [h1, h2] at this
    simpa using this
  have hrs : m.restrict S ≪ m := Measure.restrict_le_self.absolutelyContinuous
  have heq : llr ν (m.restrict S) =ᵐ[ν] llr ν m := by
    have h1 : ν.rnDeriv (m.restrict S) * (m.restrict S).rnDeriv m =ᵐ[m.restrict S] ν.rnDeriv m :=
      Measure.rnDeriv_mul_rnDeriv' hrs
    have h2 : (m.restrict S).rnDeriv m =ᵐ[m] S.indicator 1 := Measure.rnDeriv_restrict_self m hS
    have h3 : ∀ᵐ x ∂(m.restrict S), x ∈ S := ae_restrict_mem hS
    refine hA'.ae_le ?_
    filter_upwards [h1, hrs.ae_le h2, h3] with x hx1 hx2 hx3
    simp only [llr]
    rw [← hx1]
    simp only [Pi.mul_apply]
    rw [hx2]
    simp [Set.indicator_of_mem hx3]
  have hI' : Integrable (llr ν (m.restrict S)) ν := hI.congr (heq.symm)
  unfold h3c_Fu
  rw [if_pos ⟨hA', hI'⟩, if_pos ⟨hA, hI⟩]
  have : ∫ x, llr ν (m.restrict S) x ∂ν = ∫ x, llr ν m x ∂ν := integral_congr_ae heq
  rw [this]

/-- Data processing for `F`. -/
theorem h3c_F_map_le (ν m : Measure α) [IsProbabilityMeasure ν] [IsFiniteMeasure m] (h0 : m univ ≠ 0)
    {f : α → β} (hf : Measurable f) : h3c_F (ν.map f) (m.map f) ≤ h3c_F ν m := by
  unfold h3c_F
  have hu : (m.map f) univ = m univ := by rw [Measure.map_apply hf MeasurableSet.univ, Set.preimage_univ]
  rw [hu, ← Measure.map_smul _ hf.aemeasurable]
  have := h3c_normalised_isProb m h0
  exact EReal.sub_le_sub (by exact_mod_cast klDiv_map_le ν ((m univ)⁻¹ • m) hf) le_rfl

/-- Isomorphism invariance of `F` (left inverse on a set carrying both measures). -/
theorem h3c_F_map_eq (ν m : Measure α) [IsProbabilityMeasure ν] [IsFiniteMeasure m] {f : α → β}
    {g : β → α} (hf : Measurable f) (hg : Measurable g) {S : Set α} (hS : MeasurableSet S)
    (hleft : ∀ x ∈ S, g (f x) = x) (hν : ν Sᶜ = 0) (hm : m Sᶜ = 0) (h0 : m univ ≠ 0) :
    h3c_F (ν.map f) (m.map f) = h3c_F ν m := by
  refine le_antisymm (h3c_F_map_le ν m h0 hf) ?_
  have : IsProbabilityMeasure (ν.map f) := ⟨by rw [Measure.map_apply hf MeasurableSet.univ, Set.preimage_univ]; exact measure_univ⟩
  have : IsFiniteMeasure (m.map f) := Measure.isFiniteMeasure_map m f
  have h0f : (m.map f) univ ≠ 0 := by rwa [Measure.map_apply hf MeasurableSet.univ, Set.preimage_univ]
  have := h3c_F_map_le (ν.map f) (m.map f) h0f hg
  have e1 : (ν.map f).map g = ν := by
    rw [Measure.map_map hg hf]
    have : g ∘ f =ᵐ[ν] id := by
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hν |>.mono fun x hx => (not_not.mp hx)] with x hx
      exact hleft x hx
    rw [Measure.map_congr this, Measure.map_id]
  have e2 : (m.map f).map g = m := by
    rw [Measure.map_map hg hf]
    have : g ∘ f =ᵐ[m] id := by
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hm |>.mono fun x hx => (not_not.mp hx)] with x hx
      exact hleft x hx
    rw [Measure.map_congr this, Measure.map_id]
  rwa [e1, e2] at this

end HRS.MC.CepH3
