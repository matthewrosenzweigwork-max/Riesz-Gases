import HRS.MC.CepE6aA4

/-!
# Packet CEPE6A, file 5: generic measure-theoretic lemmas

* `e6a_ae_tendsto_zero`: summable `L¹` norms force a.e. convergence to `0`;
* `e6a_Icc_subset_of_ae`: a closed set of `ℝ` containing a.e. point of `[0,T]` contains `[0,T]`;
* `e6a_ae_ae_of_ae_prod`: product-a.e. to iterated a.e.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepE6A

open HRS HRS.MC.Cepa

theorem e6a_ae_tendsto_zero {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : ℕ → α → ℝ≥0∞}
    (hf : ∀ j, Measurable (f j)) {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hb : ∀ j, ∫⁻ x, f j x ∂μ ≤ c * (2⁻¹ : ℝ≥0∞) ^ j) :
    ∀ᵐ x ∂μ, Tendsto (fun j => f j x) atTop (𝓝 0) := by
  have hsum : ∫⁻ x, ∑' j, f j x ∂μ ≠ ⊤ := by
    rw [lintegral_tsum fun j => (hf j).aemeasurable]
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hb)
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    simp [ENNReal.mul_eq_top, hc]
  have hmeas : Measurable fun x => ∑' j, f j x := Measurable.ennreal_tsum hf
  have hae := ae_lt_top hmeas hsum
  filter_upwards [hae] with x hx
  exact ENNReal.tendsto_atTop_zero_of_tsum_ne_top hx.ne

theorem e6a_Icc_subset_of_ae {F : Set ℝ} (hF : IsClosed F) {T : ℝ} (hT : 0 < T)
    (h : ∀ᵐ s ∂(volume.restrict (Icc (0 : ℝ) T)), s ∈ F) : Icc (0 : ℝ) T ⊆ F := by
  have h0 : volume (Icc (0 : ℝ) T ∩ Fᶜ) = 0 := by
    rw [ae_restrict_iff' measurableSet_Icc] at h
    have := ae_iff.1 h
    convert this using 2
    ext s; simp only [mem_inter_iff, mem_compl_iff, mem_setOf_eq]; tauto
  have hIoo : Ioo (0 : ℝ) T ⊆ F := by
    intro s hs
    by_contra hsF
    have hopen : IsOpen (Ioo (0 : ℝ) T ∩ Fᶜ) := isOpen_Ioo.inter hF.isOpen_compl
    have hne : (Ioo (0 : ℝ) T ∩ Fᶜ).Nonempty := ⟨s, hs, hsF⟩
    have hpos := hopen.measure_pos volume hne
    have hsub : Ioo (0 : ℝ) T ∩ Fᶜ ⊆ Icc (0 : ℝ) T ∩ Fᶜ := inter_subset_inter_left _ Ioo_subset_Icc_self
    exact hpos.ne' (measure_mono_null hsub h0)
  have : closure (Ioo (0 : ℝ) T) = Icc (0 : ℝ) T := closure_Ioo hT.ne
  rw [← this]
  exact closure_minimal hIoo hF

theorem e6a_ae_ae_of_ae_prod {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ν : Measure ℝ}
    [SFinite P] [SFinite ν] {q : Ω × ℝ → Prop} (h : ∀ᵐ p ∂(P.prod ν), q p) :
    ∀ᵐ ω ∂P, ∀ᵐ s ∂ν, q (ω, s) :=
  Measure.ae_ae_of_ae_prod h

/-- Fatou for the extended force norm along alcove-valued approximations. -/
theorem e6a_fatou {a : ℝ} (ha : 0 < a) {N : ℕ} {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {Zl : α → Ch N} (hZl : Measurable Zl) {W : ℕ → α → Ch N} (hW : ∀ j, Measurable (W j))
    (hWa : ∀ j p, W j p ∈ cep_Alcove N) {c : ℝ≥0∞}
    (hb : ∀ j, ∫⁻ p, ENNReal.ofReal (∑ i, |(gradient (cep_chamberPot a N) (W j p)) i|) ∂μ ≤ c)
    (hconv : ∀ᵐ p ∂μ, Tendsto (fun j => W j p) atTop (𝓝 (Zl p))) :
    ∫⁻ p, e6a_ext a N (Zl p) ∂μ ≤ c := by
  classical
  have hmeasE : ∀ j, Measurable fun p => ENNReal.ofReal (∑ i, |(gradient (cep_chamberPot a N) (W j p)) i|) := by
    intro j
    have hg : Measurable (gradient (cep_chamberPot a N)) := by
      unfold gradient
      exact (InnerProductSpace.toDual ℝ (Ch N)).symm.continuous.measurable.comp (measurable_fderiv ℝ _)
    refine ENNReal.measurable_ofReal.comp ?_
    exact Finset.measurable_sum _ fun i _ => ((EuclideanSpace.proj i).continuous.measurable.comp (hg.comp (hW j))).abs
  calc ∫⁻ p, e6a_ext a N (Zl p) ∂μ
      ≤ ∫⁻ p, liminf (fun j => ENNReal.ofReal (∑ i, |(gradient (cep_chamberPot a N) (W j p)) i|)) atTop ∂μ := by
        refine lintegral_mono_ae ?_
        filter_upwards [hconv] with p hp
        exact e6a_ext_le_liminf ha (fun j => hWa j p) hp
    _ ≤ liminf (fun j => ∫⁻ p, ENNReal.ofReal (∑ i, |(gradient (cep_chamberPot a N) (W j p)) i|) ∂μ) atTop :=
        lintegral_liminf_le hmeasE
    _ ≤ c := liminf_le_of_frequently_le' (Eventually.of_forall hb).frequently

end HRS.MC.CepE6A
