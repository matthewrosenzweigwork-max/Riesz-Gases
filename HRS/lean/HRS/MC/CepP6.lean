import HRS.MC.CepP6Aux1
import HRS.MC.CepP5

/-!
# Packet P6: assembly of Proposition B.4
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.CepP6

open HRS HRS.MC.CepP3

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {d N : ℕ}

theorem cep_P6_selected_law_smoothing_proof [IsProbabilityMeasure P] (hN : 2 ≤ N) [NeZero N]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    {D : DynData d} (hβ : 0 < D.invβ) (hV : Torus.IsSmooth D.V) {T : ℝ} (hT : 0 < T)
    {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (hX : SelectedFlow P D T X₀ W X) (hF : IsFilteredSolution P ℱ W' W X) :
    ∃ f : ℝ → Config d N → ℝ,
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × (Fin N → Euc d) => f p.1 (fun i => Torus.mk (p.2 i)))
        (Set.Ioo 0 T ×ˢ {Y : Fin N → Euc d | (fun i => Torus.mk (Y i)) ∉ collisionSet d N}) ∧
      (∀ r ∈ Set.Ioo 0 T, ∀ x ∉ collisionSet d N, 0 ≤ f r x) ∧
      (∀ t ∈ Set.Ioo 0 T,
        (selectedLaw P X t).restrict (collisionSet d N)ᶜ =
          ((volume : Measure (Config d N)).restrict (collisionSet d N)ᶜ).withDensity
            (fun x => ENNReal.ofReal (f t x))) ∧
      (∀ r ∈ Set.Ioo 0 T, ∀ x ∉ collisionSet d N,
        HasDerivAt (fun r' => f r' x) (fkeForward D f r x) r) ∧
      ((∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ) ≤ T → X t ω ∉ collisionSet d N) →
        ∀ t ∈ Set.Ioo 0 T, selectedLaw P X t (collisionSet d N) = 0 ∧
          selectedLaw P X t =
            (volume : Measure (Config d N)).withDensity (fun x => ENNReal.ofReal (f t x))) := by
  classical
  obtain ⟨f, hfs, hf0, hρ⟩ := HRS.MC.CepP3.cep_P3_spacetime_density_proof hN hβ hV hT hX hF
  have h4 := HRS.MC.CepP4.cep_P4_time_slices_proof hN hV hT hX hF hfs hf0 hρ
  have h5 := HRS.MC.CepP5.cep_P5_forward_equation_core hN hV hT hX hF hfs hf0 hρ
  refine ⟨f, hfs, hf0, h4, h5, fun hnc t ht => ?_⟩
  have hd : 1 ≤ d := by
    by_contra h
    have h0 : d = 0 := by omega
    have := D.hsd
    have := D.hs0
    subst h0
    simp at *
    linarith
  have hC : MeasurableSet (collisionSet d N) := (isClosed_collisionSet d N).measurableSet
  have hC0 : selectedLaw P X t (collisionSet d N) = 0 := by
    have hC' := selectedFlow_toContact hX
    have hXm : Measurable (X (Real.toNNReal t)) := hC'.adapted _
    unfold selectedLaw law
    rw [Measure.map_apply hXm hC]
    have hle : ((Real.toNNReal t : ℝ≥0) : ℝ) ≤ T := by
      rw [Real.coe_toNNReal t ht.1.le]; exact ht.2.le
    have := hnc.mono fun ω hω => hω (Real.toNNReal t) hle
    show P {ω | X (Real.toNNReal t) ω ∈ collisionSet d N} = 0
    rw [ae_iff] at this
    simpa using this
  refine ⟨hC0, ?_⟩
  have hvol : (volume : Measure (Config d N)) (collisionSet d N) = 0 := volume_collisionSet hd
  have e1 : (selectedLaw P X t).restrict (collisionSet d N)ᶜ = selectedLaw P X t := by
    refine Measure.restrict_eq_self_of_ae_mem ?_
    rw [ae_iff]
    simpa using hC0
  have e2 : (volume : Measure (Config d N)).restrict (collisionSet d N)ᶜ = volume := by
    refine Measure.restrict_eq_self_of_ae_mem ?_
    rw [ae_iff]
    simpa using hvol
  rw [← e1, h4 t ht, e2]

end HRS.MC.CepP6
