import HRS.Stochastic.SelectedFlow

/-!
# Packet M (CEPH5 measure lemmas): `h5_cond_brownian`, `h5_cond_indep`
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepH5Pf

open HRS

section Cond

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {N : ℕ} [NeZero N]

/-- Conditioning on an `X₀`-event leaves the law of the (path-valued) `W` unchanged. -/
theorem h5M_cond_path [IsProbabilityMeasure P] {X₀ : Ω → Config 1 N} (hX₀ : Measurable X₀)
    {W : ℝ≥0 → Ω → (Fin N → Euc 1)} (hind : IndepFun X₀ (fun ω => fun t => W t ω) P)
    {B : Set (Config 1 N)} (hB : MeasurableSet B) {E : Set (ℝ≥0 → Fin N → Euc 1)}
    (hE : MeasurableSet E) (hPB : P (X₀ ⁻¹' B) ≠ 0) :
    ProbabilityTheory.cond P (X₀ ⁻¹' B) ((fun ω => fun t => W t ω) ⁻¹' E)
      = P ((fun ω => fun t => W t ω) ⁻¹' E) := by
  rw [ProbabilityTheory.cond_apply (hX₀ hB) P]
  rw [hind.measure_inter_preimage_eq_mul B E hB hE, ← mul_assoc,
    ENNReal.inv_mul_cancel hPB (measure_ne_top P _), one_mul]

theorem h5_cond_indep_proof [IsProbabilityMeasure P] {X₀ : Ω → Config 1 N} (hX₀ : Measurable X₀)
    {W : ℝ≥0 → Ω → (Fin N → Euc 1)} (hind : IndepFun X₀ (fun ω => fun t => W t ω) P)
    {B : Set (Config 1 N)} (hB : MeasurableSet B) (hPB : P (X₀ ⁻¹' B) ≠ 0) :
    IndepFun X₀ (fun ω => fun t => W t ω) (ProbabilityTheory.cond P (X₀ ⁻¹' B)) := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro B' E hB' hE
  have hA : MeasurableSet (X₀ ⁻¹' B) := hX₀ hB
  have e1 : X₀ ⁻¹' B ∩ (X₀ ⁻¹' B' ∩ (fun ω => fun t => W t ω) ⁻¹' E)
      = X₀ ⁻¹' (B ∩ B') ∩ (fun ω => fun t => W t ω) ⁻¹' E := by
    ext ω; simp only [mem_inter_iff, mem_preimage]; tauto
  have e2 : X₀ ⁻¹' B ∩ X₀ ⁻¹' B' = X₀ ⁻¹' (B ∩ B') := by
    ext ω; simp only [mem_inter_iff, mem_preimage]
  rw [h5M_cond_path hX₀ hind hB hE hPB]
  have e4 : P (X₀ ⁻¹' B ∩ (X₀ ⁻¹' B' ∩ (fun ω => fun t => W t ω) ⁻¹' E))
      = P (X₀ ⁻¹' (B ∩ B')) * P ((fun ω => fun t => W t ω) ⁻¹' E) := by
    rw [e1]; exact hind.measure_inter_preimage_eq_mul (B ∩ B') E (hB.inter hB') hE
  rw [ProbabilityTheory.cond_apply hA P, ProbabilityTheory.cond_apply hA P, e4]
  rw [← mul_assoc]; rfl

/-- Each coordinate path is a measurable function of the full path. -/
theorem h5M_meas_coord (i : Fin N) (j : Fin 1) :
    Measurable fun w : ℝ≥0 → Fin N → Euc 1 => fun t : ℝ≥0 => w t i j := by
  fun_prop

theorem h5M_map_eq [IsProbabilityMeasure P] {X₀ : Ω → Config 1 N} (hX₀ : Measurable X₀)
    {W : ℝ≥0 → Ω → (Fin N → Euc 1)} (hind : IndepFun X₀ (fun ω => fun t => W t ω) P)
    {B : Set (Config 1 N)} (hB : MeasurableSet B) (hPB : P (X₀ ⁻¹' B) ≠ 0)
    {γ : Type*} [MeasurableSpace γ] {f : Ω → γ} (hf : AEMeasurable f P)
    (g : (ℝ≥0 → Fin N → Euc 1) → γ) (hg : Measurable g) (hfg : ∀ ω, f ω = g (fun t => W t ω)) :
    (ProbabilityTheory.cond P (X₀ ⁻¹' B)).map f = P.map f := by
  ext s hs
  rw [Measure.map_apply_of_aemeasurable (hf.mono_ac ProbabilityTheory.cond_absolutelyContinuous) hs,
    Measure.map_apply_of_aemeasurable hf hs]
  have : f ⁻¹' s = (fun ω => fun t => W t ω) ⁻¹' (g ⁻¹' s) := by
    ext ω; simp [hfg]
  rw [this]
  exact h5M_cond_path hX₀ hind hB (hg hs) hPB

theorem h5_cond_brownian_proof [IsProbabilityMeasure P] {X₀ : Ω → Config 1 N} (hX₀ : Measurable X₀)
    {W : ℝ≥0 → Ω → (Fin N → Euc 1)} (hW : IsVectorBrownian P W)
    (hind : IndepFun X₀ (fun ω => fun t => W t ω) P)
    {B : Set (Config 1 N)} (hB : MeasurableSet B) (hPB : P (X₀ ⁻¹' B) ≠ 0) :
    IsVectorBrownian (ProbabilityTheory.cond P (X₀ ⁻¹' B)) W := by
  have hQP : ProbabilityTheory.cond P (X₀ ⁻¹' B) ≪ P := ProbabilityTheory.cond_absolutelyContinuous
  refine ⟨fun i j => ?_, ?_⟩
  · have h := hW.1 i j
    refine ⟨⟨fun I => ?_⟩, hQP.ae_le h.cont⟩
    have hl := h.hasLaw I
    refine ⟨hl.aemeasurable.mono_ac hQP, ?_⟩
    rw [h5M_map_eq hX₀ hind hB hPB hl.aemeasurable
      (fun w => I.restrict (fun t => w t i j)) ?_ (fun ω => rfl)]
    · exact hl.map_eq
    · show Measurable fun w : ℝ≥0 → Fin N → Euc 1 => fun t : I => w t i j
      fun_prop
  · have h2 := hW.2
    rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at h2 ⊢
    intro S sets hsets
    have hmeas : MeasurableSet (⋂ i ∈ S, (fun w : ℝ≥0 → Fin N → Euc 1 => fun t : ℝ≥0 => w t i.1 i.2) ⁻¹' sets i) :=
      MeasurableSet.biInter S.countable_toSet fun i hi => (h5M_meas_coord i.1 i.2) (hsets i hi)
    have e : (⋂ i ∈ S, (fun ω => fun t : ℝ≥0 => W t ω i.1 i.2) ⁻¹' sets i)
        = (fun ω => fun t => W t ω) ⁻¹'
          (⋂ i ∈ S, (fun w : ℝ≥0 → Fin N → Euc 1 => fun t : ℝ≥0 => w t i.1 i.2) ⁻¹' sets i) := by
      ext ω; simp
    rw [e, h5M_cond_path hX₀ hind hB hmeas hPB, ← e, h2 S hsets]
    refine Finset.prod_congr rfl fun i hi => ?_
    have : (fun ω => fun t : ℝ≥0 => W t ω i.1 i.2) ⁻¹' sets i
        = (fun ω => fun t => W t ω) ⁻¹'
          ((fun w : ℝ≥0 → Fin N → Euc 1 => fun t : ℝ≥0 => w t i.1 i.2) ⁻¹' sets i) := rfl
    rw [this, h5M_cond_path hX₀ hind hB ((h5M_meas_coord i.1 i.2) (hsets i hi)) hPB]

end Cond

end HRS.MC.CepH5Pf
