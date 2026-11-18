import HRS.MS.MfeConfAux132

/-!
# S.B.1, R2 (part 4): the hypotheses `hBmeas` and `hTM` of `sb1_bdd_movEnt`, discharged

`sb1_hBmeas` and `sb1_hTM` have exactly the shape of the hypotheses `hBmeas`, `hTM` of `sb1_bdd_entropy` / `sb1_bdd_movEnt`
(Aux121/122), for the regularising family `sb1kM`.
-/

open MeasureTheory Filter Topology ProbabilityTheory InformationTheory
open HRS HRS.Whole HRS.MD.EQLawPath HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Mol HRS.MP.SelfSimP4Impl
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace HRS.MS.MfeConf

variable {d N : ℕ}

section Main

variable {D : Whole.WholeDyn d} {T C B C3 : ℝ} {ρ : ℝ → Euc d → ℝ} (H : Sb1Tr3 D T C B C3 ρ)

include H

theorem sb1_hBmeas (hT : 0 < T) : ∀ (M : ℕ) (r : ℝ),
    Measurable (sb1_lv_B (N := N) D (sb1kM d D.s M) hT.le ρ r) :=
  fun M r => sb1_lv_B_meas H hT.le (sb1kM_isKernel D.s H.tr.hs0 M) r

theorem sb1_hTM (hT : 0 < T) (hN : 1 ≤ N) (hβ : 0 < D.invβ) (Kf : ℝ → ℝ) (hKi : IntegrableOn Kf (Set.Icc 0 T))
    (hLip : ∀ t ∈ Set.Icc (0 : ℝ) T, Whole.HasLipBoundW (Whole.mfeTransportW D (ρ t)) (Kf t))
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {Pm : Measure Ω} [IsProbabilityMeasure Pm]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {X₀ : Ω → Whole.EucConfig d N} {X : ℝ≥0 → Ω → Whole.EucConfig d N}
    (hX : Whole.IsWholeStrongSolution Pm D T X₀ W X) (hF : Whole.IsWholeFilteredSolution Pm ℱ W' W X)
    (hX₀ : Measurable X₀) (hmom : ∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂(Pm.map X₀) < ⊤) :
    ∀ M : ℕ, AEStronglyMeasurable (fun s => ∫ y, (-(D.invβ⁻¹ * N) *
        (sb1_lv_Ck D (sb1kM d D.s M) N ρ s y - sb1_lv_EQ D (sb1kM d D.s M) N ρ s) +
        sb1_lv_B (N := N) D (sb1kM d D.s M) hT.le ρ s y)
        ∂(sb1Flow D (sb1kM d D.s M) N (Pm.map (X 0))
          (Pm.map (bfPath (p4r_shiftFil_brownian hF.brownian))) s)) (volume.restrict (Set.Icc 0 T)) := by
  intro M
  have h0eq : Pm.map (X 0) = Pm.map X₀ := Measure.map_congr hX.init
  haveI : IsProbabilityMeasure (Pm.map X₀) := (Measure.isProbabilityMeasure_map_iff hX₀.aemeasurable).2 inferInstance
  haveI : IsProbabilityMeasure (Pm.map (X 0)) := by rw [h0eq]; infer_instance
  exact sb1_ent_M_meas H hT.le hβ hN (sb1kM_isKernel D.s H.tr.hs0 M) Kf hKi hLip (Pm.map (X 0))
    (by rw [h0eq]; exact hmom) (p4r_shiftFil_brownian hF.brownian)

end Main

end HRS.MS.MfeConf
