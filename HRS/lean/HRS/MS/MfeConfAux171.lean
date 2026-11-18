import HRS.MS.MfeConfAux170

/-!
# S.B.1 (SB5), R3d (part 2): `SbMovEnt` at the horizon `T = 0`

At `T = 0` the entropy inequality is trivial (the time integral runs over a null set); what remains is the integrability of the
source under the initial law, which follows from the coarse commutator bound and `En ∈ L¹` (`sb1_Q_conv`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory InformationTheory
open HRS HRS.Whole
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

variable {d N : ℕ}

section Main

variable {D : Whole.WholeDyn d} {C B C3 : ℝ} {ρ : ℝ → Euc d → ℝ} (H : Sb1Tr3 D 0 C B C3 ρ)

include H

theorem sb1_movEnt_T0 (hN : 1 ≤ N) (hβ : 0 < D.invβ) {a b : ℝ} (hco : Sb1Coarse D N 0 ρ a b) {K0 : ℝ}
    (hK : Whole.HasLipBoundW (Whole.mfeTransportW D (ρ 0)) K0) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Y : ℝ≥0 → Ω → Whole.EucConfig d N} (hYm : ∀ t, Measurable (Y t))
    (hnc : ∀ᵐ ζ ∂P, ∀ t : ℝ≥0, (t : ℝ) ≤ 0 → Y t ζ ∉ eucCollisionSet d N) :
    SbMovEnt D N 0 ρ P (Y 0) Y := by
  intro hprem
  have hd := H.tr.hd
  have hs0 := H.tr.hs0
  have hsd := H.tr.hsd
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 0 := ⟨le_rfl, le_rfl⟩
  have hmem : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 0 → t = 0 := fun t ht => le_antisymm ht.2 ht.1
  obtain ⟨hKr, hL⟩ := sb1_lip_of_hasLip hK
  haveI : IsProbabilityMeasure (P.map (Y 0)) :=
    (Measure.isProbabilityMeasure_map_iff (hYm 0).aemeasurable).2 inferInstance
  have hnull : (volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 0) = 0 :=
    Measure.restrict_eq_zero.2 (by simp)
  have hCNint : Integrable (sb1CN D N ρ 0) (P.map (Y 0)) := by
    have hprem' : relEntropy (P.map (Y 0)) (Whole.modulatedGibbs (Whole.rieszKernel d D.s) N D.invβ⁻¹
        (Whole.withDensityReal (ρ 0))) ≠ ⊤ := hprem
    have hEn := (sb1_Q_conv hd hs0 hsd hN (inv_pos.2 hβ) (sb1KerU_riesz d D.s hs0) (H.rho hd h0) hprem').2
    have hcol := sb1_coll_ae hYm hnc h0
    simp only [Real.toNNReal_zero] at hcol
    refine ((hEn.const_mul (K0 * a)).add (integrable_const (K0 * b))).mono'
      (sb1_CN_meas (N := N) H h0 hKr hL).aestronglyMeasurable ?_
    filter_upwards [hcol] with Z hZ
    rw [Real.norm_eq_abs]
    have := hco.2.2 0 h0 K0 hKr hL Z hZ
    calc |sb1CN D N ρ 0 Z| ≤ K0 * (a * sb1En (Whole.rieszKernel d D.s) (ρ 0) Z + b) := this
      _ = K0 * a * sb1En (Whole.rieszKernel d D.s) (ρ 0) Z + K0 * b := by ring
  have hSrc : Integrable (sb1Src D N ρ 0) (P.map (Y 0)) := by
    unfold sb1Src
    exact (hCNint.sub (integrable_const _)).const_mul _
  refine ⟨fun t ht => ?_, fun r hr => ?_⟩
  · have ht0 := hmem t ht
    subst ht0
    simp only [Real.toNNReal_zero]
    refine ⟨hprem, fun r hr => ?_, ?_, ?_⟩
    · have := hmem r hr; subst this; simpa using hSrc
    · rw [IntegrableOn, hnull]; exact integrable_zero_measure
    · rw [hnull, integral_zero_measure, add_zero]
  · have := hmem r hr; subst this
    exact sb1_CN_Qint H hN hβ h0 hKr hL

end Main

end HRS.MS.MfeConf
