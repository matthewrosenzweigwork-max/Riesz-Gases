import HRS.MS.Fp81S21GaussianDSource
import HRS.MS.Fp81S21GaussianLinearChaos
import HRS.MS.Fp81S21VersionGTime2

/-! Packet 35, unit 6: shift-uniform moments of the literal retained totals.
Charts precede the radius; all source data follow it. The three moment radii
are intersected here. Source/canonical/quadratic existence radii belong to the
selection step: this generic theorem takes those already-selected witnesses.
The constants and separate operator families precede the window start and even
the history families. Histories exist by the selected payloads, and the moment
certificate holds for EVERY compatible pair, preserving prior selections.
The totals below are exactly Dcum/Jcum at a+p.T, extended by zero for a<0.
No additional analytic premise is imposed. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology Set
open scoped ENNReal
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6

/-- Compatible operators and histories, and uniform moments for every supplied
history of the selected source and canonical/quadratic fields. -/
theorem fp81s21_gaussian35_moments
    (p : Parameters)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2)) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ R : Trajectory p δ,
      ∀ {hμ₀ : IsProbabilityMeasure (r26t3_mu R 0)}
        (src : fp81s21_gaussian_source_retained_data p R hμ₀)
        (εG εB : ℕ → ℝ) (MUG : ℝ), 0 ≤ MUG →
      ∀ (canon : fp81s21_gaussian_V2_G_canonicalFamily p Es E R MUG εG)
        (S : fp81s21_QuadraticPhysical31 p R Es E εB),
      ∃ cD KD cJ KJ MD MJ MZ : ℝ,
        0 < cD ∧ 0 ≤ KD ∧ 0 < cJ ∧ 0 ≤ KJ ∧ 0 ≤ MD ∧ 0 ≤ MJ ∧ 0 ≤ MZ ∧
      ∃ (OD : ∀ a : ℝ, 0 ≤ a →
          r26t6_IntervalOperators E (r26t3_coeff R) p.T a cD KD)
        (OJ : ∀ a : ℝ, 0 ≤ a →
          r26t6_IntervalOperators E (r26t3_coeff R) p.T a cJ KJ),
      let Hist := fun a : ℝ => src.G0.Ω →
        Lp r26t6_Coeff 2 (volume.restrict (Icc (0 : ℝ) (a + p.T)))
      let qG := fp81s21_gaussian_embedFamily p Es E (canon.q src.G0)
      (∃ UB UG : ∀ a : ℝ, 0 ≤ a → Hist a,
        (∀ a ha, fp81s21_TimeL2Rep src.G0.P (S.qe src.G0)
          (S.Kstar ^ 4 * S.B / 2) 0 (a + p.T) (UB a ha)) ∧
        (∀ a ha, fp81s21_TimeL2Rep src.G0.P qG MUG 0 (a + p.T) (UG a ha))) ∧
      ∀ UB UG : ∀ a : ℝ, 0 ≤ a → Hist a,
        (∀ a ha, fp81s21_TimeL2Rep src.G0.P (S.qe src.G0)
          (S.Kstar ^ 4 * S.B / 2) 0 (a + p.T) (UB a ha)) →
        (∀ a ha, fp81s21_TimeL2Rep src.G0.P qG MUG 0 (a + p.T) (UG a ha)) →
      let D := fun a : ℝ => if ha : 0 ≤ a then
        fp81s21_gaussian_Dcum (OD a ha) (add_nonneg ha p.hT.le) (UB a ha) (a + p.T)
        else 0
      let J := fun a : ℝ => if ha : 0 ≤ a then
        fp81s21_gaussian_Jcum (OJ a ha) (add_nonneg ha p.hT.le) (UG a ha) (a + p.T)
        else 0
      ∀ a : ℝ, 0 ≤ a →
        MemLp (D a) 3 src.G0.P ∧ (∫ ω, ‖D a ω‖ ^ 3 ∂src.G0.P) ≤ MD ∧
        MemLp (J a) 2 src.G0.P ∧ (∫ ω, ‖J a ω‖ ^ 2 ∂src.G0.P) ≤ MJ ∧
        MemLp (r26t3_Zpath src.G0 a) 4 src.G0.P ∧
        (∫ ω, ‖r26t3_Zpath src.G0 a ω‖ ^ 4 ∂src.G0.P) ≤ MZ := by
  obtain ⟨δD, hδD, hhalf, hD⟩ := fp81s21_gaussian_D_moments_uniform_physical p
  obtain ⟨δJ, hδJ, _, hJ⟩ := fp81s21_uniform_gaussian_J_moments p
  obtain ⟨δZ, hδZ, _, hZ⟩ := fp81s21_retained_Z_uniform_fourth p
  refine ⟨min δD (min δJ δZ), lt_min hδD (lt_min hδJ hδZ),
    (min_le_left _ _).trans hhalf, ?_⟩
  intro δ hδ hδle R hμ₀ src εG εB MUG hMUG canon S
  have hleD : δ ≤ δD := hδle.trans (min_le_left _ _)
  have hleJ : δ ≤ δJ := (hδle.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hleZ : δ ≤ δZ := (hδle.trans (min_le_right _ _)).trans (min_le_right _ _)
  obtain ⟨cD, KD, MD, hcD, hKD, hMD, hDw⟩ := hD δ hδ hleD R src S
  obtain ⟨cJ, KJ, MJ, hcJ, hKJ, hMJ, hJw⟩ := hJ δ hδ hleJ R E MUG hMUG
  obtain ⟨MZ, hMZ, hZw⟩ := hZ δ hδ hleZ R
  let OD : ∀ a : ℝ, 0 ≤ a →
      r26t6_IntervalOperators E (r26t3_coeff R) p.T a cD KD :=
    fun a ha => Classical.choice (hDw a ha).1
  let OJ : ∀ a : ℝ, 0 ≤ a →
      r26t6_IntervalOperators E (r26t3_coeff R) p.T a cJ KJ :=
    fun a ha => Classical.choice (hJw a ha).1
  refine ⟨cD, KD, cJ, KJ, MD, MJ, MZ,
    hcD, hKD, hcJ, hKJ, hMD, hMJ, hMZ, OD, OJ, ?_⟩
  dsimp only
  constructor
  · have hB := fun (a : ℝ) (ha : 0 ≤ a) =>
      (S.payload src.G0).2.2.2.2.2.2.2 0 le_rfl (a + p.T)
        (add_pos_of_nonneg_of_pos ha p.hT)
    have hG := fun (a : ℝ) (ha : 0 ≤ a) =>
      (canon.payload src.G0).time_representation 0 le_rfl (a + p.T)
        (add_pos_of_nonneg_of_pos ha p.hT)
    choose UB hUB using hB
    choose UG hUG using hG
    refine ⟨UB, UG, fun a ha => (hUB a ha).1, ?_⟩
    intro a ha
    have ht := (hUG a ha).1
    refine ⟨ht.1, ht.2.1, ht.2.2.1, ?_⟩
    filter_upwards [ht.2.2.2] with ω hω
    refine ⟨hω.1, ?_⟩
    filter_upwards [hω.2] with t ht
    exact ht.1
  · intro UB UG hUB hUG a ha
    simp only [dif_pos ha]
    have hDm := (hDw a ha).2 (OD a ha) (S.Kstar ^ 4 * S.B / 2)
      (UB a ha) (hUB a ha)
    have hweak := (canon.payload src.G0).coefficients.weak_momentRep
    have hJm := (hJw a ha).2 (OJ a ha) src.G0
      (fp81s21_gaussian_embedFamily p Es E (canon.q src.G0)) hweak.1
      (fun u hu => ⟨(hweak.2 u hu).1, (hweak.2 u hu).2.1⟩)
      (UG a ha) (hUG a ha)
    have hZm := hZw src.G0 a ha
    exact ⟨hDm.1, hDm.2, hJm.1, hJm.2, hZm.1, hZm.2.2⟩

#print axioms fp81s21_gaussian35_moments
end HRS.Fp81.S21
end
