/-
# HRS.Equilibrium.PairMomentsTower -- the signed tower property of the pinned ensemble (EQ-01b)
-/
import HRS.Equilibrium.PairMomentsBase

open MeasureTheory ProbabilityTheory Filter Topology Function
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS.PairMom

open HRS HRS.External HRS.Quad

section Tower

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} [IsProbabilityMeasure μ] {B : Type*} [Fintype B]

/-- The `x`-fibre of the disintegration, as an integral against `μ^n`. -/
theorem lintegral_insertAt_eq (V : WeakPotential μ) {lam : ℝ} (hlam : 0 ≤ lam) (a : B → E) {n : ℕ}
    (i : Fin (n + 1)) {Φ : (Fin (n + 1) → E) → ℝ≥0∞} (hΦ : Measurable Φ) (x : E) :
    ∫⁻ y, fieldDensity V (pinField V lam a) lam (n + 1) (insertAt i x y) * Φ (insertAt i x y)
        ∂(Measure.pi fun _ : Fin n => μ) =
      pinWeight V lam a n x * ∫⁻ y, Φ (insertAt i x y) ∂(pinnedLaw V lam n (pinsWith a x)) := by
  have hψ := isField_pinField V hlam a
  have hψx : ∀ x, IsField μ (pinField V lam (pinsWith a x)) V.M
      (V.M' + lam * Fintype.card (Option B) * V.γ) := fun x => isField_pinField V hlam _
  have hΦx : Measurable fun y : Fin n → E => Φ (insertAt i x y) :=
    hΦ.comp ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E) i).symm.measurable.comp
      (measurable_const.prodMk measurable_id))
  have hdx := measurable_fieldDensity (hψx x).measurable V lam n
  have hP : (pinnedLaw V lam n (pinsWith a x)) = (Measure.pi fun _ : Fin n => μ).withDensity
      (fieldDensity V (pinField V lam (pinsWith a x)) lam n) := rfl
  rw [hP, lintegral_withDensity_eq_lintegral_mul _ hdx hΦx, ← lintegral_const_mul _ (hdx.mul hΦx)]
  refine lintegral_congr fun y => ?_
  simp only [Pi.mul_apply, fieldDensity]
  rw [fieldWeight_insertAt]
  unfold pinWeight
  have hn0 : fieldNorm V (pinField V lam (pinsWith a x)) lam n ≠ 0 :=
    (fieldNorm_pos (hψx x).measurable V lam n).ne'
  have hnt : fieldNorm V (pinField V lam (pinsWith a x)) lam n ≠ ⊤ :=
    (fieldNorm_lt_top (hψx x) hlam n).ne
  calc ENNReal.ofReal (Real.exp (pinField V lam a x)) *
        fieldWeight V (pinField V lam (pinsWith a x)) lam y *
        (fieldNorm V (pinField V lam a) lam (n + 1))⁻¹ * Φ (insertAt i x y)
      = (fieldNorm V (pinField V lam (pinsWith a x)) lam n *
          (fieldNorm V (pinField V lam (pinsWith a x)) lam n)⁻¹) *
        (ENNReal.ofReal (Real.exp (pinField V lam a x)) *
        fieldWeight V (pinField V lam (pinsWith a x)) lam y *
        (fieldNorm V (pinField V lam a) lam (n + 1))⁻¹ * Φ (insertAt i x y)) := by
        rw [ENNReal.mul_inv_cancel hn0 hnt, one_mul]
    _ = _ := by ring

theorem measurable_lintegral_insertAt (V : WeakPotential μ) {lam : ℝ} (hlam : 0 ≤ lam) (a : B → E)
    {n : ℕ} (i : Fin (n + 1)) {Φ : (Fin (n + 1) → E) → ℝ≥0∞} (hΦ : Measurable Φ) :
    Measurable fun x => ∫⁻ y, fieldDensity V (pinField V lam a) lam (n + 1) (insertAt i x y) *
      Φ (insertAt i x y) ∂(Measure.pi fun _ : Fin n => μ) := by
  have hψ := isField_pinField V hlam a
  have hdm := measurable_fieldDensity hψ.measurable V lam (n + 1)
  have hsymm : Measurable fun p : E × (Fin n → E) => insertAt i p.1 p.2 :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E) i).symm.measurable
  exact Measurable.lintegral_prod_right' (f := fun p : E × (Fin n → E) =>
    fieldDensity V (pinField V lam a) lam (n + 1) (insertAt i p.1 p.2) * Φ (insertAt i p.1 p.2))
    ((hdm.comp hsymm).mul (hΦ.comp hsymm))

/-- **Signed disintegration** of the pinned ensemble:
`E_R Φ = ∫ pinWeight(x) · E_{R^x}[Φ(insertAt i x ·)] μ(dx)` for integrable `Φ`. -/
theorem integral_pinned_succ (V : WeakPotential μ) {lam : ℝ} (hlam : 0 ≤ lam) (a : B → E) {n : ℕ} [NeZero n]
    (i : Fin (n + 1)) {Φ : (Fin (n + 1) → E) → ℝ} (hΦ : Measurable Φ)
    (hint : Integrable Φ (pinnedLaw V lam (n + 1) a)) :
    ∫ Y, Φ Y ∂(pinnedLaw V lam (n + 1) a) =
      ∫ x, (pinWeight V lam a n x).toReal *
        ∫ y, Φ (insertAt i x y) ∂(pinnedLaw V lam n (pinsWith a x)) ∂μ := by
  set P := pinnedLaw V lam (n + 1) a with hPdef
  set ν : E → Measure (Fin n → E) := fun x => pinnedLaw V lam n (pinsWith a x) with hν
  have hΦp : Measurable fun Y : Fin (n + 1) → E => ENNReal.ofReal (Φ Y) :=
    ENNReal.measurable_ofReal.comp hΦ
  have hΦm : Measurable fun Y : Fin (n + 1) → E => ENNReal.ofReal (-Φ Y) :=
    ENNReal.measurable_ofReal.comp hΦ.neg
  have hone : Measurable fun _ : Fin (n + 1) → E => (1 : ℝ≥0∞) := measurable_const
  set gp : E → ℝ≥0∞ := fun x => ∫⁻ y, fieldDensity V (pinField V lam a) lam (n + 1) (insertAt i x y) *
    ENNReal.ofReal (Φ (insertAt i x y)) ∂(Measure.pi fun _ : Fin n => μ) with hgp
  set gm : E → ℝ≥0∞ := fun x => ∫⁻ y, fieldDensity V (pinField V lam a) lam (n + 1) (insertAt i x y) *
    ENNReal.ofReal (-Φ (insertAt i x y)) ∂(Measure.pi fun _ : Fin n => μ) with hgm
  set w1 : E → ℝ≥0∞ := fun x => ∫⁻ y, fieldDensity V (pinField V lam a) lam (n + 1) (insertAt i x y) * 1
    ∂(Measure.pi fun _ : Fin n => μ) with hw1
  have hgpm : Measurable gp := measurable_lintegral_insertAt V hlam a i hΦp
  have hgmm : Measurable gm := measurable_lintegral_insertAt V hlam a i hΦm
  have hw1m : Measurable w1 := measurable_lintegral_insertAt V hlam a i hone
  have hgpe : ∀ x, gp x = pinWeight V lam a n x * ∫⁻ y, ENNReal.ofReal (Φ (insertAt i x y)) ∂(ν x) :=
    fun x => lintegral_insertAt_eq V hlam a i hΦp x
  have hgme : ∀ x, gm x = pinWeight V lam a n x * ∫⁻ y, ENNReal.ofReal (-Φ (insertAt i x y)) ∂(ν x) :=
    fun x => lintegral_insertAt_eq V hlam a i hΦm x
  have hw1e : ∀ x, w1 x = pinWeight V lam a n x := by
    intro x
    have := lintegral_insertAt_eq V hlam a i hone x
    have hP1 : IsProbabilityMeasure (ν x) := isProb_pinnedLaw V hlam n _
    simpa [hw1, lintegral_const, measure_univ] using this
  have hPp : ∫⁻ Y, ENNReal.ofReal (Φ Y) ∂P = ∫⁻ x, gp x ∂μ := by
    rw [hPdef, lintegral_pinned_succ V hlam a i hΦp]
    exact lintegral_congr fun x => (hgpe x).symm
  have hPm : ∫⁻ Y, ENNReal.ofReal (-Φ Y) ∂P = ∫⁻ x, gm x ∂μ := by
    rw [hPdef, lintegral_pinned_succ V hlam a i hΦm]
    exact lintegral_congr fun x => (hgme x).symm
  have hfp : ∫⁻ x, gp x ∂μ < ⊤ := by rw [← hPp]; exact hint.lintegral_lt_top
  have hfm : ∫⁻ x, gm x ∂μ < ⊤ := by
    rw [← hPm]; exact hint.neg.lintegral_lt_top
  have hwint : ∫⁻ x, pinWeight V lam a n x ∂μ = 1 := lintegral_pinWeight V hlam a i (0 : Fin n)
  have hwae : ∀ᵐ x ∂μ, pinWeight V lam a n x < ⊤ := by
    have hwm : Measurable (pinWeight V lam a n) := by
      have : pinWeight V lam a n = w1 := funext fun x => (hw1e x).symm
      rw [this]; exact hw1m
    exact ae_lt_top hwm (by rw [hwint]; exact ENNReal.one_ne_top)
  have hgpae : ∀ᵐ x ∂μ, gp x < ⊤ := ae_lt_top hgpm hfp.ne
  have hgmae : ∀ᵐ x ∂μ, gm x < ⊤ := ae_lt_top hgmm hfm.ne
  have hr : ∀ᵐ x ∂μ, (pinWeight V lam a n x).toReal * ∫ y, Φ (insertAt i x y) ∂(ν x) =
      (gp x).toReal - (gm x).toReal := by
    filter_upwards [hwae, hgpae, hgmae] with x hwx hgpx hgmx
    by_cases hw0 : pinWeight V lam a n x = 0
    · have h1 : gp x = 0 := by rw [hgpe x, hw0, zero_mul]
      have h2 : gm x = 0 := by rw [hgme x, hw0, zero_mul]
      rw [hw0, h1, h2]; simp
    · have hgpx' := hgpx
      have hgmx' := hgmx
      rw [hgpe x] at hgpx'
      rw [hgme x] at hgmx'
      have hApt : (∫⁻ y, ENNReal.ofReal (Φ (insertAt i x y)) ∂(ν x)) < ⊤ := by
        by_contra h
        have : (∫⁻ y, ENNReal.ofReal (Φ (insertAt i x y)) ∂(ν x)) = ⊤ := not_lt_top_iff.1 h
        rw [this, ENNReal.mul_top hw0] at hgpx'
        exact lt_irrefl _ hgpx'
      have hAmt : (∫⁻ y, ENNReal.ofReal (-Φ (insertAt i x y)) ∂(ν x)) < ⊤ := by
        by_contra h
        have : (∫⁻ y, ENNReal.ofReal (-Φ (insertAt i x y)) ∂(ν x)) = ⊤ := not_lt_top_iff.1 h
        rw [this, ENNReal.mul_top hw0] at hgmx'
        exact lt_irrefl _ hgmx'
      have hΦx : Measurable fun y : Fin n → E => Φ (insertAt i x y) :=
        hΦ.comp ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E) i).symm.measurable.comp
          (measurable_const.prodMk measurable_id))
      have hmpx : Measurable fun y : Fin n → E => ENNReal.ofReal (Φ (insertAt i x y)) :=
        ENNReal.measurable_ofReal.comp hΦx
      have hintx : Integrable (fun y : Fin n → E => Φ (insertAt i x y)) (ν x) := by
        refine ⟨hΦx.aestronglyMeasurable, ?_⟩
        unfold HasFiniteIntegral
        have : ∀ y, ‖Φ (insertAt i x y)‖ₑ = ENNReal.ofReal (Φ (insertAt i x y)) +
            ENNReal.ofReal (-Φ (insertAt i x y)) := by
          intro y
          rcases le_total 0 (Φ (insertAt i x y)) with h | h
          · rw [Real.enorm_eq_ofReal h, ENNReal.ofReal_of_nonpos (by linarith : -Φ (insertAt i x y) ≤ 0), add_zero]
          · rw [Real.enorm_eq_ofReal_abs, abs_of_nonpos h, ENNReal.ofReal_of_nonpos h, zero_add]
        simp_rw [this]
        rw [lintegral_add_left hmpx]
        exact ENNReal.add_lt_top.2 ⟨hApt, hAmt⟩
      rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hintx, hgpe x, hgme x,
        ENNReal.toReal_mul, ENNReal.toReal_mul]
      ring
  have hgpint : Integrable (fun x => (gp x).toReal) μ := integrable_toReal_of_lintegral_ne_top hgpm.aemeasurable hfp.ne
  have hgmint : Integrable (fun x => (gm x).toReal) μ := integrable_toReal_of_lintegral_ne_top hgmm.aemeasurable hfm.ne
  rw [integral_congr_ae hr, integral_sub hgpint hgmint, integral_toReal hgpm.aemeasurable hgpae,
    integral_toReal hgmm.aemeasurable hgmae, ← hPp, ← hPm,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint]

theorem measurable_pinWeight' (V : WeakPotential μ) {lam : ℝ} (hlam : 0 ≤ lam) (a : B → E) {n : ℕ}
    (i : Fin (n + 1)) : Measurable (pinWeight V lam a n) := by
  have hone : Measurable fun _ : Fin (n + 1) → E => (1 : ℝ≥0∞) := measurable_const
  have hm := measurable_lintegral_insertAt V hlam a i hone
  have : pinWeight V lam a n = fun x => ∫⁻ y, fieldDensity V (pinField V lam a) lam (n + 1)
      (insertAt i x y) * 1 ∂(Measure.pi fun _ : Fin n => μ) := by
    funext x
    have := lintegral_insertAt_eq V hlam a i hone x
    have hP1 : IsProbabilityMeasure (pinnedLaw V lam n (pinsWith a x)) := isProb_pinnedLaw V hlam n _
    rw [this]
    simp [lintegral_const, measure_univ]
  rw [this]; exact hm

theorem pinWeight_ae_lt_top (V : WeakPotential μ) {lam : ℝ} (hlam : 0 ≤ lam) (a : B → E) {n : ℕ}
    [NeZero n] (i : Fin (n + 1)) : ∀ᵐ x ∂μ, pinWeight V lam a n x < ⊤ :=
  ae_lt_top (measurable_pinWeight' V hlam a i)
    (by rw [lintegral_pinWeight V hlam a i (0 : Fin n)]; exact ENNReal.one_ne_top)

end Tower

end HRS.PairMom

end
