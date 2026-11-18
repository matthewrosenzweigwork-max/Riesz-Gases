import HRS.MS.R26T8AR09a

/-!
# S8.2 observed-time layer, packet T8A.R09b: splitting the unnormalised pinned weight at one coordinate
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.MS.R26T8A
open HRS.MS.Phase2S82

theorem r26t8a_r09_split {d p m : ℕ} {q : Euc d → ℝ} {h : ℕ → Euc d → ℝ}
    {μ : Measure (Euc d)} [SigmaFinite μ] (hqm : Measurable q) (hqe : ∀ z, q (-z) = q z)
    (beta : ℝ) (N : ℕ) (hhm : Measurable (h N)) (pins : Fin p → Euc d) (i : Fin (m + 1))
    (A : (Fin m → Euc d) → Euc d → ℝ≥0∞)
    (hAm : Measurable (fun r : (Fin m → Euc d) × Euc d => A r.1 r.2))
    (hexpo : ∀ z X', ENNReal.ofReal (Real.exp (HRS.MS.S82P2.s82p2_site q h μ beta N pins z)) *
      ENNReal.ofReal (Real.exp (referenceExponent q h μ beta N pins X' -
        (beta / N) * ∑ l, q (X' l - z))) =
      ENNReal.ofReal (Real.exp (referenceExponent q h μ beta N pins X')) * A X' z)
    (Ψ : HRS.Whole.EucConfig d (m + 1) → ℝ≥0∞) (hΨ : Measurable Ψ) :
    ∫⁻ X, Ψ X ∂(HRS.MS.S82P2.s82p2_W q h μ beta N pins : Measure (HRS.Whole.EucConfig d (m + 1))) =
      ∫⁻ X', ENNReal.ofReal (Real.exp (referenceExponent q h μ beta N pins X')) *
        ∫⁻ y, Ψ (i.insertNth y X') * A X' y ∂μ ∂(Measure.pi fun _ : Fin m => μ) := by
  have hes := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => Euc d) i).symm.measurable
  have hAm' : ∀ X', Measurable (A X') := fun X' => hAm.comp measurable_prodMk_left
  rw [HRS.MS.S82P2.s82p2_W_lintegral hqm hqe beta N hhm pins i Ψ hΨ]
  have hE0 : Measurable (fun X' : HRS.Whole.EucConfig d m => ENNReal.ofReal (Real.exp
      (referenceExponent q h μ beta N pins X'))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (HRS.MS.S82P2.s82p2_exponent_measurable hqm beta N hhm pins))
  have step : ∀ z, ENNReal.ofReal (Real.exp (HRS.MS.S82P2.s82p2_site q h μ beta N pins z)) *
      ∫⁻ X', Ψ (i.insertNth z X')
        ∂(HRS.MS.S82P2.s82p2_W q h μ beta N (Fin.cons z pins : Fin (p + 1) → Euc d) :
          Measure (HRS.Whole.EucConfig d m)) =
      ∫⁻ X', ENNReal.ofReal (Real.exp (referenceExponent q h μ beta N pins X')) *
        (Ψ (i.insertNth z X') * A X' z) ∂(Measure.pi fun _ : Fin m => μ) := by
    intro z
    have hf' : Measurable (fun X' : HRS.Whole.EucConfig d m => ENNReal.ofReal (Real.exp
        (referenceExponent q h μ beta N (Fin.cons z pins : Fin (p + 1) → Euc d) X'))) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
        (HRS.MS.S82P2.s82p2_exponent_measurable (n := m) (h := h) (mu := μ) hqm beta N hhm _))
    have hΨz : Measurable (fun X' : HRS.Whole.EucConfig d m => Ψ (i.insertNth z X')) :=
      hΨ.comp (hes.comp measurable_prodMk_left)
    unfold HRS.MS.S82P2.s82p2_W
    rw [lintegral_withDensity_eq_lintegral_mul _ hf' hΨz,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun X' => ?_
    simp only [Pi.mul_apply]
    rw [HRS.MS.S82P2.s82p2_exponent_cons]
    have hexp := hexpo z X'
    calc _ = (ENNReal.ofReal (Real.exp (HRS.MS.S82P2.s82p2_site q h μ beta N pins z)) *
          ENNReal.ofReal (Real.exp (referenceExponent q h μ beta N pins X' -
            (beta / N) * ∑ l, q (X' l - z)))) * Ψ (i.insertNth z X') := by ring
      _ = _ := by rw [hexp]; ring
  simp only [step]
  refine (lintegral_lintegral_swap ?_).trans ?_
  · have h1 : Measurable (fun r : Euc d × (Fin m → Euc d) => ENNReal.ofReal (Real.exp
        (referenceExponent q h μ beta N pins r.2))) := hE0.comp measurable_snd
    have h2 : Measurable (fun r : Euc d × (Fin m → Euc d) =>
        Ψ (i.insertNth r.1 r.2 : HRS.Whole.EucConfig d (m + 1))) := hΨ.comp hes
    have h3 : Measurable (fun r : Euc d × (Fin m → Euc d) => A r.2 r.1) := hAm.comp measurable_swap
    exact (h1.mul (h2.mul h3)).aemeasurable
  · refine lintegral_congr fun X' => ?_
    rw [← lintegral_const_mul]
    exact (hΨ.comp (hes.comp measurable_prodMk_right)).mul (hAm' X')

end HRS.MS.R26T8A
