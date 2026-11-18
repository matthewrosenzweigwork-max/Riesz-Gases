import Mathlib

/-!
# HRS.Energy.PressureDV — the Gibbs / Donsker–Varadhan variational inequality

`N:eq:pair-entropy` (main paper, Proposition 5.5, last display) follows from the entropy variational
inequality `∫ F dν ≤ KL(ν ‖ Q) + log ∫ e^F dQ`.  We prove it for bounded `F` from the Gibbs inequality
(`integral_llr_add_sub_measure_univ_nonneg`) applied to the tilted reference `Q.tilted F`, and then for
nonnegative measurable `F` with `∫⁻ e^F dQ ≤ e^K` by monotone truncation.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace HRS

section DV

variable {α : Type*} [MeasurableSpace α]

/-- Donsker–Varadhan for bounded measurable `F`. -/
theorem dv_bounded (Q ν : Measure α) [IsProbabilityMeasure Q] [IsProbabilityMeasure ν]
    (hνQ : ν ≪ Q) (hint : Integrable (llr ν Q) ν) {F : α → ℝ} (hF : Measurable F) {M : ℝ}
    (hb : ∀ x, |F x| ≤ M) :
    ∫ x, F x ∂ν ≤ ∫ x, llr ν Q x ∂ν + Real.log (∫ x, Real.exp (F x) ∂Q) := by
  have hFb : ∀ x, ‖F x‖ ≤ M := fun x => by simpa using hb x
  have hFν : Integrable F ν := Integrable.of_bound hF.aestronglyMeasurable M (Filter.Eventually.of_forall hFb)
  have hexp : Integrable (fun x => Real.exp (F x)) Q := by
    refine Integrable.of_bound (Real.measurable_exp.comp hF).aestronglyMeasurable (Real.exp M)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (le_trans (le_abs_self _) (hb x))
  have hQ' : IsProbabilityMeasure (Q.tilted F) := isProbabilityMeasure_tilted hexp
  have hνQ' : ν ≪ Q.tilted F := hνQ.trans (absolutelyContinuous_tilted hexp)
  have hint' : Integrable (llr ν (Q.tilted F)) ν :=
    integrable_llr_tilted_right hνQ hFν hint hexp
  have h1 := InformationTheory.integral_llr_add_sub_measure_univ_nonneg hνQ' hint'
  rw [integral_llr_tilted_right hνQ hFν hexp hint] at h1
  simp only [probReal_univ] at h1
  linarith

/-- Donsker–Varadhan in lintegral form: if `F ≥ 0` is measurable, `∫⁻ e^F dQ ≤ e^K` with `0 ≤ K`, and
`KL(ν ‖ Q) < ∞`, then `∫⁻ F dν ≤ KL(ν ‖ Q) + K`. -/
theorem dv_lintegral (Q ν : Measure α) [IsProbabilityMeasure Q] [IsProbabilityMeasure ν]
    (hKL : InformationTheory.klDiv ν Q ≠ ∞) {F : α → ℝ} (hF : Measurable F) (hF0 : ∀ x, 0 ≤ F x)
    {K : ℝ} (hK : 0 ≤ K) (hZ : ∫⁻ x, ENNReal.ofReal (Real.exp (F x)) ∂Q ≤ ENNReal.ofReal (Real.exp K)) :
    ∫⁻ x, ENNReal.ofReal (F x) ∂ν ≤ InformationTheory.klDiv ν Q + ENNReal.ofReal K := by
  obtain ⟨hνQ, hint⟩ := InformationTheory.klDiv_ne_top_iff.1 hKL
  have hkl : (InformationTheory.klDiv ν Q).toReal = ∫ x, llr ν Q x ∂ν := by
    rw [InformationTheory.toReal_klDiv hνQ hint]; simp
  -- truncations
  have hFn : ∀ n : ℕ, Measurable fun x => min (F x) n := fun n => hF.min measurable_const
  have hbn : ∀ n : ℕ, ∀ x, |min (F x) n| ≤ n := fun n x => by
    rw [abs_of_nonneg (le_min (hF0 x) n.cast_nonneg)]; exact min_le_right _ _
  have key : ∀ n : ℕ, ∫⁻ x, ENNReal.ofReal (min (F x) n) ∂ν ≤
      InformationTheory.klDiv ν Q + ENNReal.ofReal K := by
    intro n
    have h1 := dv_bounded Q ν hνQ hint (hFn n) (hbn n)
    have hFb : Integrable (fun x => min (F x) n) ν :=
      Integrable.of_bound (hFn n).aestronglyMeasurable n
        (Filter.Eventually.of_forall fun x => by simpa using hbn n x)
    -- bound the log term
    have hexpn : Integrable (fun x => Real.exp (min (F x) n)) Q :=
      Integrable.of_bound (Real.measurable_exp.comp (hFn n)).aestronglyMeasurable (Real.exp n)
        (Filter.Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          exact Real.exp_le_exp.2 (le_trans (le_abs_self _) (hbn n x)))
    have hZn : ∫ x, Real.exp (min (F x) n) ∂Q ≤ Real.exp K := by
      have h2 : ENNReal.ofReal (∫ x, Real.exp (min (F x) n) ∂Q) ≤ ENNReal.ofReal (Real.exp K) := by
        rw [ofReal_integral_eq_lintegral_ofReal hexpn (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)]
        refine le_trans (lintegral_mono fun x => ENNReal.ofReal_le_ofReal
          (Real.exp_le_exp.2 (min_le_left _ _))) hZ
      exact (ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le).1 h2
    have hpos : 0 < ∫ x, Real.exp (min (F x) n) ∂Q := integral_exp_pos hexpn
    have hlog : Real.log (∫ x, Real.exp (min (F x) n) ∂Q) ≤ K := by
      calc _ ≤ Real.log (Real.exp K) := Real.log_le_log hpos hZn
        _ = K := Real.log_exp K
    have h3 : ∫ x, min (F x) n ∂ν ≤ (InformationTheory.klDiv ν Q).toReal + K := by
      rw [hkl]; linarith
    rw [← ofReal_integral_eq_lintegral_ofReal hFb
      (Filter.Eventually.of_forall fun x => le_min (hF0 x) n.cast_nonneg)]
    calc ENNReal.ofReal (∫ x, min (F x) n ∂ν) ≤ ENNReal.ofReal ((InformationTheory.klDiv ν Q).toReal + K) :=
          ENNReal.ofReal_le_ofReal h3
      _ = _ := by rw [ENNReal.ofReal_add ENNReal.toReal_nonneg hK, ENNReal.ofReal_toReal hKL]
  -- monotone limit
  have hmono : Monotone fun n : ℕ => fun x => ENNReal.ofReal (min (F x) n) := by
    intro m n hmn x
    exact ENNReal.ofReal_le_ofReal (min_le_min le_rfl (by exact_mod_cast hmn))
  have hsup : ∀ x, ⨆ n : ℕ, ENNReal.ofReal (min (F x) n) = ENNReal.ofReal (F x) := by
    intro x
    apply le_antisymm
    · exact iSup_le fun n => ENNReal.ofReal_le_ofReal (min_le_left _ _)
    · obtain ⟨n, hn⟩ := exists_nat_ge (F x)
      exact le_iSup_of_le n (by rw [min_eq_left hn])
  calc ∫⁻ x, ENNReal.ofReal (F x) ∂ν = ∫⁻ x, ⨆ n : ℕ, ENNReal.ofReal (min (F x) n) ∂ν := by
        simp_rw [hsup]
    _ = ⨆ n : ℕ, ∫⁻ x, ENNReal.ofReal (min (F x) n) ∂ν :=
        lintegral_iSup (fun n => ENNReal.measurable_ofReal.comp (hFn n)) hmono
    _ ≤ _ := iSup_le key

end DV

end HRS

end
