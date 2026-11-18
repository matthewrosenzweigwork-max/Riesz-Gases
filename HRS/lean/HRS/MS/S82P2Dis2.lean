import HRS.MS.S82P2Dis1

/-!
# S8.2 (S82P2): unnormalised one-coordinate disintegration of the weak reference weight
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82P2
open HRS HRS.Whole HRS.MS.Phase2S82

/-- The unnormalised weak reference weight. -/
def s82p2_W {d p n : ℕ} (q : Euc d → ℝ) (h : ℕ → Euc d → ℝ)
    (mu : Measure (Euc d)) (beta : ℝ) (N : ℕ) (pins : Fin p → Euc d) :
    Measure (EucConfig d n) :=
  (Measure.pi fun _ : Fin n => mu).withDensity
    (fun X => ENNReal.ofReal (Real.exp (referenceExponent q h mu beta N pins X)))

lemma s82p2_exponent_cons {d p n : ℕ} (q : Euc d → ℝ) (h : ℕ → Euc d → ℝ)
    (mu : Measure (Euc d)) (beta : ℝ) (N : ℕ) (pins : Fin p → Euc d) (z : Euc d)
    (X : EucConfig d n) :
    referenceExponent q h mu beta N (Fin.cons z pins : Fin (p + 1) → Euc d) X =
      referenceExponent q h mu beta N pins X - (beta / N) * ∑ i, q (X i - z) := by
  unfold referenceExponent
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Finset.sum_add_distrib]
  rw [mul_add]
  ring

lemma s82p2_exponent_cons_measurable {d p n : ℕ} {q : Euc d → ℝ} {h : ℕ → Euc d → ℝ}
    {mu : Measure (Euc d)} [SFinite mu] (hq : Measurable q) (beta : ℝ) (N : ℕ)
    (hh : Measurable (h N)) (pins : Fin p → Euc d) :
    Measurable (fun r : Euc d × EucConfig d n =>
      referenceExponent q h mu beta N (Fin.cons r.1 pins : Fin (p + 1) → Euc d) r.2) := by
  simp only [s82p2_exponent_cons]
  refine ((s82p2_exponent_measurable hq beta N hh pins).comp measurable_snd).sub ?_
  exact measurable_const.mul (Finset.measurable_sum _ fun i _ =>
    hq.comp (((measurable_pi_apply i).comp measurable_snd).sub measurable_fst))

lemma s82p2_W_lintegral {d p m : ℕ} {q : Euc d → ℝ} {h : ℕ → Euc d → ℝ}
    {mu : Measure (Euc d)} [SigmaFinite mu] (hq : Measurable q) (hqe : ∀ z, q (-z) = q z)
    (beta : ℝ) (N : ℕ) (hh : Measurable (h N)) (pins : Fin p → Euc d) (i : Fin (m + 1))
    (F : EucConfig d (m + 1) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ X, F X ∂(s82p2_W q h mu beta N pins : Measure (EucConfig d (m + 1))) =
      ∫⁻ z, ENNReal.ofReal (Real.exp (s82p2_site q h mu beta N pins z)) *
        ∫⁻ X', F (i.insertNth z X')
          ∂(s82p2_W q h mu beta N (Fin.cons z pins : Fin (p + 1) → Euc d) :
            Measure (EucConfig d m)) ∂mu := by
  have hE := s82p2_exponent_measurable (n := m + 1) (h := h) (mu := mu) hq beta N hh pins
  have hf : Measurable (fun X : EucConfig d (m + 1) =>
      ENNReal.ofReal (Real.exp (referenceExponent q h mu beta N pins X))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hE)
  unfold s82p2_W
  rw [lintegral_withDensity_eq_lintegral_mul _ hf hF]
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => mu) i
  have hemb := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => Euc d) i).symm.measurableEmbedding
  have key := hmp.symm.lintegral_comp_emb hemb
    (fun X : EucConfig d (m + 1) => ((fun X : EucConfig d (m + 1) =>
      ENNReal.ofReal (Real.exp (referenceExponent q h mu beta N pins X))) * F) X)
  rw [← key]
  have hes := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => Euc d) i).symm.measurable
  have hprod := lintegral_prod (μ := mu) (ν := Measure.pi fun _ : Fin m => mu)
    (fun a : Euc d × (Fin m → Euc d) => ((fun X : EucConfig d (m + 1) =>
      ENNReal.ofReal (Real.exp (referenceExponent q h mu beta N pins X))) * F)
        ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => Euc d) i).symm a))
    ((hf.mul hF).comp hes).aemeasurable
  rw [hprod]
  refine lintegral_congr fun z => ?_
  have hFz : Measurable (fun X' : EucConfig d m => F (i.insertNth z X')) :=
    hF.comp (hes.comp measurable_prodMk_left)
  have hf' : Measurable (fun X' : EucConfig d m => ENNReal.ofReal (Real.exp
      (referenceExponent q h mu beta N (Fin.cons z pins : Fin (p + 1) → Euc d) X'))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (s82p2_exponent_measurable (n := m) (h := h) (mu := mu) hq beta N hh _))
  rw [lintegral_withDensity_eq_lintegral_mul _ hf' hFz,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun X' => ?_
  have e1 : (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => Euc d) i).symm (z, X') =
      i.insertNth z X' := rfl
  simp only [Pi.mul_apply, e1, s82p2_exponent_insertNth hqe]
  rw [Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le, mul_assoc]

end HRS.MS.S82P2
