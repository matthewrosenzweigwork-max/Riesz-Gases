import HRS.MS.R26T8AR09b

/-!
# S8.2 observed-time layer, packet T8A.R09: exact one-site conditional law and update invariance
For the pinned reference law, resampling a coordinate `i` from `resampleLaw` preserves the law.
Proof: split the unnormalised weight at coordinate `i` (`s82p2_W_lintegral`), swap the order of integration, and cancel
the one-site partition function, which is positive and finite since the one-site exponent is bounded above.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.MS.R26T8A
open HRS.MS.Phase2S82

set_option maxHeartbeats 2000000 in
theorem r26t8a_reference_conditional {d p n : ℕ} (hd : 2 ≤ d) {a beta C0 : ℝ}
    (hbeta : 0 < beta) {rho q : Euc d → ℝ} {h : ℕ → Euc d → ℝ}
    (hrho : HRS.Whole.IsThermalEquilibrium d (criticalS d) a beta rho)
    (hcal : CalibratedReferenceData d a beta rho q h C0) (N : ℕ) (hN : 2 ≤ N)
    (hnp : n + p ≤ N) (pins : Fin p → Euc d) (i : Fin n) :
    ∀ F : HRS.Whole.EucConfig d n → ℝ≥0∞, Measurable F →
      ∫⁻ X, F X ∂referenceLaw q h (HRS.Whole.withDensityReal rho) beta N n pins =
        ∫⁻ X, ∫⁻ y, F (Function.update X i y)
          ∂resampleLaw q h (HRS.Whole.withDensityReal rho) beta N pins i X
          ∂referenceLaw q h (HRS.Whole.withDensityReal rho) beta N n pins := by
  intro F hF
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := i.pos; omega⟩
  haveI hμ : IsProbabilityMeasure (HRS.Whole.withDensityReal rho) :=
    HRS.Whole.Q09A.measure_isProb hrho.2.1
  set μ : Measure (Euc d) := HRS.Whole.withDensityReal rho with hμdef
  have hq := hcal.short
  have hqm : Measurable q := hq.measurable
  have hqe := hq.even
  have hhm : Measurable (h N) := hcal.hmeas N
  have hconv := HRS.MS.S82P2.s82p2_conv_measurable hqm μ
  have hsym : ∀ x y : Euc d, q (x - y) = q (y - x) := fun x y => by
    rw [← hqe (y - x), neg_sub]
  -- the one-site exponent
  set ψ : (Fin m → Euc d) → Euc d → ℝ := fun X' y =>
    beta * HRS.Whole.convMeasure q μ y + h N y -
      (beta / N) * ((∑ j, q (y - X' j)) + ∑ j, q (y - pins j)) with hψ
  have hψm : Measurable (fun r : (Fin m → Euc d) × Euc d => ψ r.1 r.2) := by
    simp only [hψ]
    refine ((measurable_const.mul (hconv.comp measurable_snd)).add (hhm.comp measurable_snd)).sub
      (measurable_const.mul ((Finset.measurable_sum _ fun j _ => hqm.comp
        (measurable_snd.sub ((measurable_pi_apply j).comp measurable_fst))).add
        (Finset.measurable_sum _ fun j _ => hqm.comp (measurable_snd.sub measurable_const))))
  have hψb : ∀ X' y, ψ X' y ≤ 1 + 1 / 1000 := fun X' y =>
    r26t8a_r09_psi_le hbeta hcal hN y (add_nonneg (Finset.sum_nonneg fun j _ => hq.nonneg _)
      (Finset.sum_nonneg fun j _ => hq.nonneg _))
  have hψm' : ∀ X', Measurable (ψ X') := fun X' => hψm.comp measurable_prodMk_left
  set A : (Fin m → Euc d) → Euc d → ℝ≥0∞ := fun X' y => ENNReal.ofReal (Real.exp (ψ X' y)) with hA
  have hAm : Measurable (fun r : (Fin m → Euc d) × Euc d => A r.1 r.2) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hψm)
  have hAm' : ∀ X', Measurable (A X') := fun X' => hAm.comp measurable_prodMk_left
  have hbdd := fun X' => r26t8a_r09_tilt_bdd μ (ψ X') (hψm' X') _ (hψb X')
  set Zl : (Fin m → Euc d) → ℝ≥0∞ := fun X' => ∫⁻ y, A X' y ∂μ with hZl
  have hZ0 : ∀ X', Zl X' ≠ 0 := fun X' => by
    simp only [hZl, hA]; rw [(hbdd X').2.2]; exact (ENNReal.ofReal_pos.2 (hbdd X').2.1).ne'
  have hZt : ∀ X', Zl X' ≠ ⊤ := fun X' => by
    simp only [hZl, hA]; rw [(hbdd X').2.2]; exact ENNReal.ofReal_ne_top
  -- measurable parametric integrals
  have hes := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => Euc d) i).symm.measurable
  have hins : Measurable (fun r : (Fin m → Euc d) × Euc d => (i.insertNth r.2 r.1 : HRS.Whole.EucConfig d (m + 1))) :=
    hes.comp measurable_swap
  set K : (Fin m → Euc d) → ℝ≥0∞ := fun X' => ∫⁻ y, F (i.insertNth y X') * A X' y ∂μ with hK
  have hKm : Measurable K := by
    refine Measurable.lintegral_prod_right' (f := fun r : (Fin m → Euc d) × Euc d =>
      F (i.insertNth r.2 r.1) * A r.1 r.2) ?_
    exact (hF.comp hins).mul hAm
  have hZlm : Measurable Zl := Measurable.lintegral_prod_right' (f := fun r : (Fin m → Euc d) × Euc d => A r.1 r.2) hAm
  -- the conditional law at insertNth
  have hres : ∀ z0 X', resampleLaw q h μ beta N pins i (i.insertNth z0 X' : HRS.Whole.EucConfig d (m + 1)) =
      (Zl X')⁻¹ • μ.withDensity (A X') := by
    intro z0 X'
    have hsum : ∀ y, ∑ j ∈ Finset.univ.erase i, q (y - (i.insertNth z0 X' : HRS.Whole.EucConfig d (m + 1)) j) =
        ∑ j, q (y - X' j) := fun y => by
      rw [HRS.MS.S82P2.s82p2_sum_erase (fun j => q (y - (i.insertNth z0 X' : HRS.Whole.EucConfig d (m + 1)) j)) i]
      simp only [Fin.insertNth_apply_succAbove]
    unfold resampleLaw exponentialTilt
    simp only [hsum]
    have := (hbdd X').2.2
    simp only [hZl, hA]
    rw [this]
  set G : HRS.Whole.EucConfig d (m + 1) → ℝ≥0∞ := fun X => ∫⁻ y, F (Function.update X i y)
    ∂resampleLaw q h μ beta N pins i X with hG
  have hGins : ∀ z0 X', G (i.insertNth z0 X' : HRS.Whole.EucConfig d (m + 1)) = (Zl X')⁻¹ * K X' := by
    intro z0 X'
    simp only [hG]
    rw [hres, lintegral_smul_measure, smul_eq_mul]
    congr 1
    simp only [Fin.update_insertNth]
    have hFy : Measurable (fun y => F (i.insertNth y X' : HRS.Whole.EucConfig d (m + 1))) :=
      hF.comp (hes.comp measurable_prodMk_right)
    rw [lintegral_withDensity_eq_lintegral_mul _ (hAm' X') hFy]
    refine lintegral_congr fun y => ?_
    simp only [Pi.mul_apply]
    rw [mul_comm]
  have hGm : Measurable G := by
    have : G = fun X => (Zl (fun j => X (i.succAbove j)))⁻¹ * K (fun j => X (i.succAbove j)) := by
      funext X
      have := hGins (X i) (fun j => X (i.succAbove j))
      rw [← this]
      congr 1
      exact (Fin.insertNth_self_removeNth i X).symm
    rw [this]
    have hr : Measurable (fun X : HRS.Whole.EucConfig d (m + 1) => fun j : Fin m => X (i.succAbove j)) :=
      measurable_pi_iff.2 fun j => measurable_pi_apply _
    exact ((hZlm.inv).mul hKm).comp hr
  have hexpo : ∀ z X', ENNReal.ofReal (Real.exp (HRS.MS.S82P2.s82p2_site q h μ beta N pins z)) *
      ENNReal.ofReal (Real.exp (referenceExponent q h μ beta N pins X' -
        (beta / N) * ∑ l, q (X' l - z))) =
      ENNReal.ofReal (Real.exp (referenceExponent q h μ beta N pins X')) * A X' z := by
    intro z X'
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ← Real.exp_add, ← Real.exp_add]
    congr 2
    simp only [hψ, HRS.MS.S82P2.s82p2_site, hsym _ z]
    ring
  have hmid := fun Ψ (hΨ : Measurable Ψ) =>
    r26t8a_r09_split (m := m) (i := i) hqm hqe beta N hhm pins A hAm hexpo Ψ hΨ
  -- conclusion
  have href : referenceLaw q h μ beta N (m + 1) pins =
      (ENNReal.ofReal (∫ X, Real.exp (referenceExponent q h μ beta N pins X)
        ∂(Measure.pi fun _ : Fin (m + 1) => μ)))⁻¹ •
        (HRS.MS.S82P2.s82p2_W q h μ beta N pins : Measure (HRS.Whole.EucConfig d (m + 1))) := rfl
  rw [href, lintegral_smul_measure, lintegral_smul_measure]
  congr 1
  rw [hmid F hF, hmid G hGm]
  refine lintegral_congr fun X' => ?_
  congr 1
  have : ∀ y, G (i.insertNth y X' : HRS.Whole.EucConfig d (m + 1)) * A X' y = ((Zl X')⁻¹ * K X') * A X' y :=
    fun y => by rw [hGins]
  simp only [this]
  rw [lintegral_const_mul _ (hAm' X')]
  show K X' = (Zl X')⁻¹ * K X' * Zl X'
  rw [mul_comm ((Zl X')⁻¹), mul_assoc, ENNReal.inv_mul_cancel (hZ0 X') (hZt X'), mul_one]

end HRS.MS.R26T8A
