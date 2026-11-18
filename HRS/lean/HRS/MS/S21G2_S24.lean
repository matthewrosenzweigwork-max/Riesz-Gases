import HRS.MS.R2SeAux8

/-!
# S21G2 S24 -- Stein solution of a Gaussian on `ℓ²` for the whole `C_b^5` unit ball (R26-T3.S24)

Instance of the generic `HRS.stein_bounds`, `HRS.stein_equation`, `HRS.stein_third_derivative` for the identity
random variable on `(SeqL2, G)`; the `C_b^5` unit-ball bound turns into the normalised derivative bounds `1/k`
and the `S99.SteinCl` record.  The contract is taken verbatim.  Helper names carry the prefix `s21g2_s24_`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R26T3

private lemma s21g2_s24_sup_le (Φ : HRS.Whole.SeqL2 → ℝ) (hΦ : Φ ∈ HRS.CbUnitBall HRS.Whole.SeqL2 5)
    {k : ℕ} (hk : k ≤ 5) : (⨆ y, ‖iteratedFDeriv ℝ k Φ y‖) ≤ 1 := by
  refine le_trans ?_ hΦ.2.2
  unfold HRS.cbNorm
  refine le_trans ?_ (Finset.single_le_sum (f := fun j => ⨆ z : HRS.Whole.SeqL2, ‖iteratedFDeriv ℝ j Φ z‖)
    (fun j _ => Real.iSup_nonneg fun _ => norm_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le hk)))
  exact le_rfl

theorem r26t3_stein_solution (G : Measure HRS.Whole.SeqL2) (hG : HRS.IsCenteredGaussian G)
    (Φ : HRS.Whole.SeqL2 → ℝ) (hΦ : Φ ∈ HRS.CbUnitBall HRS.Whole.SeqL2 5) :
    S99.SteinCl (HRS.steinSolution G id Φ) ∧
      (∀ k : ℕ, 1≤k → k≤5 → ∀ x, ‖iteratedFDeriv ℝ k (HRS.steinSolution G id Φ) x‖≤1/(k : ℝ)) ∧
      (∀ x, HRS.covarianceContraction G id (HRS.steinSolution G id Φ) x-
        fderiv ℝ (HRS.steinSolution G id Φ) x x=Φ x-∫ z, Φ z ∂G) ∧
      (∀ v : Fin 3 → HRS.Whole.SeqL2,
        (∫ x, iteratedFDeriv ℝ 3 (HRS.steinSolution G id Φ) x v ∂G)=
          -(1/3)*(∫ x, iteratedFDeriv ℝ 3 Φ x v ∂G)) := by
  haveI : IsProbabilityMeasure G := hG.1.toIsProbabilityMeasure
  have hmΦ : HRS.MemCb 5 Φ := ⟨hΦ.1, hΦ.2.1⟩
  have hgl : HRS.IsCenteredGaussian (HRS.law G (id : HRS.Whole.SeqL2 → HRS.Whole.SeqL2)) := by
    simpa [HRS.law] using hG
  obtain ⟨_, hcd, hb⟩ := HRS.stein_bounds G id aemeasurable_id hgl Φ hmΦ
  have hb' : ∀ k : ℕ, 1 ≤ k → k ≤ 5 → ∀ x,
      ‖iteratedFDeriv ℝ k (HRS.steinSolution G id Φ) x‖ ≤ 1 / (k : ℝ) := fun k hk1 hk5 x => by
    refine (hb k hk1 hk5 x).trans ?_
    rw [one_div]
    exact mul_le_of_le_one_right (by positivity) (s21g2_s24_sup_le Φ hΦ hk5)
  refine ⟨⟨hcd, fun i hi1 hi5 z => ?_⟩, hb', fun x => HRS.stein_equation G id aemeasurable_id hgl Φ hmΦ x,
    fun v => HRS.stein_third_derivative G id aemeasurable_id hgl Φ hmΦ v⟩
  refine (hb' i hi1 hi5 z).trans ?_
  rw [div_le_one (by exact_mod_cast hi1)]
  exact_mod_cast hi1

end HRS.MS.R26T3
